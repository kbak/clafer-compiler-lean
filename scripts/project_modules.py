#!/usr/bin/env python3
"""Discover all Lean sources; enforce ownership, runtime imports and pinned inputs.

Header parsing adapted from clafer-semantics scripts/project_modules.py at
1454e3bd2ce9697923cdcef3863c816651ffc147 (MIT, copyright 2026 Kacper Bak).
See LICENSE. Module discovery is independent of root-module reachability.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
AUDIT_MARKER = "-- PROJECT_IMPORTS"
OWNERS = {"Frontend", "IR", "SemanticsBridge", "Backend", "Correctness", "Driver"}
PROOF = {"SemanticsBridge", "Correctness"}
UPSTREAM = {"Clafer", "FormalCD", "DPGraph", "Mathlib"}
# Pinned toolchain JSON representation/escaping and parser primitives used by #19.
# Keep this exact: importing the elaborator or arbitrary Lean modules is not admitted.
RUNTIME_JSON = {'Lean.Data.Json.Parser', 'Lean.Data.Json.FromToJson.Basic'}
PIN = "d677260305076f98d5699542a81a1dceab8c2da6"
TOOLCHAIN = "leanprover/lean4:v4.35.0"

def uncomment(source):
    """Preserve newlines; do not treat comment delimiters inside strings as code."""
    output, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            output.append(char)
            i += 1
            if char == "\\" and i < len(source):
                output.append(source[i])
                i += 1
            elif char == '"':
                string = False
        elif pair == "/-":
            output.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = end if end >= 0 else len(source)
        else:
            output.append(char)
            string = char == '"'
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(output)


def imports(source):
    # Require one complete import per line (including public/meta/import all).
    # Lean rejects imports after declarations; we reject them here as well.
    found, body = [], False
    for line in uncomment(source).splitlines():
        words = line.split()
        if not words:
            continue
        if words == ["module"] and not body and not found:
            continue
        if "import" in words[:3]:
            match = re.fullmatch(
                r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*", line
            )
            if body or not match or not MODULE.fullmatch(match[1]):
                raise ValueError(f"unsupported import header: {line.strip()}")
            found.append(match[1])
        else:
            body = True
    return found


def inventory(repo):
    modules = {}
    for directory, dirs, files in os.walk(repo, followlinks=False):
        relative = Path(directory).relative_to(repo)
        if relative == Path('.'):
            dirs[:] = [d for d in dirs if d not in {'.git', '.lake', '.venv', '__pycache__'}]
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f'source directory symlink: {relative / name}')
        for name in files:
            if not name.endswith('.lean'):
                continue
            path = relative / name
            if (repo / path).is_symlink():
                raise ValueError(f'source symlink: {path}')
            if path == Path('scripts/axiom_audit.lean'):
                continue  # Explicit metaprogram/tool boundary, executed separately.
            module = '.'.join(path.with_suffix('').parts)
            parts = module.split('.')
            owned = (module in {'ClaferCompiler', 'Main', 'tests'} or
                     (len(parts) >= 2 and parts[0] == 'ClaferCompiler' and parts[1] in OWNERS) or
                     (len(parts) >= 2 and parts[0] == 'tests'))
            if parts[:2] == ['ClaferCompiler', 'Backend']:
                owned = len(parts) >= 3 and parts[2] == 'Alloy'
            if not MODULE.fullmatch(module) or not owned:
                raise ValueError(f'unowned Lean module: {path}')
            modules[module] = path
    for required in ['ClaferCompiler', 'Main', 'tests', 'tests.Smoke', 'tests.Upstream',
                     *(f'ClaferCompiler.{p}' for p in OWNERS - {'Backend'}),
                     'ClaferCompiler.Backend.Alloy']:
        if required not in modules:
            raise ValueError(f'missing required module: {required}')
    return dict(sorted(modules.items()))


def dependency_imports(repo):
    """Include pinned imports of every owned module, even unreachable helpers."""
    return sorted({dependency for path in inventory(repo).values()
                   for dependency in imports((repo / path).read_text())
                   if dependency.split('.')[0] in UPSTREAM})


def validate(repo):
    modules = inventory(repo)
    config = tomllib.loads((repo / 'lakefile.toml').read_text())
    expected = {
        'name': 'claferCompiler', 'version': '0.1.0',
        'defaultTargets': ['ClaferCompiler', 'CompilerTests', 'clafer-compiler'],
        'leanOptions': {'warningAsError': True},
        'require': [{'name': 'clafer', 'git': 'https://github.com/kbak/clafer-semantics.git', 'rev': PIN}],
        'lean_lib': [{'name': 'ClaferCompiler', 'globs': ['ClaferCompiler', 'ClaferCompiler.**']},
                     {'name': 'CompilerTests', 'globs': ['tests.**']}],
        'lean_exe': [{'name': 'clafer-compiler', 'root': 'Main'}],
    }
    if config != expected:
        raise ValueError('Lake configuration differs from the reviewed build/ownership contract')
    if (repo / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('toolchain differs from the pinned upstream toolchain')
    edges = {}
    for module, path in modules.items():
        source = (repo / path).read_text()
        code = re.sub(r'"(?:\\.|[^"\\])*"', '""', uncomment(source))
        if re.search(r'\b(?:sorry|admit|axiom|unsafe|partial)\b', code):
            raise ValueError(f'{path}: prohibited proof escape or unsafe/partial declaration')
        edges[module] = imports(source)
        parts = module.split('.')
        runtime = module == 'Main' or (parts[0] == 'ClaferCompiler' and
                                      len(parts) > 1 and parts[1] not in PROOF)
        for dependency in edges[module]:
            dep = dependency.split('.')
            if dep[0] in {'ClaferCompiler', 'Main', 'tests'}:
                if dependency not in modules:
                    raise ValueError(f'{module}: missing local import {dependency}')
                if parts[0] != 'tests' and dep[0] == 'tests':
                    raise ValueError(f'{module}: production import of test {dependency}')
                if runtime and (dependency == 'ClaferCompiler' or
                                (len(dep) > 1 and dep[1] in PROOF)):
                    raise ValueError(f'{module}: runtime imports proof-only module {dependency}')
                if parts[0] == 'ClaferCompiler' and dep[0] == 'Main':
                    raise ValueError('library cannot import the IO entrypoint')
            elif dep[0] not in UPSTREAM | {'Init', 'Std'} and dependency not in RUNTIME_JSON:
                raise ValueError(f'{module}: unapproved dependency {dependency}')
            elif runtime and dep[0] in UPSTREAM:
                raise ValueError(f'{module}: runtime imports upstream semantics {dependency}')
    if any(d.split('.')[0] in {'ClaferCompiler', 'Main', 'tests'}
           for d in edges['tests.Upstream']):
        raise ValueError('independent upstream smoke test imports project code')
    active, done = set(), set()

    def visit(module):
        if module in active:
            raise ValueError(f'import cycle at {module}')
        if module in done:
            return
        active.add(module)
        for dep in edges[module]:
            if dep in modules:
                visit(dep)
        active.remove(module)
        done.add(module)

    for module in modules:
        visit(module)
    return modules


def check_dependencies(repo):
    manifest = json.loads((repo / 'lake-manifest.json').read_text())
    if manifest.get('packagesDir') != '.lake/packages':
        raise ValueError('manifest must use .lake/packages')
    packages = manifest['packages']
    if len({p['name'] for p in packages}) != len(packages):
        raise ValueError('duplicate package identity')
    for package in packages:
        if (package['type'] != 'git' or not re.fullmatch('[0-9a-f]{40}', package['rev']) or
                not re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', package['name'])):
            raise ValueError('every dependency must have a named immutable Git identity')
        directory = repo / '.lake/packages' / package['name']
        sha = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain'], text=True)
        if sha != package['rev'] or dirty:
            raise ValueError(f'dependency differs from pin: {package["name"]}')
    clafer = next(p for p in packages if p['name'] == 'clafer')
    if clafer['rev'] != PIN or clafer['url'] != 'https://github.com/kbak/clafer-semantics.git':
        raise ValueError('clafer dependency differs from the source register')
    upstream = repo / '.lake/packages/clafer'
    if (upstream / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('upstream toolchain mismatch')
    upstream_packages = json.loads((upstream / 'lake-manifest.json').read_text())['packages']
    identity = lambda p: (p['name'], p['url'], p['rev'])
    if {identity(p) for p in packages if p['name'] != 'clafer'} != {identity(p) for p in upstream_packages}:
        raise ValueError('transitive dependency identities differ from pinned upstream manifest')
    print('All dependency commits, clean sources, and inherited Mathlib pin verified.')


def audit_source(repo, modules):
    template = (repo / 'scripts/axiom_audit.lean').read_text()
    if template.count(AUDIT_MARKER) != 1:
        raise ValueError('audit must contain exactly one import marker')
    return template.replace(AUDIT_MARKER, '\n'.join(f'import all {m}' for m in modules))


# [impl->req~compiler-build~1]
# [impl->req~compiler-boundaries~1]
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output-dir', type=Path, default=Path('.lake/validation'))
    parser.add_argument('--dependencies', action='store_true')
    args = parser.parse_args()
    modules = validate(args.repo)
    if args.dependencies:
        check_dependencies(args.repo)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'modules.txt').write_text(''.join(f'{m}\n' for m in modules))
    (args.output_dir / 'axiom_audit.lean').write_text(audit_source(args.repo, modules))
    print(f'Owned modules ({len(modules)}): {", ".join(modules)}')


if __name__ == '__main__':
    main()
