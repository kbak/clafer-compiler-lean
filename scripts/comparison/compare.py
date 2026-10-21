#!/usr/bin/env python3
"""Exact three-way M1 comparison. All execution artifacts stay outside source."""
import argparse
import copy
from concurrent.futures import ThreadPoolExecutor
import importlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle

MUTATIONS = ('none', 'collapse-occurrence', 'drop-cardinality', 'drop-group',
             'drop-disjointness', 'swap-endpoints', 'reject-all')


def source_identity():
    paths = [*sorted((ROOT / 'ClaferCompiler').rglob('*.lean')),
             *sorted((ROOT / 'scripts/comparison').glob('*.py')),
             *sorted((ROOT / 'scripts/comparison').glob('*.java')),
             ROOT / 'tests/ComparisonNative.lean', ROOT / 'tests/test_comparison.py',
             ROOT / 'scripts/oracles/oracle.py', ROOT / 'tests/fixtures/comparison/tiny.cfr',
             ROOT / 'lean-toolchain',
             ROOT / 'lake-manifest.json', ROOT / 'lakefile.toml']
    return {str(p.relative_to(ROOT)): oracle.digest(p) for p in paths}


def run(command, directory, name, *, cwd=ROOT, env=None, timeout=60):
    oracle.write(directory / (name + '-command.json'), list(map(str, command)))
    with (directory / (name + '-stdout.log')).open('wb') as out, \
            (directory / (name + '-stderr.log')).open('wb') as err:
        subprocess.run(list(map(str, command)), cwd=cwd, env=env, stdout=out, stderr=err,
                       check=True, timeout=timeout)


# [impl->req~compiler-differential~1]
class Runtime:
    def __init__(self, tools, directory):
        self.api = oracle.adapters()
        self.tools = Path(tools).resolve()
        self.exporter, self.build, self.alloy = oracle.load_tools(tools, self.api)
        self.relation = importlib.import_module('relation')
        self.candidates = importlib.import_module('candidates')
        self.directory = oracle.external(directory)
        self.directory.mkdir(parents=True, exist_ok=False)
        self.source = source_identity()
        oracle.write(self.directory / 'source.json', self.source)
        for path in self.source:
            destination = self.directory / 'source' / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, destination)
        self.env = self.api['alloy_runtime'].java_env()
        modules = ['ClaferCompiler.IR.Structural'] + ['ClaferCompiler.Backend.Alloy.' + n for n in
            ('Syntax', 'Bounds', 'Semantics', 'Structural', 'StructuralRepresentation',
             'Decode', 'Names', 'Parse', 'Print')] + ['tests.ComparisonNative']
        run(['lake', 'build', *['+' + m + ':c.o' for m in modules]], self.directory, 'build')
        harness = self.directory / 'Harness.lean'
        harness.write_text('import tests.ComparisonNative\n'
                           'def main (args : List String) : IO Unit := ClaferCompiler.Tests.Comparison.run args\n')
        cfile = self.directory / 'Harness.c'
        self.native = self.directory / 'comparison-native'
        run(['lake', 'env', 'lean', f'--root={self.directory}', '-c', cfile, harness], self.directory, 'compile')
        run(['lake', 'env', 'leanc', cfile,
             *[ROOT / '.lake/build/ir' / (m.replace('.', '/') + '.c.o.export') for m in modules],
             '-o', self.native], self.directory, 'link')
        self.classpath = os.pathsep.join(map(str, [self.directory, self.alloy['classes'], self.alloy['jar']]))
        bridge = ROOT / 'scripts/comparison/ComparisonBridge.java'
        run([self.alloy['java'].with_name('javac'), '--release', '17', '-cp', self.classpath,
             '-d', self.directory, bridge], self.directory, 'javac', env=self.env)
        self.identity = dict(native=oracle.digest(self.native), bridge=oracle.digest(self.directory / 'ComparisonBridge.class'),
                             analyzer=self.alloy['identity'])
        oracle.write(self.directory / 'runtime.json', self.identity)
        self.snapshot = self.api['comparison'].source_snapshot()

    def check(self, core, candidate):
        return self.api['checker_runtime'].execute(core, candidate, self.snapshot)[0]


def transport(core, bounds, bitwidth):
    """Map already receipt-validated UIDs to stable numeric IDs, never names."""
    ids = {'root': 0, **{d['uid']: i + 1 for i, d in enumerate(core['declarations'])}}
    rows = [[sum(bounds.values()), bitwidth], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, bounds['root']]]
    for d in core['declarations']:
        rows.append([ids[d['uid']], ids[d['parent']] + 1 if d['parent'] in ids else 0,
                     ids[d['super']] + 1 if d['super'] else 0,
                     {'basic': 0, 'set': 1, 'bag': 2}[d['mode']], ids[d['target']] if d['target'] else 0,
                     int(d['abstract']), d['card'][0], d['card'][1] + 1,
                     d['group'][0], d['group'][1] + 1, d['parentRank'], d['superRank'],
                     int(d['unused']), bounds[d['uid']]])
    return ''.join(' '.join(map(str, r)) + '\n' for r in rows), ids


def numeric_rows(path):
    return [[int(x) for x in line.split()] for line in path.read_text().splitlines()]


def layout(output, ids):
    names = {i: uid for uid, i in ids.items()}
    maps = {names[d]: dict(signature=f'cc{4*s}', containment=None if c == 0 else f'cc{4*(c-1)+1}',
                           references=None if r == 0 else f'cc{4*(r-1)+1}')
            for d, s, c, r in numeric_rows(output / 'mapping.rows')}
    sigs, fields = {}, {}
    for row in numeric_rows(output / 'schema.rows'):
        if row[0] == 0:
            _, i, parent, abstract = row
            sigs[f'cc{4*i}'] = dict(id=i, parent=None if parent == 0 else f'cc{4*(parent-1)}', abstract=bool(abstract))
        else:
            _, i, owner, target = row
            fields[f'cc{4*i+1}'] = dict(id=i, owner=f'cc{4*owner}', target=f'cc{4*target}')
    return dict(maps=maps, signatures=sigs, fields=fields)


def pin(candidate, spec):
    names = {o: f'ib_obj_{i}' for i, o in enumerate(candidate['objects'])}
    union = lambda xs, empty='none': ' + '.join(xs) or empty
    clauses = [f"cc0 = ({union(list(names.values()))})",
               f"{spec['maps']['root']['signature']} = {names[candidate['root']]}"]
    for uid, mapping in spec['maps'].items():
        clauses.append(f"{mapping['signature']} = ({union([names[o] for u,o in candidate['members'] if u == uid])})")
        for table in ('containment', 'references'):
            if mapping[table]:
                tuples = [f'{names[a]}->{names[b]}' for u, (a,b) in candidate[table] if u == uid]
                clauses.append(f"@{mapping[table]} = ({union(tuples, 'none->none')})")
    return 'fact { some disj ' + ', '.join(names.values()) + ': cc0 | {\n' + '\n'.join(clauses) + '\n} }\n'


# [impl->req~compiler-instance-decode~1]
def witness_tables(witness, spec):
    """Strict typed JSON boundary; atom strings are opaque identities, never split."""
    if type(witness) is not dict or set(witness) != {'signatures', 'fields'}:
        raise ValueError('witness envelope')
    for kind in ('signatures', 'fields'):
        if type(witness[kind]) is not dict or set(witness[kind]) != set(spec[kind]):
            raise ValueError('witness inventory')
    sigs = witness['signatures']
    for extent in sigs.values():
        if type(extent) is not list or any(type(a) is not str or not a for a in extent) or len(set(extent)) != len(extent):
            raise ValueError('witness atoms')
    labels = {atom: i for i, atom in enumerate(sigs['cc0'])}
    if any(a not in labels for extent in sigs.values() for a in extent):
        raise ValueError('atom outside object carrier')
    rows = [[len(sigs), len(spec['fields'])]]
    for name in sorted(sigs, key=lambda x: spec['signatures'][x]['id']):
        rows.append([0, *[labels[a] for a in sigs[name]]])
    for name, field in spec['fields'].items():
        tuples = witness['fields'][name]
        if type(tuples) is not list:
            raise ValueError('witness relation')
        seen = set()
        for pair in tuples:
            if type(pair) is not list or len(pair) != 2 or any(type(a) is not str or a not in labels for a in pair):
                raise ValueError('witness tuple')
            if tuple(pair) in seen:
                raise ValueError('duplicate witness tuple')
            seen.add(tuple(pair))
            # Shape and endpoints are representation checks, not source truth.
            if pair[0] not in sigs[field['owner']] or pair[1] not in sigs[field['target']]:
                raise ValueError('witness endpoint type')
            rows.append([1, field['id'], *[labels[a] for a in pair]])
    return ''.join(' '.join(map(str, r)) + '\n' for r in rows)


def decode(runtime, output, witness, spec, ids):
    (output / 'tables.rows').write_text(witness_tables(witness, spec))
    run([runtime.native, 'decode', output / 'model.rows', output, output / 'tables.rows'], output, 'decode')
    if (output / 'decoded.error').exists():
        raise ValueError((output / 'decoded.error').read_text())
    c = dict(objects=[], root=None, members=[], containment=[], references=[])
    inverse = {i: uid for uid, i in ids.items()}
    for row in numeric_rows(output / 'decoded.rows'):
        if row[0] == 0: c['objects'] = row[1:]
        elif row[0] == 1: c['root'] = row[1]
        elif row[0] == 2: c['members'].append([inverse[row[1]], row[2]])
        else: c['containment' if row[0] == 3 else 'references'].append([inverse[row[1]], row[2:]])
    return runtime.relation.canonical(c)


def solve(runtime, output, timeout, heap_mb):
    if type(timeout) is not int or timeout <= 0 or type(heap_mb) is not int or heap_mb < 64:
        raise ValueError('resource profile')
    command = [str(runtime.alloy['java']), f'-Xmx{heap_mb}m', '-Xss1m', '-XX:ActiveProcessorCount=1',
               '-XX:+UseSerialGC', '-XX:ReservedCodeCacheSize=64m', '-XX:CompressedClassSpaceSize=64m',
               '-cp', runtime.classpath, 'ComparisonBridge']
    oracle.write(output / 'solver-command.json', command)
    oracle.write(output / 'profile.json', dict(runtime=runtime.identity, timeout=timeout, heap_mb=heap_mb,
                                             address_space_mb=heap_mb + 2048, workers=1))
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, ((heap_mb + 2048) * 1024**2,) * 2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    try:
        with (output / 'solver-stdout.log').open('wb') as out, (output / 'solver-stderr.log').open('wb') as err:
            p = subprocess.run(command, cwd=output, stdout=out, stderr=err, env=runtime.env,
                               timeout=timeout, preexec_fn=limits)
        if p.returncode:
            return dict(status='error', outcome=None, detail=f'JVM exit {p.returncode}')
        value = runtime.api['protocol'].loads((output / 'solver.json').read_bytes())
        if type(value) is not dict or value.get('status') not in ('ok', 'error', 'resource_limit') or value.get('outcome') not in (None, 'sat', 'unsat'):
            raise ValueError('solver result schema')
        return value
    except subprocess.TimeoutExpired:
        checkpoint = output / 'execution.json'
        observed = runtime.api['protocol'].loads(checkpoint.read_bytes()) if checkpoint.exists() else {}
        return dict(observed, status='timeout', detail='solver wall-clock limit')


def mutated_candidate(candidate, mutation):
    value = copy.deepcopy(candidate)
    if mutation == 'swap-endpoints':
        value['references'] = [[uid, [b,a]] for uid,(a,b) in value['references']]
    return value



# [impl->req~compiler-differential~1]
def compare(runtime, bundle, candidate_bytes, output, *, bitwidth=8, overall=5, timeout=30,
            heap_mb=512, mutation='none', search=None):
    if mutation not in MUTATIONS: raise ValueError('unknown mutation')
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    p = runtime.api['protocol']
    result = dict(schema='clafer-three-way/1', admission=None, checker=None, haskell=None,
                  compiler=None, category='inconclusive', complete=False, faithful=None)
    shutil.copytree(bundle, output / 'capture')
    (output / 'candidate.json').write_bytes(candidate_bytes)
    settings = dict(bitwidth=bitwidth, overall=overall, timeout=timeout, heap_mb=heap_mb,
                    mutation=mutation, search=search)
    oracle.write(output / 'settings.json', settings)
    oracle.write(output / 'source.json', runtime.source)
    oracle.write(output / 'runtime.json', runtime.identity)
    oracle.write(output / 'runtime-build.json', dict(directory=str(runtime.directory)))
    oracle.write(output / 'replay-command.json', ['python3', str(ROOT / 'scripts/comparison/compare.py'),
        'replay', '--tools', str(runtime.tools), str(output), str(output.with_name(output.name + '-replay'))])
    try:
        core, metadata = p.import_bundle(output / 'capture')
        oracle.write(output / 'core.json', core)
        candidate = p.loads(candidate_bytes)
        verdict = runtime.check(core, candidate)
        oracle.write(output / 'checker.json', verdict)
        oracle.write(output / 'checker-runtime.json', runtime.api['checker_runtime'].worker.identity)
        if verdict['status'] not in ('satisfies', 'violates'):
            result.update(category=verdict['status'], admission=verdict['status'])
        else:
            runtime.relation.validate_candidate(candidate, core, metadata['bounds'])
            result.update(checker=verdict['status'], admission='admitted')
            model, ids = transport(core, metadata['bounds'], bitwidth)
            (output / 'model.rows').write_text(model)
            run([runtime.native, 'compile', output / 'model.rows', output, mutation], output, 'native')
            if (output / 'compile.error').exists():
                status = (output / 'compile.error').read_text()
                p.reject('native_compilation', category=status)
            spec = layout(output, ids)
            oracle.write(output / 'layout.json', spec)
            original = (output / 'generated.als').read_text()
            effective = original
            if mutation == 'drop-disjointness':
                # In this backend disjointness is enforced by extends, not a fact.
                effective = effective.replace(' extends cc0', ' in cc0')
                effective = effective.replace('abstract sig cc0', 'sig cc0')
                # Alloy forbids command scopes on subset signatures. Keep the
                # identical bounds as explicit predicates in this mutant.
                for uid, mapping in spec['maps'].items():
                    scope = metadata['bounds'][uid]
                    effective = effective.replace(f" , {scope} {mapping['signature']}", '')
                    effective += f"\nfact {{ #{mapping['signature']} <= {scope} }}\n"
            if mutation == 'reject-all': effective += '\nfact { some none }\n'
            pinned = (importlib.import_module('mutations').inject('collapse_bag_heads', original, candidate, core, metadata)[1]
                      if mutation == 'collapse-occurrence' else mutated_candidate(candidate, mutation))
            oracle.write(output / 'pinned-candidate.json', pinned)
            pin_text = pin(pinned, spec)
            (output / 'pin.als').write_text(pin_text)
            (output / 'comparison.als').write_text(effective + '\n' + pin_text)
            bounds = {'cc0': sum(metadata['bounds'].values()),
                      **{v['signature']: metadata['bounds'][u] for u,v in spec['maps'].items()}}
            oracle.write(output / 'request.json', dict(bitwidth=bitwidth, bounds=bounds,
                fields=spec['fields'], signatures=spec['signatures'],
                scope_bounds={'cc0': bounds['cc0']} if mutation == 'drop-disjointness' else bounds,
                subset_mutation=mutation == 'drop-disjointness', maximum=2**(bitwidth-1)-1))
            # The solver processes consume immutable inputs independently. The
            # upstream checker is used only by its worker until the future joins.
            with ThreadPoolExecutor(max_workers=1) as executor:
                haskell = executor.submit(runtime.api['comparison'].compare,
                    output / 'capture', None, output / 'haskell', runtime=runtime.alloy,
                    candidate_bytes=candidate_bytes, bitwidth=bitwidth, overall=overall,
                    timeout=timeout, heap_mb=heap_mb, search=search)
                solved = solve(runtime, output, timeout, heap_mb)
                h = haskell.result()
            result['haskell'] = h
            result['compiler'] = solved
            if solved['status'] == 'ok' and solved['outcome'] == 'sat':
                try:
                    decoded = decode(runtime, output, solved['witness'], spec, ids)
                    oracle.write(output / 'decoded.json', decoded)
                    runtime.relation.validate_candidate(decoded, core, metadata['bounds'])
                    bijection = runtime.relation.isomorphism(candidate, decoded)
                    oracle.write(output / 'bijection.json', bijection)
                    checked = runtime.check(core, decoded)
                    oracle.write(output / 'decoded-checker.json', checked)
                    result['faithful'] = bijection is not None and checked['status'] == verdict['status']
                except (ValueError, KeyError, TypeError) as error:
                    result['faithful'] = False
                    result['decode_error'] = str(error)
            c = runtime.api['comparison'].category(verdict['status'], solved.get('outcome'), result['faithful'])
            c = {'alloy_accepts_lean_rejects': 'compiler_accepts_checker_rejects',
                 'lean_accepts_alloy_rejects': 'checker_accepts_compiler_rejects'}.get(c, c)
            if solved['status'] != 'ok': c = solved['status']
            result['category'] = (h['category'] if not h['complete'] else
                                  c if h['category'].startswith('agree_') else 'haskell_' + h['category'])
            result['complete'] = h['complete'] and c in ('agree_satisfies', 'agree_violates',
                'compiler_accepts_checker_rejects', 'checker_accepts_compiler_rejects')
    except p.Rejection as error:
        result.update(category=error.category, diagnostic=error.result())
    except (TimeoutError, subprocess.TimeoutExpired) as error:
        result.update(category='timeout', diagnostic=str(error))
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as error:
        result.update(category='error', diagnostic=str(error))
    if source_identity() != runtime.source:
        result.update(category='source_changed', complete=False)
    oracle.write(output / 'result.json', result)
    oracle.write(output / 'evidence-index.json', {str(f.relative_to(output)): oracle.digest(f)
        for f in sorted(output.rglob('*')) if f.is_file()})
    return result


def replay(runtime, previous, output):
    previous = Path(previous)
    p = runtime.api['protocol']
    index = p.loads((previous / 'evidence-index.json').read_bytes())
    actual = {str(f.relative_to(previous)): oracle.digest(f) for f in previous.rglob('*')
              if f.is_file() and f != previous / 'evidence-index.json'}
    if index != actual or p.loads((previous / 'source.json').read_bytes()) != runtime.source:
        raise ValueError('replay input/output or source identity changed')
    if p.loads((previous / 'runtime.json').read_bytes()) != runtime.identity:
        raise ValueError('replay runtime identity changed')
    result = compare(runtime, previous / 'capture', (previous / 'candidate.json').read_bytes(), output,
                     **p.loads((previous / 'settings.json').read_bytes()))
    before = p.loads((previous / 'result.json').read_bytes())
    if any(result[k] != before[k] for k in ('category', 'complete', 'checker', 'faithful')):
        raise ValueError('replay outcome changed')
    return result


def minimize(runtime, previous, output):
    previous, output = Path(previous), oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    p = runtime.api['protocol']
    initial = replay(runtime, previous, output / 'initial')
    if initial['category'] in ('agree_satisfies', 'agree_violates') or not initial['complete']:
        raise ValueError('minimization needs a completed discrepancy')
    core, metadata = p.import_bundle(previous / 'capture')
    settings = p.loads((previous / 'settings.json').read_bytes())
    attempt = 0
    def preserves(candidate):
        nonlocal attempt
        attempt += 1
        r = compare(runtime, previous / 'capture', p.encoded(candidate), output / f'trial-{attempt}', **settings)
        if not r['complete']: raise RuntimeError('inconclusive minimization; minimality not established')
        return r['category'] == initial['category']
    candidate, count = runtime.candidates.shrink(p.loads((previous / 'candidate.json').read_bytes()),
                                                core, metadata['bounds'], preserves)
    oracle.write(output / 'minimal.json', candidate)
    result = dict(category=initial['category'], deletion_minimal=True, attempts=count)
    oracle.write(output / 'result.json', result)
    return result


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    sub = cli.add_subparsers(dest='command', required=True)
    for name in ('compare', 'replay', 'search', 'minimize'):
        parser = sub.add_parser(name)
        parser.add_argument('--tools', type=Path, required=True)
        parser.add_argument('input', type=Path)
        if name == 'compare': parser.add_argument('candidate', type=Path)
        parser.add_argument('output', type=Path)
        if name in ('compare', 'search'):
            parser.add_argument('--bitwidth', type=int, default=8)
            parser.add_argument('--overall', type=int, default=5)
        if name == 'compare': parser.add_argument('--mutation', choices=MUTATIONS, default='none')
        if name == 'search':
            parser.add_argument('--mode', choices=('exhaustive', 'seeded'), required=True)
            parser.add_argument('--seed', type=int)
            parser.add_argument('--count', type=int)
            parser.add_argument('--limit', type=int)
    args = cli.parse_args()
    output = oracle.external(args.output)
    runtime = Runtime(args.tools, Path(tempfile.mkdtemp(prefix='clafer-three-way-runtime-')) / 'build')
    if args.command == 'replay': result = replay(runtime, args.input, output)
    elif args.command == 'minimize': result = minimize(runtime, args.input, output)
    elif args.command == 'compare':
        result = compare(runtime, args.input, args.candidate.read_bytes(), output,
                         bitwidth=args.bitwidth, overall=args.overall, mutation=args.mutation)
    else:
        if args.mode == 'seeded' and (args.seed is None or args.count is None or args.count < 0):
            cli.error('seeded mode requires --seed and nonnegative --count')
        if args.limit is not None and args.limit < 0: cli.error('negative limit')
        output.mkdir(parents=True, exist_ok=False)
        core, meta = runtime.api['protocol'].import_bundle(args.input)
        stream = (runtime.candidates.domain(core, meta['bounds']) if args.mode == 'exhaustive' else
                  runtime.candidates.generated(core, meta['bounds'], args.seed, args.count))
        spec = dict(mode=args.mode, seed=args.seed, count=args.count, bounds=meta['bounds'],
                    domain='fresh-root-all-tables/v1', symmetry_reduction=False)
        oracle.write(output / 'search.json', spec)
        result = runtime.candidates.batch(stream, lambda c,i: compare(runtime, args.input,
            runtime.api['protocol'].encoded(c), output / f'case-{i}', bitwidth=args.bitwidth,
            overall=args.overall, search=dict(spec,index=i)), mode=args.mode, expected=args.count,
            seed=args.seed, limit=args.limit)
        oracle.write(output / 'result.json', result)
    print(json.dumps(result, sort_keys=True))
    ok = result.get('complete') and result['category'] in ('agree_satisfies', 'agree_violates')
    if args.command == 'search':
        ok = result['exhausted'] and result['requested'] == result['completed'] and all(
            c in ('agree_satisfies', 'agree_violates') for c in result['categories'])
    if args.command == 'minimize': ok = result['deletion_minimal']
    return 0 if ok else 1


if __name__ == '__main__':
    try: raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps(dict(category='error', detail=str(error))), file=sys.stderr)
        raise SystemExit(1)
