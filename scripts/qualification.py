#!/usr/bin/env python3
"""Measure and package a private candidate; never publish or grant acceptance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import signal
import statistics
import subprocess
import sys
import tarfile
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


def write(path, value):
    oracle.write(path, value)


def sha(path):
    return oracle.digest(path)


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def source_identity():
    names = subprocess.check_output(['git', '-C', str(ROOT), 'ls-files', '--cached',
        '--others', '--exclude-standard', '-z']).decode().split('\0')
    files = {n: sha(ROOT/n) for n in sorted(set(filter(None, names))) if (ROOT/n).is_file()}
    return {'commit': git('rev-parse', 'HEAD'),
            'dirty': bool(git('status', '--porcelain')),
            'sha256': hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest(),
            'files': files}


def new_output(path):
    output = oracle.external(path)
    output.mkdir(parents=True, exist_ok=False)
    return output


# [impl->req~compiler-performance~1]
def measure(command, output, name, *, cwd=ROOT, timeout=600, env=None, allowed=(0,)):
    """One fresh process tree per sample; RSS is not cumulative across samples.

    GNU time observes the child and its waited-for descendants. Timeout kills the
    whole session and retains logs. Metrics are observations, not assertions of
    speed or semantic agreement.
    """
    command = list(map(str, command))
    clock = shutil.which('time')
    if not clock:
        raise RuntimeError('GNU time is required')
    metric = output/(name+'.time.json')
    wrapper = [clock, '-f', '{"wall_seconds":%e,"user_seconds":%U,'
               '"system_seconds":%S,"max_rss_kib":%M}', '-o', str(metric), *command]
    write(output/(name+'.command.json'), {'argv': command, 'cwd': str(cwd),
        'timeout_seconds': timeout, 'environment_overrides': env or {}})
    started = time.perf_counter_ns()
    with (output/(name+'.stdout')).open('wb') as stdout, (output/(name+'.stderr')).open('wb') as stderr:
        proc = subprocess.Popen(wrapper, cwd=cwd, env=dict(os.environ, **(env or {})),
                                stdout=stdout, stderr=stderr, start_new_session=True)
        expired = threading.Event()
        def stop():
            expired.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        deadline = threading.Timer(timeout, stop)
        deadline.start()
        try:
            # POSIX wait(timeout=...) polls with growing sleeps, which would
            # quantize fast compiler measurements. Use a blocking wait instead.
            code = proc.wait()
        finally:
            deadline.cancel()
            deadline.join()
        status = 'timeout' if expired.is_set() else 'completed'
    elapsed = time.perf_counter_ns() - started
    # GNU time prefixes failure diagnostics; only its last line is JSON.
    metrics = json.loads(metric.read_text().splitlines()[-1]) if metric.exists() and metric.stat().st_size else {}
    result = dict(status=status, exit_code=code, elapsed_ns=elapsed, **metrics)
    write(output/(name+'.result.json'), result)
    if status != 'completed' or code not in allowed:
        raise RuntimeError(f'{name}: {status}, exit {code}; see {output}')
    return result


def machine():
    cpu = Path('/proc/cpuinfo').read_text()
    model = next((s.split(':', 1)[1].strip() for s in cpu.splitlines() if s.startswith('model name')), '')
    return {'platform': platform.platform(), 'machine': platform.machine(),
        'cpu': model, 'logical_cpus': os.cpu_count(),
        'affinity': sorted(os.sched_getaffinity(0)), 'python': sys.version,
        'memory': Path('/proc/meminfo').read_text().splitlines()[0],
        'load_average': os.getloadavg(),
        'time_version': subprocess.check_output(['time', '--version'], text=True).splitlines()[0],
        'lean_version': subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip(),
        'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
        'dependencies': json.loads((ROOT/'lake-manifest.json').read_text()),
        'oracle_profile': json.loads(oracle.PROFILE.read_text())}


def build_probe(output):
    measure(['lake', 'build', 'clafer-compiler', '+tests.QualificationNative:c.o'], output, 'probe-build')
    objects = [p for p in shlex.split((ROOT/'.lake/build/bin/clafer-compiler.rsp').read_text())
               if p.endswith('.c.o.export') and Path(p).name != 'Main.c.o.export']
    if not objects:
        raise RuntimeError('Missing production object closure')
    harness = output/'Probe.lean'
    harness.write_text('import tests.QualificationNative\ndef main (args : List String) : IO Unit :=\n'
                       '  ClaferCompiler.Tests.Qualification.run args\n')
    measure(['lake', 'env', 'lean', f'--root={output}', '-c', output/'Probe.c', harness], output, 'probe-compile')
    binary = output/'stage-probe'
    measure(['lake', 'env', 'leanc', output/'Probe.c', *objects,
             '.lake/build/ir/tests/QualificationNative.c.o.export', '-o', binary], output, 'probe-link')
    return binary


def generated(count):
    """Common structural domain: explicit cards, unique names, no default dispute."""
    if not 1 <= count <= 48:
        raise ValueError('count must be 1..48 for the width-16 benchmark profile')
    source = ''.join(f'Owner{i} 0..1\n  field{i} 0..1\n  ref{i} -> field{i} 0..1\n'
                     for i in range(count))
    bounds = {'version': 'clafer-bounds/2', 'objects': 1+count*3, 'bitwidth': 16,
              'declarations': [{'id': i, 'size': 1, 'exact': i == 0} for i in range(1+count*3)],
              'integers': []}
    names = [name for i in range(count) for name in (f'Owner{i}', f'field{i}', f'ref{i}')]
    return source, bounds, names


def corpus(output):
    result = []
    for name, count in [('tiny', 1), ('representative', 8), ('larger', 48)]:
        source, bounds, names = generated(count)
        directory = output/name
        directory.mkdir()
        (directory/'input.cfr').write_text(source)
        write(directory/'bounds.json', bounds)
        # Haskell's root is virtual; these are the identical user-declaration
        # upper bounds. The explicit Lean root accounts for the extra object.
        write(directory/'haskell-bounds.json', {'bitwidth': bounds['bitwidth'],
            'declarations': {n: 1 for n in names}})
        result.append((name, directory, True))
    for name, source, bounds in [
        ('integers', 'tests/fixtures/pipeline/two-values.cfr', 'tests/fixtures/pipeline/two-values.bounds.json'),
        ('telematics', 'tests/fixtures/constraints/telematics.cfr', 'tests/fixtures/pipeline/telematics.bounds.json')]:
        directory = output/name
        directory.mkdir()
        shutil.copyfile(ROOT/source, directory/'input.cfr')
        shutil.copyfile(ROOT/bounds, directory/'bounds.json')
        result.append((name, directory, False))
    return result


def build_haskell(work, output):
    api = oracle.adapters()
    work = Path(work).resolve()
    if not api['runtime'].valid_runtime(work/'clafer-capture', work/'build.json'):
        raise ValueError('Haskell work directory must come from the pinned upstream build recipe')
    # Check the extracted library sources against the immutable archive, not just
    # the previously built exporter receipt.
    archive = work/'compiler.tar.gz'
    if sha(archive)['sha256'] != api['protocol'].ARCHIVE:
        raise ValueError('Wrong Haskell source archive')
    with tarfile.open(archive) as packed:
        for item in packed.getmembers():
            if item.isfile():
                name = Path(item.name).relative_to(item.name.split('/')[0])
                if (work/'compiler'/name).read_bytes() != packed.extractfile(item).read():
                    raise ValueError(f'Modified pinned Haskell source: {name}')
    binary = output/'haskell-benchmark'
    objects = output/'haskell-objects'
    objects.mkdir()
    measure([work/'stack', 'exec', '--', 'ghc', '-O2', '-package', 'clafer', '-package', 'aeson',
        '-package', 'containers', '-package', 'mtl', '-outputdir', objects,
        ROOT/'scripts/qualification/HaskellBenchmark.hs', '-o', binary], output, 'haskell-build',
        cwd=work/'compiler', env={'STACK_ROOT': str(work/'stack-root')})
    write(output/'haskell-build-identity.json', {'upstream': json.loads((work/'build.json').read_text()),
        'adapter': sha(ROOT/'scripts/qualification/HaskellBenchmark.hs'), 'binary': sha(binary),
        'optimization': '-O2; pinned library built by upstream Stack recipe'})
    return binary


def summary(samples):
    keys = set.intersection(*(set(s) for s in samples))
    return {k: {'min': min(s[k] for s in samples), 'median': statistics.median(s[k] for s in samples),
                'max': max(s[k] for s in samples)}
            for k in sorted(keys) if all(isinstance(s[k], (int, float)) and not isinstance(s[k], bool) for s in samples)}


def runtime(args):
    output = new_output(args.out)
    identity = source_identity()
    write(output/'source.json', identity)
    write(output/'machine.json', machine())
    probe = build_probe(output)
    haskell = build_haskell(args.haskell_work, output)
    api = oracle.adapters()
    _, _, analyzer = oracle.load_tools(args.tools, api)
    write(output/'analyzer-identity.json', analyzer['identity'])
    measure([analyzer['java'].with_name('javac'), '--release', '17', '-cp', analyzer['jar'],
        '-d', output, ROOT/'scripts/qualification/BoundsAudit.java'], output, 'bounds-audit-build')
    compiler = ROOT/'.lake/build/bin/clafer-compiler'
    write(output/'binaries.json', {'compiler': sha(compiler), 'probe': sha(probe), 'haskell': sha(haskell)})
    results = []
    for name, directory, common in corpus(output):
        commands = {
            'native': [compiler, 'compile-source', 'input.cfr', '--bounds', 'bounds.json', '--output', 'native.als'],
            'stages': [probe, 'input.cfr', 'bounds.json', 'stages.als']}
        if common:
            commands['haskell'] = [haskell, 'input.cfr', 'haskell-bounds.json', 'haskell.als']
        observations = {tool: [] for tool in commands}
        # Interleave tools and alternate order to reduce systematic order bias.
        for repeat in range(args.warmup + args.samples):
            order = list(commands)
            if repeat % 2:
                order.reverse()
            for tool in order:
                sample = measure(commands[tool], directory, f'{tool}-{repeat}', cwd=directory,
                                 timeout=args.timeout, env={'LEAN_NUM_THREADS': '1'})
                if tool == 'stages':
                    sample.update(json.loads((directory/f'{tool}-{repeat}.stdout').read_text()))
                sample['output_bytes'] = (directory/(tool+'.als')).stat().st_size
                if repeat >= args.warmup:
                    observations[tool].append(sample)
            if (directory/'native.als').read_bytes() != (directory/'stages.als').read_bytes():
                raise RuntimeError('Stage probe differs from the production source CLI')
        results.append({'case': name, 'source': sha(directory/'input.cfr'), 'bounds': sha(directory/'bounds.json'),
            'common_haskell_domain': common, 'samples': observations,
            'summary': {tool: summary(rows) for tool, rows in observations.items()}})
        if common:
            bounds = json.loads((directory/'bounds.json').read_text())
            receipt = json.loads((directory/'haskell-0.stdout').read_text())
            requested = json.loads((directory/'haskell-bounds.json').read_text())
            if set(receipt['names']) != set(requested['declarations']):
                raise ValueError('Haskell declaration inventory differs')
            mapping = json.loads((directory/'stages-0.stdout').read_text())['signatures']
            names = {row['id']: row['name'] for row in mapping}
            if len(names) != len(mapping) or set(names) != {d['id'] for d in bounds['declarations']}:
                raise ValueError('Native declaration inventory differs')
            inventories = {
                'native': {'cc0': {'size': bounds['objects'], 'exact': False},
                    **{names[d['id']]: {'size': d['size'], 'exact': d['exact']}
                       for d in bounds['declarations']}},
                'haskell': {uid: {'size': requested['declarations'][name], 'exact': False}
                            for name, uid in receipt['names'].items()}}
            for tool, declarations in inventories.items():
                expected = directory/(tool+'-expected-scopes.json')
                write(expected, {'bitwidth': bounds['bitwidth'], 'declarations': declarations})
                measure([analyzer['java'], '-Xmx512m', '-XX:ActiveProcessorCount=1', '-XX:+UseSerialGC',
                    '-cp', os.pathsep.join([str(output), str(analyzer['jar'])]), 'BoundsAudit',
                    directory/(tool+'.als'), expected, directory/(tool+'-parsed-scopes.json')],
                    directory, tool+'-bounds-audit', cwd=directory, timeout=30)
    if source_identity() != identity:
        raise RuntimeError('Source changed during runtime measurement')
    write(output/'runtime.json', {'schema': 'clafer-runtime-benchmark/1', 'source': identity,
        'warmup': args.warmup, 'samples': args.samples, 'cases': results,
        'solver_invocations': 0, 'rss_unit': 'KiB, whole child process high-water mark',
        'stage_unit': 'nanoseconds; input/output IO and startup excluded',
        'haskell_boundary': 'whole native pinned library parse/desugar/compile/static generation; no solver; explicit upper scopes',
        'limitations': ['Fresh processes with warm filesystem caches; not cold OS boots.',
            'Stage probe includes checked reconstruction; Haskell has no corresponding proof check.',
            'Timing is machine/load specific, with no speedup or semantic-equivalence assertion.',
            'Haskell comparisons use common structural inputs; integer and telematics cases are Lean-only.']})
    print(output/'runtime.json')


def clean_candidate(candidate):
    commit = git('rev-parse', candidate+'^{commit}')
    if git('rev-parse', 'HEAD') != commit or git('status', '--porcelain'):
        raise ValueError('Candidate must be the clean current commit, including untracked source')
    return commit


def export_source(commit, output):
    archive = output/'source.tar'
    subprocess.run(['git', '-C', str(ROOT), 'archive', '--format=tar', '-o', str(archive), commit], check=True)
    target = output/'source'
    target.mkdir()
    with tarfile.open(archive) as packed:
        for member in packed.getmembers():
            path = target/member.name
            if not path.resolve().is_relative_to(target) or not (member.isdir() or member.isfile()):
                raise ValueError('Unexpected source archive member')
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(packed.extractfile(member).read())
                path.chmod(member.mode)
    return target


def linker_inventory(response):
    words = shlex.split(response.read_text())
    directories = [Path(words[i+1]) for i, word in enumerate(words[:-1]) if word == '-L']
    archives = {}
    for word in words:
        if word.startswith('-l') and not word.startswith('-l:'):
            name = 'lib'+word[2:]+'.a'
            for directory in directories:
                if (directory/name).is_file():
                    archives[name] = sha(directory/name)
                    break
    if 'libgmp.a' not in archives or 'libleanrt.a' not in archives:
        raise ValueError('Unrecognized native link closure; review runtime licensing before packaging')
    return {'archive_inputs': archives,
            'boundary': 'Link command inputs, not a claim that every archive member survives section GC'}


def builds(args):
    commit = clean_candidate(args.candidate)
    output = new_output(args.out)
    identity = source_identity()
    write(output/'machine.json', machine())
    source = export_source(commit, output)
    (source/'.lake').mkdir()
    # Only prepared pinned dependencies are reused. No project output is copied.
    subprocess.run(['cp', '-a', '--reflink=auto', str(ROOT/'.lake/packages'), str(source/'.lake/packages')], check=True)
    measure(['python3', 'scripts/project_modules.py', '--dependencies'], output, 'dependencies', cwd=source)
    env = {'LEAN_NUM_THREADS': '4', 'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_RESTORE_ARTIFACTS': 'true'}
    result = {'schema': 'clafer-build-benchmark/1', 'source': identity,
        'cold_definition': 'No project build outputs; prepared immutable dependencies and OS caches reused',
        'proof_boundary': 'lake build includes proof elaboration; kernel replay measured separately',
        'cold': measure(['lake', 'build'], output, 'cold-build', cwd=source, env=env, timeout=1800),
        'warm': measure(['lake', 'build'], output, 'warm-build', cwd=source, env=env, timeout=1800)}
    for phase in ('first', 'repeat'):
        result['kernel_'+phase] = measure(['lake', 'env', 'leanchecker', '--verbose',
            'ClaferCompiler', 'Main', 'tests'], output, 'kernel-'+phase, cwd=source,
            env={**env, 'LEAN_NUM_THREADS': '2'}, timeout=600)
    result['axiom_audit'] = measure(['lake', 'env', 'lean', '-DwarningAsError=true',
        '.lake/validation/axiom_audit.lean'], output, 'axiom-audit', cwd=source, env=env)
    result['binary'] = sha(source/'.lake/build/bin/clafer-compiler')
    response = source/'.lake/build/bin/clafer-compiler.rsp'
    shutil.copyfile(response, output/'linker.rsp')
    write(output/'linker-inputs.json', linker_inventory(response))
    if source_identity() != identity:
        raise RuntimeError('Source changed during build measurement')
    write(output/'builds.json', result)
    print(output/'builds.json')


def evidence_check(path):
    document = json.loads(path.read_text())
    p = document['predicate']
    if p['status'] not in ('passed', 'review_required') or p['tests']['status'] != 'passed' or p['tests']['source_status'] != 'matched':
        raise ValueError('IntentBond evidence must pass automation and match executed source')
    for name, digest in p['artifacts'].items():
        target = (path.parent/name).resolve()
        if not target.is_relative_to(path.parent.resolve()) or sha(target)['sha256'] != digest:
            raise ValueError(f'Changed evidence artifact: {name}')
    return p


# [impl->req~compiler-qualification~1]
def package(args):
    commit = clean_candidate(args.candidate)
    identity = source_identity()
    evidence = oracle.external(args.evidence)
    p = evidence_check(evidence)
    runtime_dir, build_dir = oracle.external(args.runtime), oracle.external(args.builds)
    runtime_data = json.loads((runtime_dir/'runtime.json').read_text())
    build_data = json.loads((build_dir/'builds.json').read_text())
    for data in (runtime_data, build_data):
        if data['source'] != identity:
            raise ValueError('Measurements do not match the clean candidate')
    oracle_dir = oracle.external(args.oracles)
    if str(oracle_dir) not in (evidence.parent/'tests.log').read_text():
        raise ValueError('Oracle directory is not referenced by this check log')
    output = new_output(args.out)
    measure([args.ib, 'verify', '--repo', ROOT, '--base', args.base, '--candidate', commit,
        '--evidence', evidence, '--allow-pending-review'], output, 'intentbond-verify')
    source = export_source(commit, output)
    binary = build_dir/'source/.lake/build/bin/clafer-compiler'
    if sha(binary) != build_data['binary']:
        raise ValueError('Clean-built binary changed')
    (output/'bin').mkdir()
    shutil.copy2(binary, output/'bin/clafer-compiler')
    licenses = output/'licenses'
    licenses.mkdir()
    shutil.copyfile(ROOT/'LICENSE', licenses/'compiler-MIT.txt')
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT, text=True).strip())
    for name in ('LICENSE', 'LICENSES'):
        shutil.copyfile(prefix/name, licenses/('lean-'+name+'.txt'))
    shutil.copyfile(ROOT/'.lake/packages/clafer/LICENSE', licenses/'semantics-MIT.txt')
    shutil.copyfile(ROOT/'.lake/packages/mathlib/LICENSE', licenses/'mathlib-Apache-2.0.txt')
    shutil.copytree(evidence.parent, output/'intentbond')
    # Receipts and generated inputs/outputs, without comparison tool binaries.
    shutil.copytree(runtime_dir, output/'runtime', ignore=shutil.ignore_patterns(
        'haskell-objects', 'haskell-benchmark', 'stage-probe', 'Probe.c', 'Probe.lean'))
    # Exclude the copied dependency cache and build intermediates from receipts.
    build_receipts = output/'builds'
    build_receipts.mkdir()
    for item in build_dir.iterdir():
        if item.is_file() and item.name != 'source.tar':
            shutil.copyfile(item, build_receipts/item.name)
    shutil.copytree(oracle_dir, output/'oracles')
    shutil.copyfile(oracle.external(args.review), output/'review.json')
    review = json.loads((output/'review.json').read_text())
    if review.get('candidate') != commit or review.get('status') not in ('pending', 'accepted', 'changes_requested'):
        raise ValueError('Review disposition must identify this candidate and an explicit status')
    measure(['ldd', output/'bin/clafer-compiler'], output, 'runtime-libraries')
    # Smoke-test the actual packaged binary in the existing runtime-only sandbox.
    libraries = sorted(set(re.findall(r'(/[^\s()]+)', (output/'runtime-libraries.stdout').read_text())))
    if not libraries or 'not found' in (output/'runtime-libraries.stdout').read_text():
        raise ValueError('Incomplete native runtime library closure')
    smoke = output/'smoke'
    smoke.mkdir()
    for name in ['two-values.cfr', 'two-values.bounds.json']:
        shutil.copyfile(source/'tests/fixtures/pipeline'/name, smoke/name)
    cmd = ['bwrap', '--unshare-user', '--unshare-pid', '--unshare-ipc', '--unshare-uts',
        '--die-with-parent', '--clearenv', '--setenv', 'PATH', '/no-tools', '--setenv', 'LANG', 'C',
        '--ro-bind', output/'bin/clafer-compiler', '/compiler', '--bind', smoke, '/work',
        '--dev', '/dev', '--proc', '/proc', '--chdir', '/work']
    for library in libraries:
        cmd += ['--ro-bind', library, library]
    measure([*cmd, '/compiler', 'compile-source', 'two-values.cfr', '--bounds', 'two-values.bounds.json',
             '--output', 'isolated.als'], output, 'packaged-smoke')
    measure([output/'bin/clafer-compiler', 'compile-source', 'two-values.cfr', '--bounds',
        'two-values.bounds.json', '--output', 'host.als'], output, 'packaged-host', cwd=smoke)
    if (smoke/'isolated.als').read_bytes() != (smoke/'host.als').read_bytes():
        raise ValueError('Packaged isolated output differs')
    write(output/'candidate.json', {'schema': 'clafer-private-candidate/1', 'candidate': commit,
        'baseline': args.base, 'source': identity, 'intentbond_source': p['candidate']['sha256'],
        'automation': p['status'], 'independent_review': review, 'publication': 'not authorized',
        'binary': sha(output/'bin/clafer-compiler'), 'runtime_libraries': {p: sha(p) for p in libraries},
        'licenses': {p.name: sha(p) for p in licenses.iterdir()}})
    write(output/'manifest.json', {str(p.relative_to(output)): sha(p) for p in sorted(output.rglob('*')) if p.is_file()})
    archive = output.with_suffix('.tar.gz')
    if archive.exists():
        raise ValueError('Refusing to replace an existing candidate archive')
    with tarfile.open(archive, 'w:gz') as packed:
        packed.add(output, arcname=output.name)
    print(archive)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    run = commands.add_parser('runtime')
    run.add_argument('--out', required=True, type=Path)
    run.add_argument('--haskell-work', required=True, type=Path)
    run.add_argument('--tools', default=os.environ.get('CLAFER_ORACLE_TOOLS'), type=Path)
    run.add_argument('--samples', type=int, default=5)
    run.add_argument('--warmup', type=int, default=1)
    run.add_argument('--timeout', type=int, default=120)
    build = commands.add_parser('builds')
    build.add_argument('--out', required=True, type=Path)
    build.add_argument('--candidate', default='HEAD')
    pack = commands.add_parser('package')
    for name in ('out', 'evidence', 'runtime', 'builds', 'oracles', 'review'):
        pack.add_argument('--'+name, required=True, type=Path)
    for name in ('candidate', 'base', 'ib'):
        pack.add_argument('--'+name, required=True)
    args = parser.parse_args()
    if args.command == 'runtime' and (args.samples < 2 or args.warmup < 1 or args.timeout < 1):
        parser.error('runtime needs at least two samples, one warmup and a positive timeout')
    if args.command == 'runtime' and args.tools is None:
        parser.error('runtime needs --tools or CLAFER_ORACLE_TOOLS for independent scope auditing')
    {'runtime': runtime, 'builds': builds, 'package': package}[args.command](args)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error)) from error
