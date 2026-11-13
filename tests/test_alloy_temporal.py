"""Checked temporal output against the actual pinned Alloy parser and SAT4J."""
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle
import temporal
sys.path.insert(0, str(ROOT / 'scripts'))
import project_modules


# [utest->req~compiler-alloy-temporal-target~1]
# [utest->req~compiler-alloy-temporal-text~1]
class AlloyTemporalTests(unittest.TestCase):
    def test_checked_text_and_temporal_witnesses(self):
        config = os.environ.get('CLAFER_ORACLE_TOOLS')
        self.assertTrue(config, 'CLAFER_ORACLE_TOOLS required')
        api = oracle.adapters()
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='alloy-temporal-', dir=parent))
        print(f'Temporal target evidence: {output}', flush=True)
        runtime = temporal.compile_bridge(runtime, output / 'classes', api)
        env = api['alloy_runtime'].java_env()
        modules = []
        forbidden = ('Clafer.', 'Mathlib.', 'ClaferCompiler.SemanticsBridge',
                     'ClaferCompiler.Correctness')

        def include(module):
            if module in modules:
                return
            self.assertFalse(module.startswith(forbidden), module)
            path = ROOT / (module.replace('.', '/') + '.lean')
            for dependency in project_modules.imports(path.read_text()):
                self.assertFalse(dependency.startswith(forbidden), dependency)
                if (ROOT / (dependency.replace('.', '/') + '.lean')).exists():
                    include(dependency)
            modules.append(module)

        include('tests.AlloyTemporalNative')
        sources = [ROOT / (m.replace('.', '/') + '.lean') for m in modules]
        sources += [Path(__file__), ROOT / 'scripts/project_modules.py',
                    ROOT / 'scripts/oracles/AlloyTemporalBridge.java',
                    ROOT / 'scripts/oracles/temporal.py']
        identities = {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources}
        for p in sources:
            dest = output / 'source' / p.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(p.read_bytes())
        oracle.write(output / 'source.json', identities)

        def run(name, command, cwd=ROOT, timeout=120):
            oracle.write(output / (name + '-command.json'), command)
            with (output / (name + '-stdout.log')).open('w') as out, \
                    (output / (name + '-stderr.log')).open('w') as err:
                subprocess.run(command, cwd=cwd, env=env, stdout=out, stderr=err,
                               check=True, timeout=timeout)

        run('build-native', ['lake', 'build', *['+' + m + ':c.o' for m in modules]])
        harness = output / 'Harness.lean'
        harness.write_text('import tests.AlloyTemporalNative\n'
                           'def main (args : List String) : IO Unit := '
                           'ClaferCompiler.Tests.AlloyTemporalNative.run args\n')
        c_file, executable = output / 'Harness.c', output / 'temporal-tests'
        run('compile-native', ['lake', 'env', 'lean', f'--root={output}', '-c', str(c_file), str(harness)])
        run('link-native', ['lake', 'env', 'leanc', str(c_file),
                           *[str(ROOT / '.lake/build/ir' / (m.replace('.', '/') + '.c.o.export'))
                             for m in modules], '-o', str(executable)])
        generated = output / 'generated'
        run('native', [str(executable), str(generated)])
        self.assertIn('rejecting parser mutations', (output / 'native-stdout.log').read_text())
        files = sorted(generated.glob('*.als'))
        self.assertGreater(len(files), 100)
        results = {}
        cases = []
        for path in files:
            with self.subTest(case=path.stem):
                raw = path.read_bytes()
                self.assertTrue(raw.isascii())
                self.assertNotIn(b'/*', raw)
                for line in path.with_suffix('.map').read_text().splitlines():
                    name, start, end = line.split('\t')
                    self.assertEqual(raw[int(start):int(end)].decode(), name)
                lines = path.with_suffix('.bounds').read_text().splitlines()
                width, low, high = map(int, lines[0].split('\t'))
                scopes = {}
                for line in lines[1:]:
                    name, size, exact = line.split('\t')
                    scopes['this/' + name] = dict(count=int(size), exact=exact == 'true')
                request = dict(command_index=0, overall=4, bitwidth=width,
                               min_steps=low, max_steps=high, identities=scopes)
                case_dir = output / path.stem
                case_dir.mkdir()
                (case_dir / 'model.als').write_bytes(raw)
                cases.append((path, case_dir, request))

        def solve(case):
            path, case_dir, request = case
            scalar_fields = path.with_suffix('.integer-fields').read_text().splitlines()
            # Full-profile expression expansion needs room for Alloy's parsed
            # types as well as bounded solving; retain every original witness.
            result = temporal.solve(runtime, api, case_dir, request, timeout=120,
                                    heap_mb=1024, integer_fields=scalar_fields)
            oracle.write(case_dir / 'result.json', result)
            return result

        # Reuse the regression runner's CPU-capped worker setting, with fresh
        # JVMs and disjoint directories. All unittest checks stay on this thread.
        requested = int(os.environ.get('CLAFER_TEST_JOBS', '2'))
        if not 1 <= requested <= 4:
            raise ValueError('CLAFER_TEST_JOBS must be between 1 and 4')
        cpus = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else (os.cpu_count() or 1)
        with ThreadPoolExecutor(max_workers=min(requested, cpus)) as pool:
            futures = [pool.submit(solve, case) for case in cases]
            for (path, _, request), future in zip(cases, futures):
                with self.subTest(case=path.stem):
                    result = future.result()
                    self.assertEqual(result['status'], 'ok', result)
                    original = result['original_command']
                    # The bridge overrides bounds for reproducibility; independently
                    # verify that the actual emitted command already had those bounds.
                    self.assertEqual((original['bitwidth'], original['min_steps'], original['max_steps']),
                                     (request['bitwidth'], request['min_steps'], request['max_steps']))
                    self.assertEqual({s['signature']: (s['start'], s['exact']) for s in original['scopes']},
                                     {name: (scope['count'], scope['exact'])
                                      for name, scope in request['identities'].items()})
                    expected = path.with_suffix('.expected')
                    if expected.exists():
                        self.assertEqual(result['outcome'], expected.read_text(), result)
                    results[path.stem] = result
        self.assertGreater(results['nonzero-prefix']['trace']['loop'], 0)
        self.assertEqual(len(results['identity-two']['trace']['inventory']), 2)
        trace = results['birth-loop']['trace']
        self.assertEqual(trace['frames'][0]['signatures']['this/cc0'],
                         trace['frames'][2 if len(trace['frames']) > 2 else trace['loop']]['signatures']['this/cc0'])
        fields = results['mutable-field']['trace']['frames']
        self.assertTrue(fields[0]['fields']['this/cc0/cc1'])
        self.assertFalse(fields[1]['fields']['this/cc0/cc1'])
        self.assertEqual(identities, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / 'evidence-index.json', {
            str(p.relative_to(output)): oracle.digest(p) for p in sorted(output.rglob('*')) if p.is_file()})
