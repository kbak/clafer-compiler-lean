"""Actual compiler output, pinned Alloy SAT4J, and concrete identity witnesses."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
sys.path.insert(0, str(ROOT / 'scripts'))
import oracle
import project_modules
import temporal


# [utest->req~compiler-behavioral-encoding~1]
# [utest->req~compiler-trace-representation~1]
# [utest->req~compiler-behavioral-correctness~1]
class BehavioralEncodingTests(unittest.TestCase):
    def test_compiled_lifetime_and_identity_cases(self):
        config = os.environ.get('CLAFER_ORACLE_TOOLS')
        self.assertTrue(config, 'CLAFER_ORACLE_TOOLS required')
        api = oracle.adapters()
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='behavioral-encoding-', dir=parent))
        print(f'Behavioral encoding evidence: {output}', flush=True)
        runtime = temporal.compile_bridge(runtime, output / 'classes', api)
        env = api['alloy_runtime'].java_env()

        # Resolve only the fixture's runtime import closure. Reject proof imports
        # before linking, so execution cannot accidentally use source semantics.
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

        include('tests.BehavioralEncodingNative')
        sources = [ROOT / (m.replace('.', '/') + '.lean') for m in modules]
        sources += [Path(__file__), ROOT / 'scripts/project_modules.py',
                    ROOT / 'scripts/oracles/temporal.py',
                    ROOT / 'scripts/oracles/AlloyTemporalBridge.java']
        identities = {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources}
        for p in sources:
            dest = output / 'source' / p.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(p.read_bytes())
        oracle.write(output / 'source.json', identities)

        def run(name, command, timeout=120):
            oracle.write(output / (name + '-command.json'), command)
            with (output / (name + '-stdout.log')).open('w') as out, \
                    (output / (name + '-stderr.log')).open('w') as err:
                subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=err,
                               check=True, timeout=timeout)

        run('build-native', ['lake', 'build', *['+' + m + ':c.o' for m in modules]])
        harness = output / 'Harness.lean'
        harness.write_text('import tests.BehavioralEncodingNative\n'
                           'def main (args : List String) : IO Unit := '
                           'ClaferCompiler.Tests.BehavioralEncoding.run args\n')
        c_file, executable = output / 'Harness.c', output / 'behavioral-encoding'
        run('compile-native', ['lake', 'env', 'lean', f'--root={output}', '-c', str(c_file), str(harness)])
        run('link-native', ['lake', 'env', 'leanc', str(c_file),
                           *[str(ROOT / '.lake/build/ir' / (m.replace('.', '/') + '.c.o.export'))
                             for m in modules], '-o', str(executable)])
        generated = output / 'generated'
        run('native', [str(executable), str(generated)])
        self.assertIn('native trace roundtrips', (output / 'native-stdout.log').read_text())
        files = sorted(generated.glob('*.als'))
        self.assertEqual(len(files), 35)
        results = {}
        for path in files:
            with self.subTest(case=path.stem):
                lines = path.with_suffix('.bounds').read_text().splitlines()
                width, low, high = map(int, lines[0].split('\t'))
                scopes = {}
                for line in lines[1:]:
                    name, size, exact = line.split('\t')
                    scopes['this/' + name] = dict(count=int(size), exact=exact == 'true')
                request = dict(command_index=0, overall=6, bitwidth=width,
                               min_steps=low, max_steps=high, identities=scopes)
                case_dir = output / path.stem
                case_dir.mkdir()
                (case_dir / 'model.als').write_bytes(path.read_bytes())
                result = temporal.solve(runtime, api, case_dir, request)
                oracle.write(case_dir / 'result.json', result)
                self.assertEqual(result['status'], 'ok', result)
                original = result['original_command']
                self.assertEqual(original['check'], path.stem == 'bag-counterexample')
                self.assertEqual((original['bitwidth'], original['min_steps'], original['max_steps']),
                                 (width, low, high))
                self.assertEqual({s['signature']: (s['start'], s['exact']) for s in original['scopes']},
                                 {name: (scope['count'], scope['exact']) for name, scope in scopes.items()})
                self.assertEqual(result['outcome'], path.with_suffix('.expected').read_text(), result)
                results[path.stem] = result
                if result['outcome'] == 'sat':
                    trace = result['trace']
                    labels = {atom: i for i, atom in enumerate(trace['inventory'])}
                    (case_dir / 'trace.rows').write_text(f"{len(trace['frames'])} {trace['loop']}\n")
                    (case_dir / 'inventory.rows').write_text(' '.join(map(str, labels.values())) + '\n')
                    for t, frame in enumerate(trace['frames']):
                        lines = ['5 6']
                        for i in range(5):
                            atoms = frame['signatures'][f'this/cc{i * 4}']
                            lines.append(' '.join(map(str, [0] + [labels[a[0]] for a in atoms])))
                        for i in range(6):
                            owner = 4 if i == 1 else 0
                            rows = frame['fields'][f'this/cc{owner}/cc{i * 4 + 1}']
                            lines.extend(f'1 {i} {labels[a]} {labels[b]}' for a, b in rows)
                        (case_dir / f'frame-{t}.rows').write_text('\n'.join(lines) + '\n')
                    expected = ('changing-identity' if path.stem == 'renaming-mutable-parent-mutant'
                                else 'invalid' if path.stem == 'missing-state-invariants-mutant'
                                else 'valid')
                    run(path.stem + '-replay', [str(executable), 'replay', str(case_dir), expected])

        # Check concrete observations, independently of the compiler's expectation
        # labels: two distinct bag heads share one target, the old parent leaves,
        # and exactly those same identities reappear across the cycle.
        stable = results['stable-bag']['trace']
        self.assertEqual(stable['loop'], 0)
        self.assertEqual(len(stable['inventory']), 6)
        frames = stable['frames']
        fields = frames[0]['fields']
        reference = fields['this/cc0/cc17']
        self.assertEqual(len(reference), 2)
        self.assertEqual(len({row[0] for row in reference}), 2)
        self.assertEqual(len({row[1] for row in reference}), 1)
        parents = fields['this/cc0/cc1']
        live = [{row[1] for row in s['fields']['this/cc4/cc5']} for s in frames]
        parent = next(row[1] for row in parents if row[0] == reference[0][0])
        self.assertIn(parent, live[0])
        self.assertNotIn(parent, live[2])
        self.assertIn(parent, live[3])
        self.assertEqual(identities, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / 'evidence-index.json', {
            str(p.relative_to(output)): oracle.digest(p) for p in sorted(output.rglob('*')) if p.is_file()})
