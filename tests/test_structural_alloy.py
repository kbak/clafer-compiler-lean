"""Link the actual backend and execute independent positive/negative candidates."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-structural-encoding~1]
class StructuralAlloyTests(unittest.TestCase):
    def test_independent_upstream_candidates(self):
        result = subprocess.run(
            ['lake', 'env', 'lean', 'tests/StructuralAlloyComparison.lean'], cwd=ROOT,
            capture_output=True, text=True, timeout=45)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('39 fixtures and 256 generated candidates agree with upstream; 10 generated positives', result.stdout)

    def test_native_structural_generation(self):
        modules = [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.Backend.Alloy.Syntax',
            'ClaferCompiler.Backend.Alloy.Bounds', 'ClaferCompiler.Backend.Alloy.Semantics',
            'ClaferCompiler.Backend.Alloy.Structural',
            'tests.StructuralNative', 'tests.StructuralAlloyNative',
        ]

        def run(*args):
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result

        run('lake', 'build', *(f'+{m}:c.o' for m in modules))
        with tempfile.TemporaryDirectory(prefix='clafer-structural-native-') as tmp:
            directory = Path(tmp)
            harness = directory / 'Harness.lean'
            harness.write_text('import tests.StructuralAlloyNative\n'
                               'def main : IO Unit := ClaferCompiler.Tests.StructuralAlloy.run\n')
            c_file, binary = directory / 'Harness.c', directory / 'structural-tests'
            run('lake', 'env', 'lean', f'--root={directory}', '-c', str(c_file), str(harness))
            objects = [f'.lake/build/ir/{m.replace(".", "/")}.c.o.export' for m in modules]
            run('lake', 'env', 'leanc', str(c_file), *objects, '-o', str(binary))
            result = run(str(binary))
            self.assertEqual(result.stderr, '')
            self.assertIn('39 structural candidates; 28 admission fixtures; 6 obligation mutations;', result.stdout)
