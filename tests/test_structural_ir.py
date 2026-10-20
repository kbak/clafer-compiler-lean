"""Link and execute native IR tests without changing the production CLI."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-ir~1]
class StructuralIRTest(unittest.TestCase):
    def test_linked_ir_fixtures(self):
        def run(*args):
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result

        run('lake', 'build', '+tests.StructuralNative:c.o', '+ClaferCompiler.IR.Structural:c.o')
        with tempfile.TemporaryDirectory(prefix='clafer-ir-native-') as tmp:
            directory = Path(tmp)
            harness = directory / 'Harness.lean'
            harness.write_text('import tests.StructuralNative\n'
                               'def main : IO Unit := ClaferCompiler.Tests.Structural.run\n')
            c_file, binary = directory / 'Harness.c', directory / 'ir-tests'
            run('lake', 'env', 'lean', f'--root={directory}', '-c', str(c_file), str(harness))
            run('lake', 'env', 'leanc', str(c_file),
                '.lake/build/ir/tests/StructuralNative.c.o.export',
                '.lake/build/ir/ClaferCompiler/IR/Structural.c.o.export', '-o', str(binary))
            result = run(str(binary))
            self.assertEqual(result.stderr, '')
            self.assertIn('28 admission cases;', result.stdout)
            self.assertIn('bag identities passed', result.stdout)
