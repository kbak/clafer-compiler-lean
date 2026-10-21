"""Exercise the linked native representation API, including rejecting inputs."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-structural-representation~1]
class StructuralRepresentationTests(unittest.TestCase):
    def test_native_representation(self):
        modules = [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.Backend.Alloy.Syntax',
            'ClaferCompiler.Backend.Alloy.Bounds', 'ClaferCompiler.Backend.Alloy.Semantics',
            'ClaferCompiler.Backend.Alloy.Structural',
            'ClaferCompiler.Backend.Alloy.StructuralRepresentation',
            'tests.StructuralNative', 'tests.StructuralAlloyNative',
            'tests.StructuralRepresentationNative',
        ]

        def run(*args):
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result

        run('lake', 'build', *(f'+{module}:c.o' for module in modules))
        with tempfile.TemporaryDirectory(prefix='clafer-representation-') as tmp:
            directory = Path(tmp)
            harness = directory / 'Harness.lean'
            harness.write_text('import tests.StructuralRepresentationNative\n'
                               'def main : IO Unit := '
                               'ClaferCompiler.Tests.StructuralRepresentationNative.run\n')
            c_file, binary = directory / 'Harness.c', directory / 'representation-tests'
            run('lake', 'env', 'lean', f'--root={directory}', '-c', str(c_file), str(harness))
            objects = [f'.lake/build/ir/{module.replace(".", "/")}.c.o.export' for module in modules]
            run('lake', 'env', 'leanc', str(c_file), *objects, '-o', str(binary))
            result = run(str(binary))
            self.assertEqual(result.stderr, '')
            self.assertIn('72 corpus round trips; 1 dangling-tuple round trip; 2 distinct bag occurrences; '
                          '9 rejecting decoder cases', result.stdout)
