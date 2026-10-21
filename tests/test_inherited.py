"""Execute the complete structural inventory through the native inherited API."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-inherited-realization~1]
class InheritedTests(unittest.TestCase):
    def test_native_appendix6(self):
        modules = [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.IR.Inherited',
            'ClaferCompiler.Backend.Alloy.Syntax', 'ClaferCompiler.Backend.Alloy.Bounds',
            'ClaferCompiler.Backend.Alloy.Semantics', 'ClaferCompiler.Backend.Alloy.Structural',
            'ClaferCompiler.Backend.Alloy.StructuralRepresentation',
            'ClaferCompiler.Backend.Alloy.Inherited', 'ClaferCompiler.Backend.Alloy.InheritedViews',
            'tests.InheritedNative',
        ]

        def run(*args):
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result

        run('lake', 'build', *(f'+{m}:c.o' for m in modules))
        with tempfile.TemporaryDirectory(prefix='clafer-inherited-native-') as tmp:
            directory = Path(tmp)
            harness = directory / 'Harness.lean'
            harness.write_text('import tests.InheritedNative\n'
                               'def main : IO Unit := ClaferCompiler.Tests.InheritedNative.run\n')
            c_file, binary = directory / 'Harness.c', directory / 'inherited-tests'
            run('lake', 'env', 'lean', f'--root={directory}', '-c', str(c_file), str(harness))
            objects = [f'.lake/build/ir/{m.replace(".", "/")}.c.o.export' for m in modules]
            run('lake', 'env', 'leanc', str(c_file), *objects, '-o', str(binary))
            result = run(str(binary))
            self.assertEqual(result.stderr, '')
            self.assertIn('28 declarations, 7 super edges, 5 families, 3 xor groups;', result.stdout)
            self.assertIn('4 candidates, context identity, 5 admission mutations', result.stdout)
