"""Execute the expression checker natively, independently of proof-only imports."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-expressions~1]
# [utest->req~compiler-arithmetic~1]
class ExpressionsTest(unittest.TestCase):
    def test_native_expressions(self):
        def run(*args):
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result

        modules = ['tests.ExprNative', 'ClaferCompiler.IR.Structural',
                   'ClaferCompiler.IR.Expr', 'ClaferCompiler.IR.ExprBounds',
                   'ClaferCompiler.IR.ExprObservation']
        run('lake', 'build', *(f'+{module}:c.o' for module in modules))
        with tempfile.TemporaryDirectory(prefix='clafer-expr-native-') as tmp:
            directory = Path(tmp)
            harness = directory / 'Harness.lean'
            harness.write_text('import tests.ExprNative\n'
                               'def main : IO Unit := ClaferCompiler.Tests.Expressions.run\n')
            c_file, binary = directory / 'Harness.c', directory / 'expression-tests'
            run('lake', 'env', 'lean', f'--root={directory}', '-c', str(c_file), str(harness))
            run('lake', 'env', 'leanc', str(c_file),
                *(f'.lake/build/ir/{module.replace(".", "/")}.c.o.export' for module in modules),
                '-o', str(binary))
            result = run(str(binary))
            self.assertEqual(result.stderr, '')
            self.assertEqual(result.stdout.strip(),
                             '41 expression cases; 882 arithmetic boundaries; extraction and observations passed')
