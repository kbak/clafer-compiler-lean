"""Execute the expression checker natively, independently of proof-only imports."""
import unittest

from native import run_native


# [utest->req~compiler-expressions~1]
# [utest->req~compiler-arithmetic~1]
class ExpressionsTest(unittest.TestCase):
    def test_native_expressions(self):
        modules = ['tests.ExprNative', 'ClaferCompiler.IR.Structural',
                   'ClaferCompiler.IR.Expr', 'ClaferCompiler.IR.ExprBounds',
                   'ClaferCompiler.IR.ExprObservation']
        result = run_native(self, modules, 'tests.ExprNative',
                            'ClaferCompiler.Tests.Expressions.run')
        self.assertEqual(result.stderr, '')
        self.assertEqual(result.stdout.strip(),
                         '41 expression cases; 882 arithmetic boundaries; 360 extraction interval boundaries; extraction and observations passed')
