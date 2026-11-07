"""Exercise partial syntax and normalization using native compiler modules."""
import unittest
from native import run_native


# [utest->req~compiler-behavioral-elaboration~1]
class BehavioralPrimitiveTests(unittest.TestCase):
    def test_normalization(self):
        result = run_native(self, [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.IR.Expr',
            'ClaferCompiler.IR.ExprBounds', 'ClaferCompiler.IR.ExprObservation',
            'ClaferCompiler.IR.BehavioralArithmetic', 'ClaferCompiler.IR.Behavioral.Syntax',
            'ClaferCompiler.IR.Behavioral.Surface', 'ClaferCompiler.IR.Behavioral.Primitive',
            'ClaferCompiler.IR.Behavioral.Grouped', 'tests.BehavioralPrimitiveNative'],
            'tests.BehavioralPrimitiveNative', 'ClaferCompiler.Tests.BehavioralPrimitive.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('partial formulas and grouped counting barriers passed', result.stdout)
