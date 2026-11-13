"""Grouped authored-variable plans and native lowering, without proof imports."""
import unittest
from native import run_native


# [utest->req~compiler-behavioral-elaboration~1]
class BehavioralBinderTests(unittest.TestCase):
    def test_captures(self):
        result = run_native(self, [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.IR.Expr',
            'ClaferCompiler.IR.ExprBounds', 'ClaferCompiler.IR.ExprObservation',
            'ClaferCompiler.IR.BehavioralArithmetic',
            'ClaferCompiler.IR.Behavioral.Syntax',
            'ClaferCompiler.IR.Behavioral.Primitive',
            'ClaferCompiler.IR.Behavioral.Grouped',
            'ClaferCompiler.IR.Behavioral.Binders',
            'ClaferCompiler.Frontend.Surface', 'ClaferCompiler.Frontend.Defaults',
            'ClaferCompiler.Frontend.BehavioralLookup', 'ClaferCompiler.Frontend.Resolve', 'ClaferCompiler.IR.StructuralNormalization',
            'ClaferCompiler.Frontend.Behavioral.Surface',
            'ClaferCompiler.Frontend.Behavioral.Binders',
            'tests.BehavioralBindersNative'],
            'tests.BehavioralBindersNative',
            'ClaferCompiler.Tests.BehavioralBinders.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('behavioral binder captures, disjoint domains and tuple counting passed', result.stdout)
