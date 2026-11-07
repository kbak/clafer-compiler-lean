"""Execute the C6 structural handoff independently of the proof import closure."""
import unittest

from native import run_native


# [utest->req~compiler-behavioral-structural-bridge~1]
class BehavioralStructuralTests(unittest.TestCase):
    def test_structural_handoff(self):
        modules = [
            'ClaferCompiler.IR.Structural',
            'ClaferCompiler.Frontend.Surface', 'ClaferCompiler.Frontend.Defaults',
            'ClaferCompiler.Frontend.Lexer', 'ClaferCompiler.Frontend.Parser',
            'ClaferCompiler.Frontend.Resolve',
            'ClaferCompiler.IR.Expr', 'ClaferCompiler.IR.ExprBounds',
            'ClaferCompiler.IR.ExprObservation',
            'ClaferCompiler.IR.BehavioralStructural',
            'ClaferCompiler.Frontend.BehavioralResolution',
            'ClaferCompiler.Frontend.BehavioralDeclarations',
            'ClaferCompiler.IR.BehavioralSupport',
            'ClaferCompiler.IR.BehavioralArithmetic',
            'tests.BehavioralStructuralNative',
        ]
        result = run_native(self, modules, 'tests.BehavioralStructuralNative',
                            'ClaferCompiler.Tests.BehavioralStructural.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('behavioral structural, resolution, support, enums, '
                      'initializers and arithmetic checks passed', result.stdout)
