"""Authored source-to-request integration through the native runtime closure."""
import unittest
from native import run_native


# [utest->req~compiler-behavioral-elaboration~1]
class BehavioralElaborationTests(unittest.TestCase):
    def test_source_requests(self):
        result = run_native(self, [
            'ClaferCompiler.IR.Structural',
            'ClaferCompiler.Frontend.Surface',
            'ClaferCompiler.Frontend.Lexer',
            'ClaferCompiler.Frontend.Parser',
            'ClaferCompiler.Frontend.Behavioral.Surface',
            'ClaferCompiler.Frontend.Defaults',
            'ClaferCompiler.IR.BehavioralStructural',
            'ClaferCompiler.Frontend.Behavioral.Parser',
            'ClaferCompiler.Frontend.Resolve', 'ClaferCompiler.IR.StructuralNormalization',
            'ClaferCompiler.IR.Behavioral.Syntax',
            'ClaferCompiler.IR.Expr',
            'ClaferCompiler.IR.ExprBounds',
            'ClaferCompiler.IR.ExprObservation',
            'ClaferCompiler.IR.BehavioralArithmetic',
            'ClaferCompiler.IR.Behavioral.Primitive',
            'ClaferCompiler.IR.Behavioral.Grouped',
            'ClaferCompiler.IR.Behavioral.Binders',
            'ClaferCompiler.IR.Behavioral.Expression',
            'ClaferCompiler.IR.Behavioral.RangeRules',
            'ClaferCompiler.IR.Behavioral.Ranges',
            'ClaferCompiler.Frontend.Behavioral.Binders',
            'ClaferCompiler.Frontend.ConstraintsSupport',
            'ClaferCompiler.Frontend.ConstraintsRules',
            'ClaferCompiler.IR.BehavioralSupport',
            'ClaferCompiler.IR.Behavioral.Surface',
            'ClaferCompiler.Frontend.Behavioral.ValueCore',
            'ClaferCompiler.Frontend.Behavioral.Values',
            'ClaferCompiler.Frontend.Behavioral.NameRules',
            'ClaferCompiler.Frontend.Behavioral.Names',
            'ClaferCompiler.Frontend.Behavioral.ValueRules',
            'ClaferCompiler.Frontend.Behavioral.BinaryRules',
            'ClaferCompiler.Frontend.Behavioral.ConditionalRules',
            'ClaferCompiler.Frontend.Behavioral.Traversal',
            'ClaferCompiler.Frontend.Behavioral.ExpressionCore',
            'ClaferCompiler.Frontend.Behavioral.Operations',
            'ClaferCompiler.Frontend.Behavioral.ExpressionRules',
            'ClaferCompiler.Frontend.Behavioral.Expressions',
            'ClaferCompiler.Frontend.BehavioralResolution',
            'ClaferCompiler.Frontend.BehavioralDeclarations',
            'ClaferCompiler.Frontend.Behavioral.Declarations',
            'ClaferCompiler.IR.Behavioral.Modifiers',
            'ClaferCompiler.Frontend.Behavioral.Modifiers',
            'ClaferCompiler.Frontend.Behavioral.Headers',
            'ClaferCompiler.IR.Behavioral.Properties',
            'ClaferCompiler.Frontend.Behavioral.Elaborate',
            'tests.BehavioralElaborationNative',
        ], 'tests.BehavioralElaborationNative',
            'ClaferCompiler.Tests.BehavioralElaboration.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('behavioral source expressions, captures, arithmetic, surfaces and requests passed', result.stdout)
