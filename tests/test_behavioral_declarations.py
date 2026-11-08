"""Source-to-declaration integration without semantics/proof runtime imports."""
import unittest
from native import run_native


# [utest->req~compiler-behavioral-elaboration~1]
class BehavioralDeclarationsTests(unittest.TestCase):
    def test_binding(self):
        result = run_native(self, [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.Frontend.Surface',
            'ClaferCompiler.Frontend.Defaults', 'ClaferCompiler.Frontend.Resolve',
            'ClaferCompiler.IR.StructuralNormalization',
            'ClaferCompiler.IR.BehavioralStructural',
            'ClaferCompiler.Frontend.BehavioralResolution',
            'ClaferCompiler.Frontend.BehavioralDeclarations',
            'ClaferCompiler.Frontend.Lexer', 'ClaferCompiler.Frontend.Parser',
            'ClaferCompiler.IR.Behavioral.Syntax', 'ClaferCompiler.IR.Behavioral.Surface',
            'ClaferCompiler.IR.Behavioral.Modifiers',
            'ClaferCompiler.Frontend.Behavioral.Surface',
            'ClaferCompiler.Frontend.Behavioral.Parser',
            'ClaferCompiler.Frontend.Behavioral.Declarations',
            'ClaferCompiler.Frontend.Behavioral.Modifiers',
            'ClaferCompiler.Frontend.Behavioral.Headers',
            'tests.BehavioralDeclarationsNative'],
            'tests.BehavioralDeclarationsNative',
            'ClaferCompiler.Tests.BehavioralDeclarations.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('behavioral declaration, enum, modifier and property binding passed', result.stdout)
