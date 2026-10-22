"""Execute the complete structural inventory through the native inherited API."""
import unittest

from native import run_native


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

        result = run_native(self, modules, 'tests.InheritedNative',
                            'ClaferCompiler.Tests.InheritedNative.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('28 declarations, 7 super edges, 5 families, 3 xor groups;', result.stdout)
        self.assertIn('4 candidates, context identity, 5 admission mutations', result.stdout)
