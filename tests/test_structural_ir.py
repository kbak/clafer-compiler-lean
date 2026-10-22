"""Link and execute native IR tests without changing the production CLI."""
import unittest

from native import run_native


# [utest->req~compiler-ir~1]
class StructuralIRTest(unittest.TestCase):
    def test_linked_ir_fixtures(self):
        modules = ['tests.StructuralNative', 'ClaferCompiler.IR.Structural']
        result = run_native(self, modules, 'tests.StructuralNative',
                            'ClaferCompiler.Tests.Structural.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('28 admission cases;', result.stdout)
        self.assertIn('bag identities passed', result.stdout)
