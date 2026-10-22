"""Exercise the linked native representation API, including rejecting inputs."""
import unittest

from native import run_native


# [utest->req~compiler-structural-representation~1]
class StructuralRepresentationTests(unittest.TestCase):
    def test_native_representation(self):
        modules = [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.Backend.Alloy.Syntax',
            'ClaferCompiler.Backend.Alloy.Bounds', 'ClaferCompiler.Backend.Alloy.Semantics',
            'ClaferCompiler.Backend.Alloy.Structural',
            'ClaferCompiler.Backend.Alloy.StructuralRepresentation',
            'tests.StructuralNative', 'tests.StructuralAlloyNative',
            'tests.StructuralRepresentationNative',
        ]

        result = run_native(self, modules, 'tests.StructuralRepresentationNative',
                            'ClaferCompiler.Tests.StructuralRepresentationNative.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('72 corpus round trips; 1 dangling-tuple round trip; 2 distinct bag occurrences; '
                      '9 rejecting decoder cases', result.stdout)
