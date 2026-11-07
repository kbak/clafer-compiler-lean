"""Exercise executable reductions independently of upstream/proof imports."""
import unittest
from native import run_native


# [utest->req~compiler-behavioral-elaboration~1]
class BehavioralSurfaceTests(unittest.TestCase):
    def test_surface_reductions(self):
        result = run_native(self, [
            'ClaferCompiler.IR.Structural', 'ClaferCompiler.IR.Behavioral.Syntax',
            'ClaferCompiler.IR.Behavioral.Surface', 'tests.BehavioralSurfaceNative'],
            'tests.BehavioralSurfaceNative', 'ClaferCompiler.Tests.BehavioralSurface.run')
        self.assertEqual(result.stderr, '')
        self.assertIn('behavioral pattern, chain and modifier reductions passed', result.stdout)
