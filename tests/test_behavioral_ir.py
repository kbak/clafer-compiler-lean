"""Run the first behavioral IR slice without proof-only runtime imports."""
import unittest

from native import run_native


class BehavioralIRTest(unittest.TestCase):
    # [utest->req~compiler-behavioral-ir~1]
    # [utest->req~compiler-behavioral-interpretation~1]
    def test_native_behavioral_ir(self):
        modules = ['ClaferCompiler.IR.Structural',
                   'ClaferCompiler.IR.Behavioral.Syntax',
                   'ClaferCompiler.IR.Behavioral.Admission',
                   'ClaferCompiler.IR.Behavioral.Trace',
                   'ClaferCompiler.IR.Behavioral', 'tests.BehavioralNative']
        result = run_native(self, modules, 'tests.BehavioralNative',
                            'ClaferCompiler.Tests.Behavioral.run')
        self.assertEqual(result.stderr, '')
        self.assertEqual(result.stdout.strip(),
                         'behavioral admission, trace identities, observations and signed normalization passed')
