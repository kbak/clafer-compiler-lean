"""Characterize current lookup separately from the candidate 0.5.8 disposition.

The fixtures deliberately retain unsupported/error cases. Updating these assertions
to the reviewed candidate belongs to the separately selected compatibility task.
External 0.5.8 captures are review evidence, not an adopted CI oracle profile.
"""
import json
from pathlib import Path
import unittest

from native import run_native

FIXTURES = Path(__file__).resolve().parent / 'fixtures/super-lookup'
MODULES = [
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
    'tests.SuperLookupNative',
]


# [utest->req~compiler-resolution~1]
# [utest->req~compiler-behavioral-structural-bridge~1]
# [utest->req~compiler-behavioral-frontend~1]
class SuperLookupTests(unittest.TestCase):
    def test_current_profile_matrix(self):
        expected = json.loads((FIXTURES / 'current.json').read_text())
        self.assertEqual(set(expected), {p.name for p in FIXTURES.glob('*.cfr')})
        result = run_native(self, MODULES, 'tests.SuperLookupNative',
                            'ClaferCompiler.Tests.SuperLookup.run')
        self.assertEqual(result.stderr, '')
        actual = {}
        for line in result.stdout.splitlines():
            name, static, behavioral = line.split('\t')
            self.assertNotIn(name, actual)
            actual[name] = {'static': static, 'behavioral': behavioral}
        self.assertEqual(actual, expected)
