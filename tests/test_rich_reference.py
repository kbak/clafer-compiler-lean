"""Fresh fixed points from the immutable Haskell rich/core candidate."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts/oracles'))
import rich
import test_rich_core as explicit


# [utest->req~compiler-rich-core-explicit~1]
class RichReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.binary = rich.load_tools(os.environ['CLAFER_RICH_TOOLS'])
        cls.output = Path(tempfile.mkdtemp(prefix='rich-reference-', dir=os.environ.get('CLAFER_ORACLE_EVIDENCE')))

    def test_explicit_fixed_points_and_core_erasure(self):
        models = [
            'enum E = a | b\nP\n  r -> E ? := a\n',
            'P\n  q ?\n  r -> int ? := if once some q then 1 else 0\n',
            'P ?\nQ ?\nR ?\n[never some P between some Q and some R]\n',
            'P ?\nQ ?\n[some P --> some Q]\n',
            'P ?\n[initially F (previous (previous some P))]\n',
        ]
        for i, source in enumerate(models):
            with self.subTest(model=i):
                rich_text = rich.capture(self.binary, self.output/f'{i}-rich', source)
                core = rich.capture(self.binary, self.output/f'{i}-core', source, core=True)
                self.assertEqual(rich.capture(self.binary, self.output/f'{i}-rich-again', rich_text), rich_text)
                self.assertEqual(rich.capture(self.binary, self.output/f'{i}-core-again', core, core=True), core)
                lowered = rich.capture(self.binary, self.output/f'{i}-lower-rich', rich_text, core=True)
                if i == 2:
                    # The candidate prints absence differently after rich replay:
                    # counts are natural, so !(#x >= 1) and #x = 0 agree.
                    self.assertNotEqual(lowered, core)
                    normalized = lowered.replace('(!((#R) >= 1))', '((#R) = 0)').replace('(!((#P) >= 1))', '((#P) = 0)')
                    self.assertEqual(normalized, core)
                else:
                    self.assertEqual(lowered, core)
                self.assertNotIn(':=', core)
                self.assertNotIn('never ', core)
                self.assertNotIn('-->', core)
                compiler = explicit.ExplicitTests()
                compiler.setUp()
                self.addCleanup(compiler.doCleanups)
                for selected, text in [('rich', rich_text), ('core', core)]:
                    # Lean takes bounds/profile separately and deliberately rejects
                    # Haskell option directives. This fixture adapter recognizes
                    # only the exact explicit/trace flags used in this corpus.
                    header, body = text.split('\n', 1)
                    self.assertIn(header, ('//# OPTIONS --explicit', '//# OPTIONS --explicit --tl=10'))
                    rejected = compiler.call(text, [6,4,4,3,2][i])
                    self.assertEqual(rejected.returncode, 3)
                    self.assertEqual(json.loads(rejected.stderr)['code'], 'lexer.directive')
                    imported = compiler.ok(body, [6,4,4,3,2][i], narrow=True)
                    self.assertEqual(compiler.ok(imported.stdout.decode(), [6,4,4,3,2][i], explicit=True, narrow=True).stdout,
                                     imported.stdout)
                    encoded = rich.capture(self.binary, self.output/f'{i}-{selected}-json', text,
                                           core=(selected == 'core'), mode='json')
                    self.assertIsInstance(json.loads(encoded), dict)


if __name__ == '__main__': unittest.main()
