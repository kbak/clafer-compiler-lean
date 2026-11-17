"""Finality source/rich/core replay with independent exact target observations."""
from concurrent.futures import ThreadPoolExecutor
import copy
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/comparison'))
import behavioral_source as bs
from behavioral_source_cases import case, features
from test_behavioral_source_comparison import case_workers


class FinalityCoreReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workers=case_workers()
        parent=bs.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output=Path(tempfile.mkdtemp(prefix='finality-core-',dir=parent))
        tools=os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools: raise AssertionError('CLAFER_ORACLE_TOOLS required')
        cls.runtime=bs.Runtime(tools,cls.output/'runtime')
        print(f'Finality core evidence: {cls.output}',flush=True)

    # [utest->req~compiler-rich-core-explicit~1]
    # [utest->req~compiler-full-behavioral-correctness~1]
    # [utest->req~compiler-abstract-multiplicity~1]
    def test_finality_core_exact_replay(self):
        rows = [(n, e, c) for n, _, e, c in features()
                if n.startswith(('modifier-', 'inherited-final', 'inherited-initial'))]
        # A shallow final parent does not freeze its child's changing value.
        rows.append(('shallow-final', 'satisfied', case('final P\n  r -> int\n', 3,
            [(1, 1, 0), (2, 2, 1)], [[1, 2], [1, 2]], values=[{2: 0}, {2: 1}], width=3)))
        rows.append(('enum-final', 'satisfied', case('enum E = a | b\n', 4,
            [(1, 2, 0), (2, 3, 0)], [[1, 2], [1, 2]], width=3, supers={2: 1, 3: 1})))
        # Stable counts do not imply stable identities, and finality cannot
        # replace either endpoint of the independently authored aggregate bound.
        for name, expected, identities, live in (
            ('stable', 'satisfied', [(1, 2, 0)], [[1], [1]]),
            ('swap', 'violated', [(1, 2, 0), (2, 2, 0)], [[1], [2]]),
            ('underflow', 'violated', [], [[], []]),
            ('overflow', 'violated', [(i, 2, 0) for i in range(1, 4)], [[1, 2, 3], [1, 2, 3]])):
            rows.append(('aggregate-final-' + name, expected, case(
                'abstract A 1..2\nfinal a : A *\n', 3, identities, live, supers={2: 1})))
        mutation_names = {'modifier-False-final-swap', 'modifier-False-finaltarget-gap', 'inherited-final-True'}
        def replay(row):
            name, expected, original = row
            c = copy.deepcopy(original)
            c['bounds']['profile'] = c['candidate']['profile'] = (
                'behavioral-abstract-multiplicity/1' if name.startswith('aggregate-final-')
                else 'behavioral-rich-core/1')
            directory = self.output / ('core-finality-' + name.replace(' ', '-'))
            result = self.runtime.compare(c, directory)
            p = bs.temporal.read(directory / 'compilation.json')
            trace = bs.within_bounds(c['candidate'], p, c['bounds'])
            answers = {}
            rich_matches = False
            for form in ('core', 'rich'):
                exported = directory / (form + '.json')
                bs.tc.run([self.runtime.compiler, 'compile-behavioral-source', directory / 'input.cfr',
                    '--bounds', directory / 'bounds.json', '--format', form + '-json',
                    '--output', exported], directory, 'export-' + form)
                target = directory / (form + '.als')
                bs.tc.run([self.runtime.compiler, 'compile-behavioral-explicit', exported,
                    '--bounds', directory / 'bounds.json', '--output', target], directory, 'replay-' + form)
                text = target.read_text()
                if form == 'rich':
                    # Exact target equality transports the already solved source
                    # observation to rich replay, including every pinned bound.
                    rich_matches = text == p['alloy']
                else:
                    answers[form] = self.runtime.solve(directory / (form + '-solver'), text, trace, p)
            mutation = None
            if name in mutation_names:
                core = bs.temporal.read(directory / 'core.json')
                if name == 'inherited-final-True':
                    # Keep the original view but use root survival: this
                    # wrongly enforces equality across the parent's gap.
                    def wrong_lifetime(node):
                        if node == ['this']:
                            return ['root']
                        return [wrong_lifetime(x) for x in node] if isinstance(node, list) else node
                    for constraint in core['constraints']:
                        constraint['body'] = wrong_lifetime(constraint['body'])
                else:
                    # Remove reference stability or target-loss prevention.
                    core['constraints'] = [constraint for constraint in core['constraints']
                        if constraint['owner'] != (1 if name.endswith('swap') else 0)]
                mutated = directory / 'mutated.json'
                bs.oracle.write(mutated, core)
                target = directory / 'mutated.als'
                bs.tc.run([self.runtime.compiler, 'compile-behavioral-explicit', mutated,
                    '--bounds', directory / 'bounds.json', '--output', target], directory, 'mutated')
                mutation = self.runtime.solve(directory / 'mutated-solver', target.read_text(), trace, p)
            return name, expected, result, answers, mutation, rich_matches

        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results = list(pool.map(replay, rows))
        for name, expected, result, answers, mutation, rich_matches in results:
            with self.subTest(name=name):
                self.assertEqual(result, dict(status='complete', source=expected,
                    target='sat' if expected == 'satisfied' else 'bounded_unsat', directions=[]))
                for answer in answers.values():
                    self.assertEqual((answer['status'], answer.get('outcome')), ('ok', result['target']))
                self.assertTrue(rich_matches, 'rich replay changed the source Alloy target')
                if name in mutation_names:
                    self.assertIsNotNone(mutation)
                    self.assertEqual(mutation['status'], 'ok')
                    self.assertNotEqual(mutation['outcome'], result['target'])
