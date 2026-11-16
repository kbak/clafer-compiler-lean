"""Production CLI round trips and independent past-history boundary witnesses."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/comparison'))
from behavioral_observation import Observation, Undefined, ordinary
from test_behavioral_source_cli import bounds
EXE = ROOT / '.lake/build/bin/clafer-compiler'
PROFILE = 'behavioral-rich-core/1'


# [utest->req~compiler-rich-core-explicit~1]
# [utest->req~compiler-past-operators~1]
class ExplicitTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)

    def call(self, text, count, format='core-json', explicit=False, profile=PROFILE, extra=(), narrow=False):
        source = self.work / ('explicit.json' if explicit else 'model.cfr')
        source.write_text(text)
        b = bounds(count, objects=4, width=6, high=3, steps=4)
        b['profile'] = profile
        if narrow:
            b['bitwidth'] = 4
            b['integers']['upper'] = 1
            for row in b['declarations']: row['size'] = 1
        (self.work / 'bounds.json').write_text(json.dumps(b))
        return subprocess.run([str(EXE), 'compile-behavioral-explicit' if explicit else 'compile-behavioral-source',
            source.name, '--bounds', 'bounds.json', '--output', '-', '--format', format,
            '--diagnostics', 'json', *extra], cwd=self.work, capture_output=True, timeout=60)

    def ok(self, *args, **kwargs):
        result = self.call(*args, **kwargs)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return result

    def test_all_past_source_operators_and_profile_isolation(self):
        for expression in ['previous some A', 'once some A', 'historically some A',
                           'some A since no A', 'some A triggered no A',
                           '! (previous some A)', 'F (previous (previous some A))']:
            source = f'P\n  A ?\n  [{expression}]\n'
            self.ok(source, 3)
            result = self.call(source, 3, profile='behavioral-0.5.8/v2')
            self.assertIn(result.returncode, (2, 3))
            self.assertEqual(result.stdout, b'')

    def test_old_profile_past_spellings_remain_identifiers(self):
        for word in ['previous', 'once', 'historically', 'since', 'triggered']:
            source = f'P\n  {word} ?\n  [some {word}]\n'
            self.ok(source, 3, 'json', profile='behavioral-0.5.8/v2')
            explicit = self.call(source, 3, profile='behavioral-0.5.8/v2')
            self.assertEqual(explicit.returncode, 3)
            self.assertEqual(json.loads(explicit.stderr)['code'], 'behavioral.profile')
            rejected = self.call(source, 3)
            self.assertNotEqual(rejected.returncode, 0)

    def test_fixed_points_and_same_target(self):
        cases = [
            ('P\n  A ?\n  [F (previous (previous some A))]\n', 3),
            ('enum Mode = Off | On\nP\n  q ?\n  r -> int ? := if once some q then 1 else 0\n'
             '  [never some r between some q and no q]\n  [some q --> some r]\n', 7),
            ('P\n  A *\n  [all x : A | let y = x in (once (x = y))]\n', 3),
            ('P\n  r -> int ? = if previous some this then 0 else 1\n  assert [r = 0]\n', 3),
        ]
        for source, count in cases:
            with self.subTest(source=source):
                target = self.ok(source, count, 'alloy').stdout
                core = self.ok(source, count, 'core-json').stdout
                rich = self.ok(source, count, 'rich-json').stdout
                self.assertEqual(self.ok(core.decode(), count, explicit=True).stdout, core)
                self.assertEqual(self.ok(rich.decode(), count, 'rich-json', explicit=True).stdout, rich)
                self.assertEqual(self.ok(rich.decode(), count, explicit=True).stdout, core)
                for form in (rich, core):
                    self.assertEqual(self.ok(form.decode(), count, 'alloy', explicit=True).stdout, target)
                pretty = self.ok(core.decode(), count, 'core', explicit=True).stdout
                self.assertEqual(self.ok(pretty.decode(), count, 'core', explicit=True).stdout, pretty)

    def test_rich_intent_clocks_and_stale_annotations(self):
        source = ('enum E = a | b\nabstract P\n  r -> int := 1\n'
                  'p : P\n  [never some r after some r]\n')
        rich = json.loads(self.ok(source, 7, 'rich-json').stdout)
        self.assertEqual(rich['enumerations'][0]['family']['name'], 'E')
        init = next(h for h in rich['headers'] if h['kind'] == 'initializer')
        self.assertEqual(init['clock'], 'instance-birth')
        self.assertEqual(rich['properties'][0]['expression']['operation'][:2], ['pattern', 'never'])
        for edit in [lambda x: x['headers'][0].update(clock='parent-birth'),
                     lambda x: x['lowered']['constraints'][0].update(body=['truth']),
                     lambda x: x['enumerations'][0]['family'].update(id=999)]:
            mutated = copy.deepcopy(rich)
            edit(mutated)
            result = self.call(json.dumps(mutated), 7, 'rich-json', explicit=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('differs from resolved source', result.stderr.decode())

    def test_closed_core_and_no_invented_rich_intent(self):
        core = json.loads(self.ok('P\n  A ?\n  [once some A]\n', 3).stdout)
        bad = copy.deepcopy(core)
        bad['constraints'][0]['body'] = ['atom', ['primitive', ['inhabited', ['set', ['var', 0]]]]]
        result = self.call(json.dumps(bad), 3, explicit=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('lexical index', result.stderr.decode())
        bad = copy.deepcopy(core)
        bad['unknown'] = True
        self.assertEqual(self.call(json.dumps(bad), 3, explicit=True).returncode, 2)
        result = self.call(json.dumps(core), 3, 'rich-json', explicit=True)
        self.assertEqual(result.returncode, 3)
        self.assertEqual(json.loads(result.stderr)['code'], 'explicit.intent-unavailable')

    def test_warning_does_not_reject_conflicting_model(self):
        result = self.ok('P\n  r -> int ? := 1 ++ 2\n', 3, 'rich-json')
        warning = json.loads(result.stderr)
        self.assertEqual(warning['code'], 'behavioral.initializer-multiple-literals')
        rich = json.loads(result.stdout)
        self.assertEqual(rich['warnings'], [warning])
        core = self.ok(result.stdout.decode(), 3, 'core-json', explicit=True)
        self.assertEqual(json.loads(core.stdout)['warnings'], [warning])
        self.assertEqual(self.ok(core.stdout.decode(), 3, explicit=True).stderr, result.stderr)
        duplicate = self.ok('P\n  r -> int ? := 1 ++ 1\n', 3)
        self.assertEqual(duplicate.stderr, b'')
        collection = self.ok('P\n  rs ->> int 2 := 1 ++ 2\n', 3)
        self.assertEqual(collection.stderr, b'')


# [utest->req~compiler-past-operators~1]
class PastObservationTests(unittest.TestCase):
    def observer(self, formula, frames=None, loop=0):
        compiled = dict(declarations=[dict(id=0, primitive=False, super=None),
            dict(id=1, primitive=True, super=None)], resolved=dict(constraints=[dict(body=formula)]))
        candidate = dict(root=0, loop=loop, identities=[dict(id=0, parent=None, type=0),
            dict(id=1, parent=0, type=0), dict(id=2, parent=1, type=0)],
            frames=frames or [dict(live=[0,1,2], references=[], values=[])])
        return Observation(compiled, candidate)

    def test_nested_previous_same_frame_and_mixed_future(self):
        f = ['truth']
        for _ in range(12): f = ['previous', f]
        obs = self.observer(['eventually', f])
        self.assertFalse(obs.checked(f, ordinary(2), [], 11))
        self.assertTrue(obs.checked(f, ordinary(2), [], 12))
        self.assertTrue(obs.checked(['eventually', f], ordinary(2), [], 0))
        self.assertFalse(obs.checked(['always', ['not', f]], ordinary(2), [], 0))
        # The old (current frame, predecessor frame) key would stop at t=2.
        self.assertGreater(max(obs.orbit(0)), 12)

    def test_parent_history_precedes_child_and_resets(self):
        def frame(live): return dict(live=live, references=[], values=[])
        obs = self.observer(['once', ['truth']], [frame([0,1]), frame([0,1,2]),
            frame([0]), frame([0,1,2])], 3)
        self.assertTrue(obs.checked(['previous', ['truth']], ordinary(2), [], 1))
        self.assertFalse(obs.checked(['previous', ['truth']], ordinary(2), [], 3))
        self.assertTrue(obs.checked(['weakPrevious', ['truth']], ordinary(2), [], 3))
        self.assertFalse(obs.checked(['once', ['truth']], ordinary(2), [], 2))
        self.assertTrue(obs.checked(['historically', ['truth']], ordinary(2), [], 2))

    def test_strict_domains_only_demand_available_history(self):
        undefined = ['atom', ['primitive', ['integerEqual',
            ['binary', 'divide', ['literal', 1], ['literal', 0]], ['literal', 0]]]]
        obs = self.observer(['previous', undefined])
        self.assertFalse(obs.checked(['previous', undefined], ordinary(2), [], 0))
        self.assertTrue(obs.checked(['weakPrevious', undefined], ordinary(2), [], 0))
        with self.assertRaises(Undefined): obs.checked(['previous', undefined], ordinary(2), [], 1)
        with self.assertRaises(Undefined): obs.checked(['once', undefined], ordinary(2), [], 0)

    def test_since_endpoints_and_signed_duals(self):
        q = ['atom', ['primitive', ['inhabited', ['set', ['this']]]]]
        f = ['since', ['truth'], q]
        frames = [dict(live=live, references=[], values=[]) for live in ([0,1,2], [0,1], [0], [0,1])]
        obs = self.observer(f, frames, 3)
        self.assertEqual([obs.checked(f, ordinary(2), [], t) for t in range(5)],
                         [True, True, False, False, False])
        for t in range(8):
            self.assertEqual(obs.truth(['not', f], ordinary(2), [], t),
                             obs.truth(['triggered', ['not', ['truth']], ['not', q]], ordinary(2), [], t))


if __name__ == '__main__':
    unittest.main()
