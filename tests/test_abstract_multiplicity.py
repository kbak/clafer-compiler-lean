"""Native admission, provenance and metadata-free core replay for #144."""
import copy
import json
import unittest

import test_rich_core as explicit
from behavioral_abstract_multiplicity_cases import PROFILE, aggregate_cases
from behavioral_observation import Observation


# Reuse the CLI fixture methods without inheriting its unrelated test cases.
# [utest->req~compiler-abstract-multiplicity~1]
# [utest->req~compiler-rich-core-explicit~1]
class AbstractMultiplicityTests(unittest.TestCase):
    setUp = explicit.ExplicitTests.setUp
    def call(self, *args, **kwargs):
        # CLI/provenance checks need only small conservative scopes; the exact
        # comparison suite supplies each candidate's actual identity scopes.
        kwargs.setdefault('narrow', True)
        return explicit.ExplicitTests.call(self, *args, **kwargs)
    ok = explicit.ExplicitTests.ok

    def test_independent_source_boundary_matrix(self):
        for name, expected, candidate in aggregate_cases():
            with self.subTest(name=name):
                # This helper supplies conservative, non-exact scopes. Exact
                # fixture scopes are checked separately by the Analyzer corpus.
                count = len(candidate['bounds']['declarations'])
                output = self.ok(candidate['source'], count, 'json', profile=PROFILE)
                compiled = json.loads(output.stdout)
                observed = Observation(compiled, candidate['candidate'])
                self.assertEqual(observed.check()['status'], expected)

    def test_rich_core_round_trips_and_erased_metadata(self):
        sources = [('abstract A 1..2\na : A *\n', 3),
                   ('abstract Base\n  abstract A ?\nP : Base\n  a : Base.A *\n', 5)]
        for source, count in sources:
            rich = self.ok(source, count, 'rich-json', profile=PROFILE).stdout
            core = self.ok(source, count, 'core-json', profile=PROFILE).stdout
            target = self.ok(source, count, 'alloy', profile=PROFILE).stdout
            self.assertEqual(self.ok(rich.decode(), count, 'rich-json', explicit=True, profile=PROFILE).stdout, rich)
            self.assertEqual(self.ok(rich.decode(), count, explicit=True, profile=PROFILE).stdout, core)
            self.assertEqual(self.ok(core.decode(), count, explicit=True, profile=PROFILE).stdout, core)
            for form in (rich, core):
                self.assertEqual(self.ok(form.decode(), count, 'alloy', explicit=True, profile=PROFILE).stdout, target)
            erased = json.loads(core)
            for row in erased['structure']['declarations']:
                row['authored'] = None
            self.assertEqual(self.ok(json.dumps(erased), count, 'alloy', explicit=True, profile=PROFILE).stdout, target)
            mutated = json.loads(rich)
            mutated['lowered']['constraints'] = []
            self.assertEqual(self.call(json.dumps(mutated), count, explicit=True, profile=PROFILE).returncode, 2)

    def test_authored_omission_effective_and_optimizer_bounds(self):
        for spelling, authored in [('', None), ('*', dict(lower=0, upper='*')), ('0', dict(lower=0, upper=0))]:
            core = json.loads(self.ok(f'abstract A {spelling}\na : A *\n', 3, profile=PROFILE).stdout)
            abstract = core['structure']['declarations'][1]
            self.assertEqual(abstract['authored']['localBounds'], authored)
            self.assertEqual(abstract['localBounds'], dict(lower=0, upper='*'))
            target = self.ok(json.dumps(core), 3, 'alloy', explicit=True, profile=PROFILE).stdout
            # An optimizer may zero a parentless effective slot. It cannot erase
            # the independently retained authored cardinality constraint.
            abstract['localBounds'] = dict(lower=0, upper=0)
            replay = self.ok(json.dumps(core), 3, 'alloy', explicit=True, profile=PROFILE).stdout
            self.assertEqual(replay, target)

    def test_clock_and_profile_boundaries(self):
        for bound in ('0', '?', '1', '1..2', '1..*'):
            result = self.call(f'abstract A -> int {bound} := 1\na : A *\n', 3, profile=PROFILE)
            self.assertEqual(result.returncode, 3)
            self.assertEqual(json.loads(result.stderr)['code'], 'behavioral.initializer-parentless-multiplicity')
        source = 'abstract A 2\na : A *\n'
        extended = json.loads(self.ok(source, 3, profile=PROFILE).stdout)
        historical = json.loads(self.ok(source, 3).stdout)
        self.assertEqual(len(extended['constraints']), 1)
        self.assertEqual(historical['constraints'], [])
        self.assertEqual(self.call(json.dumps(extended), 3, explicit=True).returncode, 3)
        self.assertNotEqual(self.call('abstract A 3..1\n', 2, profile=PROFILE).returncode, 0)

    def test_unsafe_aggregate_count_range_is_diagnostic(self):
        result = self.call('abstract A 8\na : A *\n', 3, profile=PROFILE, narrow=True)
        self.assertEqual(result.returncode, 3)
        self.assertEqual(result.stdout, b'')
        # The authored endpoints fit three bits, but the independently supplied
        # identity budget allows four heads and therefore cannot fit that width.
        result = self.call('abstract A ?\na : A *\n', 3, profile=PROFILE,
                           narrow=False, extra=('--bitwidth', '3'))
        self.assertEqual(result.returncode, 3)
        self.assertEqual(result.stdout, b'')
