"""Full source requests through the production executable and closed protocols."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/clafer-compiler'
PROFILE = 'behavioral-0.5.7-candidate/v1'


def bounds(count, objects=3, width=4, low=0, high=1, steps=3):
    return dict(version='clafer-behavioral-bounds/2', profile=PROFILE,
                objects=objects, bitwidth=width, minSteps=1, maxSteps=steps,
                declarations=[dict(id=i, size=1 if i == 0 else objects, exact=False)
                              for i in range(count)],
                integers=dict(lower=low, upper=high))


# [utest->req~compiler-behavioral-integration~1]
class BehavioralSourceCLITests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='clafer-behavioral-source-')
        self.addCleanup(directory.cleanup)
        self.work = Path(directory.name)
        self.source = 'P\n  A ?\n  assert [some A]\n'
        self.bounds = bounds(3)

    def call(self, args, data=None):
        return subprocess.run([str(EXE), *args], cwd=self.work, input=data,
                              env={'PATH': '/nonexistent', 'LANG': 'C'},
                              capture_output=True, timeout=30)

    def compile(self, source=None, b=None, extra=(), output='-'):
        (self.work / 'model.cfr').write_text(self.source if source is None else source)
        (self.work / 'bounds.json').write_text(json.dumps(self.bounds if b is None else b))
        return self.call(['compile-behavioral-source', 'model.cfr', '--bounds', 'bounds.json',
                          '--output', output, '--diagnostics', 'json', *extra])

    def product(self, **kwargs):
        result = self.compile(extra=['--format', 'json', *kwargs.pop('extra', ())], **kwargs)
        self.assertEqual((result.returncode, result.stderr), (0, b''))
        return json.loads(result.stdout)

    def test_deterministic_runtime_files_and_streams(self):
        result = self.compile()
        self.assertEqual((result.returncode, result.stderr), (0, b''))
        self.assertIn(b' steps', result.stdout)
        self.assertEqual(self.compile().stdout, result.stdout)
        self.assertNotIn(str(self.work).encode(), result.stdout)
        product = self.product()
        self.assertEqual(product['alloy'].encode(), result.stdout)
        self.assertEqual((product['version'], product['profile']),
                         ('clafer-behavioral-compilation/2', PROFILE))
        self.assertEqual(product['command'], {'kind': 'run'})
        self.assertEqual(len(product['assertions']), 1)
        self.assertEqual(product['constraints'], [])
        self.assertEqual(product['scenario'], [])
        self.assertEqual([d['id'] for d in product['declarations']], [0, 1, 2, 3])
        self.assertTrue(product['declarations'][-1]['primitive'])
        for args, data in [(['-', '--bounds', 'bounds.json'], self.source.encode()),
                           (['model.cfr', '--bounds', '-'], json.dumps(self.bounds).encode())]:
            streamed = self.call(['compile-behavioral-source', *args, '--output', '-'], data)
            self.assertEqual((streamed.returncode, streamed.stdout, streamed.stderr),
                             (0, result.stdout, b''))
        written = self.compile(output='model.als')
        self.assertEqual((written.returncode, written.stdout, written.stderr), (0, b'', b''))
        self.assertEqual((self.work / 'model.als').read_bytes(), result.stdout)

    def test_assertion_and_scenario_selection(self):
        checked = self.product(extra=['--assertion', '0'])
        self.assertEqual(checked['command'], {'kind': 'check', 'assertion': 0})
        self.assertIn('\ncheck {', checked['alloy'])
        self.assertEqual(checked['constraints'], [])
        scenario = '[initially some A]\n'
        (self.work / 'scenario.cfr').write_text(scenario)
        run = self.product(extra=['--scenario', 'scenario.cfr', '--owner', '1'])
        self.assertEqual(run['command'], {'kind': 'run'})
        self.assertEqual(run['scenario'][0]['owner'], 1)
        self.assertEqual(run['scenario'][0]['source']['file'], 'scenario.cfr')
        streamed = self.call(['compile-behavioral-source', 'model.cfr', '--bounds', 'bounds.json',
                              '--output', '-', '--scenario', '-', '--owner', '1'], scenario.encode())
        self.assertEqual((streamed.returncode, streamed.stdout), (0, run['alloy'].encode()))
        for extra, code in [(['--assertion', '1'], 'behavioral.assertion-index'),
                            (['--scenario', 'scenario.cfr', '--owner', '99'], 'behavioral.scenario-owner')]:
            result = self.compile(extra=extra)
            self.assertEqual((result.returncode, result.stdout), (2, b''))
            self.assertEqual(json.loads(result.stderr)['code'], code)

    def test_empty_model_numeric_scenario_and_inherited_references(self):
        (self.work / 'scenario.cfr').write_text('[all x : 0 | some x]\n')
        p = self.product(source='', b=bounds(1, objects=1), extra=['--scenario', 'scenario.cfr'])
        self.assertEqual(p['scenario'][0]['owner'], p['root'])
        source = 'abstract P\n  finalref finaltarget r -> int ?\np : P\n'
        p = self.product(source=source, b=bounds(4))
        names = {d['name']: d for d in p['declarations']}
        self.assertEqual(names['p']['super'], names['P']['id'])
        self.assertEqual(names['r']['referenceOwner'], names['r']['id'])
        self.assertIn(': one Int', p['alloy'])

    def test_closed_bounds_and_safe_ranges(self):
        cases = []
        def case(edit, exit_code):
            b = copy.deepcopy(self.bounds)
            edit(b)
            cases.append((b, exit_code))
        case(lambda b: b.update(version='clafer-behavioral-bounds/1'), 3)
        case(lambda b: b.update(profile='behavioral-core/1'), 3)
        case(lambda b: b.update(unknown=True), 2)
        case(lambda b: b['declarations'].pop(), 2)
        case(lambda b: b['declarations'].append(b['declarations'][0]), 2)
        case(lambda b: b['declarations'][0].update(id=3), 2)
        case(lambda b: b.update(minSteps=0), 2)
        case(lambda b: b.update(minSteps=4), 2)
        case(lambda b: b.update(objects=-1), 2)
        case(lambda b: b['integers'].update(lower=2), 2)
        case(lambda b: b['integers'].update(lower=-1.0), 2)
        case(lambda b: b['integers'].update(lower='-1'), 2)
        case(lambda b: b['integers'].update(lower=-9), 3)
        case(lambda b: b.update(bitwidth=0), 3)
        for b, code in cases:
            with self.subTest(bounds=b):
                result = self.compile(b=b)
                self.assertEqual((result.returncode, result.stdout), (code, b''), result.stderr)
        for raw in ['{"version":"clafer-behavioral-bounds/2","version":"other"}',
                    json.dumps(self.bounds).replace('"objects": 3', '"objects": 3e0')]:
            (self.work / 'bounds.json').write_text(raw)
            result = self.call(['compile-behavioral-source', 'model.cfr', '--bounds', 'bounds.json', '--output', '-'])
            self.assertEqual(result.returncode, 2, result.stderr)

    def test_argument_separation_and_atomic_failures(self):
        for extra in [['--assertion', '0', '--scenario', 'scenario.cfr'], ['--owner', '1'],
                      ['--assertion', '-1'], ['--assertion', '00'], ['--format', 'ir'],
                      ['--scenario', ''], ['--assertion', '0', '--assertion', '0']]:
            result = self.compile(extra=extra)
            self.assertEqual((result.returncode, result.stdout), (2, b''), result.stderr)
            self.assertEqual(json.loads(result.stderr)['code'], 'cli.arguments')
        for command in ['compile-ir', 'compile-source', 'compile-behavioral-ir']:
            result = self.call([command, 'model.cfr', '--bounds', 'bounds.json', '--output', '-', '--assertion', '0'])
            self.assertEqual(result.returncode, 2)
        sentinel = self.work / 'out.als'
        sentinel.write_text('preserve me')
        result = self.compile(source='A := 1\n', output='out.als')
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertEqual(sentinel.read_text(), 'preserve me')
        result = self.compile(extra=['--scenario', 'missing.cfr'], output='out.als')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(sentinel.read_text(), 'preserve me')
        result = self.call(['compile-behavioral-source', '-', '--bounds', '-', '--output', '-'])
        self.assertEqual(result.returncode, 2)
        result = self.call(['compile-behavioral-source', '-', '--bounds', 'bounds.json', '--output', '-', '--scenario', '-'])
        self.assertEqual(result.returncode, 2)

    def test_source_diagnostics_and_scenario_rejections(self):
        source = 'P\r\n  résumé -> int\r\n  [résumé * résumé = 0]\r\n'
        result = self.compile(source=source, b=bounds(3, low=-2, high=2, width=3))
        self.assertEqual(result.returncode, 3, result.stderr)
        diagnostic = json.loads(result.stderr)
        self.assertEqual(diagnostic['primary']['kind'], 'source')
        self.assertEqual(diagnostic['primary']['line'], 3)
        self.assertEqual(diagnostic['primary']['file'], 'model.cfr')
        for source, code, exit_code in [('[assert some A]', None, 2),
                                        ('assert [some A]', 'behavioral.scenario-assertion', 2),
                                        ('B', 'behavioral.scenario-declaration', 3)]:
            (self.work / 'scenario.cfr').write_text(source)
            result = self.compile(extra=['--scenario', 'scenario.cfr', '--owner', '1'])
            self.assertEqual(result.returncode, exit_code, result.stderr)
            if code:
                self.assertEqual(json.loads(result.stderr)['code'], code)
            self.assertEqual(json.loads(result.stderr)['primary']['file'], 'scenario.cfr')

    # [utest->req~compiler-diagnostics~1]
    # [utest->req~compiler-behavioral-elaboration~1]
    def test_literal_empty_navigation_and_warning_locations(self):
        source = 'P\r\n  résumé ?\r\nQ\r\n  résumé ?\r\n[no (noclafer).résumé.missing.parent.dref]\r\n'
        result = self.compile(source=source, b=bounds(5), extra=['--format', 'json'])
        self.assertEqual(result.returncode, 0, result.stderr)
        p = json.loads(result.stdout)
        warnings = [json.loads(line) for line in result.stderr.splitlines()]
        self.assertEqual(len(warnings), 1)
        w = warnings[0]
        self.assertEqual(set(w), {'version', 'severity', 'code', 'phase', 'message', 'operator', 'primary'})
        self.assertEqual((w['version'], w['severity'], w['code'], w['operator']),
                         ('clafer-warning/1', 'warning', 'behavioral.empty-navigation', '.'))
        first = source.index('(noclafer)')
        last = source.index(']', first)
        self.assertEqual(w['primary'], dict(kind='source', file='model.cfr', line=5, column=5,
                         startByte=len(source[:first].encode()), endByte=len(source[:last].encode())))
        direct = self.compile(source=source[:source.index('[no')] + '[no noclafer]\r\n',
                              b=bounds(5), extra=['--format', 'json'])
        self.assertEqual((direct.returncode, direct.stderr), (0, b''))
        self.assertEqual(p['resolved']['constraints'][0]['body'],
                         json.loads(direct.stdout)['resolved']['constraints'][0]['body'])
        self.assertNotIn('warnings', p)

    # [utest->req~compiler-diagnostics~1]
    def test_self_expressions_warn_without_rewriting_or_changing_outputs(self):
        source = 'A ?\n[A = (A)]\n[A != A]\n[no (A -- A)]\n[some (A ** A)]\n'
        result = self.compile(source=source, b=bounds(2), extra=['--format', 'json'])
        self.assertEqual(result.returncode, 0, result.stderr)
        p = json.loads(result.stdout)
        warnings = [json.loads(line) for line in result.stderr.splitlines()]
        self.assertEqual([w['operator'] for w in warnings], ['=', '!=', '--', '**'])
        self.assertEqual([w['primary']['line'] for w in warnings], [2, 3, 4, 5])
        self.assertTrue(all(w['code'] == 'behavioral.redundant-expression' for w in warnings))
        self.assertEqual(self.compile(source=source, b=bounds(2), extra=['--format', 'json']).stderr,
                         result.stderr)
        text = self.call(['compile-behavioral-source', 'model.cfr', '--bounds', 'bounds.json', '--output', '-'])
        self.assertEqual((text.returncode, text.stdout), (0, p['alloy'].encode()))
        self.assertEqual(text.stderr.count(b'warning [behavioral.redundant-expression]'), 4)
        written = self.compile(source=source, b=bounds(2), output='out.als')
        self.assertEqual((written.returncode, written.stdout, written.stderr), (0, b'', result.stderr))
        self.assertEqual((self.work / 'out.als').read_text(), p['alloy'])
        # Different names and different binder bodies must not produce syntactic-identity warnings.
        plain = self.compile(source='A ?\nB ?\n[(some A) = (some B)]\n[(all x : A | some x) = (all y : A | some y)]\n',
                             b=bounds(3))
        self.assertEqual((plain.returncode, plain.stderr), (0, b''))

    # [utest->req~compiler-diagnostics~1]
    def test_warning_authored_inventory_and_scenarios(self):
        source = 'abstract P\n  [this = this]\np : P ?\nassert [no noclafer.missing]\n'
        (self.work / 'scenario.cfr').write_text('[no noclafer.unknown]\n')
        result = self.compile(source=source, b=bounds(3), extra=['--scenario', 'scenario.cfr'])
        self.assertEqual(result.returncode, 0, result.stderr)
        warnings = [json.loads(line) for line in result.stderr.splitlines()]
        self.assertEqual([(w['primary']['file'], w['primary']['line']) for w in warnings],
                         [('model.cfr', 2), ('model.cfr', 4), ('scenario.cfr', 1)])
        # Generated initializer/transition constraints must not duplicate authored warnings.
        result = self.compile(source='r -> int = #(noclafer.unknown)\nA ? -[A = A]-> A\n', b=bounds(3))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([json.loads(line)['operator'] for line in result.stderr.splitlines()], ['.', '='])

    # [utest->req~compiler-behavioral-elaboration~1]
    def test_empty_navigation_preserves_rejections_and_zero_divisor_admission(self):
        for expression in ['no (A -- A).missing', 'no (if some A then noclafer else noclafer).missing',
                           'no noclafer.(A ++ missing)', 'no noclafer.int', 'no noclafer.(some missing)',
                           '(noclafer.missing + (some A)) = 0']:
            result = self.compile(source='A ?\n[' + expression + ']\n', b=bounds(2))
            self.assertNotEqual(result.returncode, 0, (expression, result.stdout))
            self.assertEqual(result.stdout, b'')
            self.assertEqual(json.loads(result.stderr)['version'], 1)
        for expression in ['(1 / 0) = (1 / 0)', '(1 % 0) != (1 % 0)',
                           'noclafer.(1 / 0) = 0',
                           'no (if 1 / 0 = 0 then A else A).(noclafer.missing)',
                           'some A || (1 / 0) = (1 / 0)']:
            result = self.compile(source='A ?\n[' + expression + ']\n', b=bounds(2))
            self.assertEqual((result.returncode, result.stdout), (3, b''), (expression, result.stderr))
            self.assertNotIn(b'clafer-warning', result.stderr)
        # An earlier warning must not turn a later error into a partial successful result.
        result = self.compile(source='A ?\n[A = A]\n[some missing]\n', b=bounds(2))
        self.assertEqual((result.returncode, result.stdout), (2, b''))
        self.assertEqual(json.loads(result.stderr)['code'], 'behavioral.unknown-name')
        self.assertNotIn(b'clafer-warning', result.stderr)
