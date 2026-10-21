"""Source compilation, explicit M2 bounds and original source diagnostics."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/clafer-compiler'
FIXTURE = ROOT / 'tests/fixtures/pipeline'


# [utest->req~compiler-pipeline-correctness~1]
# [utest->req~compiler-cli~1]
# [utest->req~compiler-diagnostics~1]
class SourceCLITests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='clafer-source-')
        self.addCleanup(directory.cleanup)
        self.work = Path(directory.name)
        self.source = (FIXTURE / 'two-values.cfr').read_bytes()
        self.bounds = json.loads((FIXTURE / 'two-values.bounds.json').read_text())

    def compile(self, source=None, bounds=None, extra=(), output='-'):
        (self.work / 'model.cfr').write_bytes(self.source if source is None else source)
        (self.work / 'bounds.json').write_text(json.dumps(self.bounds if bounds is None else bounds))
        return self.call(['compile-source', 'model.cfr', '--bounds', 'bounds.json',
                          '--output', output, '--diagnostics', 'json', *extra])

    def call(self, args, data=None):
        return subprocess.run([str(EXE), *args], input=data, cwd=self.work,
                              env={'PATH': '/nonexistent', 'LANG': 'C'},
                              capture_output=True, timeout=10)

    def test_runtime_files_streams_and_stable_output(self):
        r = self.compile()
        self.assertEqual((r.returncode, r.stderr), (0, b''))
        self.assertIn(b': one Int', r.stdout)
        self.assertNotIn(str(self.work).encode(), r.stdout)
        self.assertEqual(self.compile().stdout, r.stdout)
        for args, data in [(['-', '--bounds', 'bounds.json'], self.source),
                           (['model.cfr', '--bounds', '-'], json.dumps(self.bounds).encode())]:
            streamed = self.call(['compile-source', *args, '--output', '-'], data)
            self.assertEqual(streamed.returncode, 0, streamed.stderr)
            # Logical input filenames may differ only in comments/maps.
            self.assertEqual(streamed.stdout, r.stdout)
        out = self.compile(output='out.als')
        self.assertEqual((out.returncode, out.stdout, out.stderr), (0, b'', b''))
        self.assertEqual((self.work / 'out.als').read_bytes(), r.stdout)
        self.assertEqual(self.compile(extra=['--objects', '4', '--bitwidth', '5']).returncode, 0)

    def test_closed_bounds_and_integer_tokens(self):
        cases = []
        def case(edit, exit_code):
            b = copy.deepcopy(self.bounds)
            edit(b)
            cases.append((b, exit_code))
        case(lambda b: b.update(version='clafer-bounds/1'), 3)
        case(lambda b: b.update(integers=[]), 2)
        case(lambda b: b['integers'].append(b['integers'][0]), 2)
        case(lambda b: b['integers'][0].update(id=2), 2)
        case(lambda b: b['integers'][0].update(lower=2, upper=1), 2)
        case(lambda b: b['integers'][0].update(lower=-9), 3)
        case(lambda b: b['integers'][0].update(lower=-1.0), 2)
        case(lambda b: b['integers'][0].update(lower='-1'), 2)
        case(lambda b: b['declarations'].pop(), 2)
        case(lambda b: b.update(objects=-1), 2)
        case(lambda b: b.update(unknown=True), 2)
        for b, code in cases:
            with self.subTest(bounds=b):
                r = self.compile(bounds=b)
                self.assertEqual(r.returncode, code, r.stderr)
                self.assertEqual(r.stdout, b'')
                self.assertEqual(json.loads(r.stderr)['version'], 1)
        for key, value in [('bitwidth', 0), ('lower', -9)]:
            bad = copy.deepcopy(self.bounds)
            if key == 'bitwidth': bad[key] = value
            else: bad['integers'][0][key] = value
            r = self.compile(bounds=bad)
            self.assertEqual(r.returncode, 3, r.stderr)
            self.assertEqual(json.loads(r.stderr)['primary']['file'], 'bounds.json')
            self.assertEqual(json.loads(r.stderr)['primary']['kind'], 'ir')
        self.compile()
        raw = json.dumps(self.bounds).replace('"lower": -1', '"lower": -0')
        (self.work / 'bounds.json').write_text(raw)
        r = self.call(['compile-source', 'model.cfr', '--bounds', 'bounds.json',
                       '--output', '-', '--diagnostics', 'json'])
        self.assertEqual(r.returncode, 2)

    def test_source_locations_and_failure_atomicity(self):
        old = b'previous output\n'
        (self.work / 'out.als').write_bytes(old)
        source = '// λ\r\nA\r\n[missing]\r\n'.encode()
        r = self.compile(source, output='out.als')
        self.assertEqual(r.returncode, 2, r.stderr)
        d = json.loads(r.stderr)
        loc = d['primary']
        self.assertEqual(loc['kind'], 'source')
        self.assertEqual(loc['file'], 'model.cfr')
        self.assertEqual((loc['line'], loc['column']), (3, 2))
        self.assertEqual(source[loc['startByte']:loc['endByte']], b'missing')
        self.assertNotIn('pointer', loc)
        self.assertEqual((self.work / 'out.als').read_bytes(), old)
        self.assertEqual(list(self.work.glob('.clafer-compiler-*.tmp')), [])
        r = self.compile(self.source + b'[a + 7 = 0]\n')
        self.assertEqual(r.returncode, 3, r.stderr)
        self.assertEqual(json.loads(r.stderr)['primary']['kind'], 'source')

    def test_valid_contradiction_and_exclusions(self):
        r = self.compile(self.source + b'[a = 1]\n')
        self.assertEqual(r.returncode, 0, r.stderr)
        for source in [b'a -> int\n[int]\n', b'A\n[2 * 3 = 6]\n', b'A\n<<A>>\n']:
            r = self.compile(source)
            self.assertEqual(r.returncode, 3, r.stderr)
            self.assertEqual(r.stdout, b'')

    # [utest->req~compiler-telematics~1]
    def test_complete_telematics_source(self):
        source = (ROOT / 'tests/fixtures/constraints/telematics.cfr').read_bytes()
        bounds = json.loads((FIXTURE / 'telematics.bounds.json').read_text())
        r = self.compile(source, bounds)
        self.assertEqual((r.returncode, r.stderr), (0, b''))
        self.assertEqual(r.stdout, self.compile(source, bounds).stdout)
        self.assertIn(b'7 Int', r.stdout)
        self.assertIn(b': one Int', r.stdout)

    def test_unused_primitive_and_primitive_parent_navigation(self):
        bounds = {
            'version': 'clafer-bounds/2', 'objects': 1, 'bitwidth': 4,
            'declarations': [{'id': 0, 'size': 1, 'exact': True},
                             {'id': 1, 'size': 0, 'exact': True}],
            'integers': [{'id': 1, 'lower': 0, 'upper': 0}],
        }
        r = self.compile(b'[0 = 0]\n', bounds)
        self.assertEqual((r.returncode, r.stderr), (0, b''))
        self.assertIn(b': one Int', r.stdout)
        r = self.compile(self.source + b'[a.dref.parent = b.dref.parent]\n')
        self.assertEqual((r.returncode, r.stderr), (0, b''))

    def test_ir_command_keeps_m1_bounds_version(self):
        self.bounds['integers'][0]['lower'] = 0
        self.compile()
        model = ROOT / 'tests/fixtures/cli/optional.json'
        r = self.call(['compile-ir', str(model), '--bounds', 'bounds.json',
                       '--output', '-', '--diagnostics', 'json'])
        self.assertEqual(r.returncode, 3)
        self.assertEqual(json.loads(r.stderr)['code'], 'bounds.version')


if __name__ == '__main__':
    unittest.main()
