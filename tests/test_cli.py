"""Native JSON/argument/IO boundaries and finite deterministic-output properties."""
import copy
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/clafer-compiler'
FIXTURES = ROOT / 'tests/fixtures/cli'


def encoded(value, **kwargs):
    return json.dumps(value, ensure_ascii=False, **kwargs).encode('utf-8')


# [utest->req~compiler-cli~1]
# [utest->req~compiler-diagnostics~1]
# [utest->req~compiler-ir~1]
class CLITests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='clafer-cli-')
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.model = json.loads((FIXTURES / 'optional.json').read_text())
        self.bounds = json.loads((FIXTURES / 'bounds.json').read_text())

    def call(self, args, data=None, **kwargs):
        return subprocess.run([str(EXE), *map(str, args)], input=data,
                              cwd=self.directory, capture_output=True, timeout=10, **kwargs)

    def compile(self, model=None, bounds=None, *, raw=None, extra=(), output='out.als'):
        (self.directory / 'model.json').write_bytes(
            raw if raw is not None else encoded(self.model if model is None else model))
        (self.directory / 'bounds.json').write_bytes(encoded(self.bounds if bounds is None else bounds))
        return self.call(['compile-ir', 'model.json', '--bounds', 'bounds.json',
                          '--output', output, '--diagnostics', 'json', *extra])

    def failure(self, result, code=2, diagnostic=None):
        self.assertEqual(result.returncode, code, result.stderr)
        self.assertEqual(result.stdout, b'')
        d = json.loads(result.stderr)
        self.assertEqual(set(d), {'version', 'code', 'phase', 'category', 'message', 'primary', 'related'})
        self.assertEqual(d['version'], 1)
        self.assertEqual(d['category'], {1:'operational', 2:'malformed', 3:'unsupported'}[code])
        self.assertEqual(d['primary']['kind'], 'ir')
        self.assertNotIn('line', d['primary'])
        self.assertNotIn('startByte', d['primary'])
        self.assertEqual(d['related'], [])
        if diagnostic:
            self.assertEqual(d['code'], diagnostic)
        return d

    def isolated_case(self, case):
        raw, bounds = case
        with tempfile.TemporaryDirectory(dir=self.directory) as directory:
            work = Path(directory)
            (work/'model.json').write_bytes(raw)
            (work/'bounds.json').write_bytes(encoded(bounds))
            (work/'out.als').write_bytes(b'previous output')
            r = subprocess.run([str(EXE),'compile-ir','model.json','--bounds','bounds.json',
                                '--output','out.als','--diagnostics','json'],cwd=work,
                               capture_output=True,timeout=10)
            return r, (work/'out.als').read_bytes(), list(work.glob('.clafer-compiler-*.tmp'))

    def test_files_streams_and_overrides(self):
        r = self.compile()
        self.assertEqual((r.returncode, r.stdout, r.stderr), (0, b'', b''))
        expected = (self.directory / 'out.als').read_bytes()
        self.assertTrue(expected.endswith(b'\n'))
        self.assertNotIn('résumé'.encode(), expected)
        for args, data in [
            (['-', '--bounds', 'bounds.json'], encoded(self.model)),
            (['model.json', '--bounds', '-'], encoded(self.bounds)),
        ]:
            r = self.call(['compile-ir', *args, '--output', '-'], data,
                          env={'PATH':'/nonexistent', 'LANG':'C'})
            self.assertEqual((r.returncode, r.stdout, r.stderr), (0, expected, b''))
        r = self.compile(extra=['--objects','3','--bitwidth','6'], output='-')
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(b'for 6 Int , 3 cc0', r.stdout)
        self.assertEqual(self.compile(output='model.json').returncode, 0)
        self.assertEqual((self.directory / 'model.json').read_bytes(), expected)
        self.assertEqual(list(self.directory.glob('.clafer-compiler-*.tmp')), [])

    def test_arguments_and_explicit_source_rejection(self):
        base = ['compile-ir','model.json','--diagnostics','json']
        for suffix in [[], ['--bounds','b'], ['--output','o'],
                       ['--bounds','b','--output','o','--unknown','x'],
                       ['--bounds','b','--output','o','--output','q'],
                       ['--bounds','b','--output','o','--bitwidth'],
                       ['--bounds','b','--output','o','--diagnostics','text']]:
            self.failure(self.call(base + suffix), diagnostic='cli.arguments')
        for value in ['-1','+2','2.0','2e0','02','', 'true']:
            self.failure(self.compile(extra=['--bitwidth',value]), diagnostic='cli.arguments')
        self.failure(self.call(['compile-ir','-','--bounds','-','--output','-',
                                '--diagnostics','json']), diagnostic='cli.arguments')
        self.failure(self.call(['compile-source','x','--diagnostics','json']), 3,
                     'cli.source-unsupported')

    def test_strict_json_and_utf8_preserve_existing_output(self):
        original = encoded(self.model)
        mutations = [b'', b'{} {}', b'\xef\xbb\xbf'+original, original+b'x',
            original.replace(b'"root": 100', b'"root": 100, "r\\u006fot": 100'),
            original.replace(b'"id": 7', b'"id": 7, "id": 7'),
            original.replace(b'"file": "example.cfr"', b'"file": "a", "file": "b"'),
            original.replace(b'"name": "root"', b'"name": "\\ud800"'),
            original.replace(b'"name": "root"', b'"name": "\\udc00"'),
            original.replace(b'"name": "root"', b'"name": "\\ud800\\u0041"'),
            original.replace(b'"name": "root"', b'"name": "\\q"'),
            original.replace(b'"name": "root"', b'"name": "bad\x00"'),
            original.replace(b'"root"', b'"\xff"', 1), original[:-1]+b',}',
        ]
        for token in [b'true', b'"100"', b'-0', b'-100', b'100.0', b'1e2', b'0100', b'+100']:
            mutations.append(original.replace(b'"root": 100', b'"root": '+token))
        # Each subprocess owns its entire input/output directory. Keep all cases,
        # but overlap process startup instead of serializing independent checks.
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(self.isolated_case,[(raw,self.bounds) for raw in mutations]))
        for raw,(result,output,temporary) in zip(mutations,results):
            with self.subTest(raw=raw[:100]):
                self.assertNotEqual(raw, original)
                self.failure(result)
                self.assertEqual(output,b'previous output')
                self.assertEqual(temporary,[])
        for name in ['"\\ud83d\\ude00"', '"😀"']:
            self.assertEqual(self.compile(raw=original.replace(b'"name": "root"',
                b'"name": '+name.encode())).returncode, 0)

    def test_schema_admission_codes_and_identity_locations(self):
        cases = []
        def case(edit, code, diagnostic):
            model = copy.deepcopy(self.model); edit(model); cases.append((model,code,diagnostic))
        case(lambda m: m.update(version='clafer-ir/2'), 3, 'ir.version')
        case(lambda m: m.update(profile='temporal'), 3, 'ir.profile')
        case(lambda m: m.update(constraints=[]), 2, 'input.schema')
        case(lambda m: m.pop('unused'), 2, 'input.schema')
        case(lambda m: m.update(root=999), 2, 'ir.missing-root')
        case(lambda m: m.update(parentRanks=[]), 2, 'ir.certificate-length')
        case(lambda m: m['declarations'][1].update(id=100), 2, 'ir.duplicate-id')
        case(lambda m: m['declarations'][1].update(parent=999), 2, 'ir.dangling-id')
        case(lambda m: m['declarations'][1].update(parent=7), 2, 'ir.invalid-core-or-ranks')
        case(lambda m: m['declarations'][1]['source'].update(endByte=0), 2, 'ir.invalid-span')
        case(lambda m: m['declarations'][1]['localBounds'].update(lower=2), 2, 'ir.invalid-core-or-ranks')
        case(lambda m: m['declarations'][1].update(origin='integer'), 3, 'ir.unsupported-or-invalid-certificate')
        case(lambda m: m['declarations'][1].update(origin='mystery'), 2, 'input.schema')
        case(lambda m: m['declarations'][1].update(reference={'kind':'unknown'}), 2, 'input.schema')
        case(lambda m: m['declarations'][1]['source'].update(extra=True), 2, 'input.schema')
        for model, code, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic):
                d = self.failure(self.compile(model), code, diagnostic)
                self.assertEqual(d['primary']['file'], 'model.json')
                if diagnostic == 'ir.dangling-id':
                    self.assertEqual(d['primary']['pointer'], '/declarations/1')
                    self.assertEqual(d['primary']['declaration'], 7)

    def test_bounds_and_contradictions(self):
        for key, value, code in [('version','clafer-bounds/2',3), ('objects',True,2),
                                  ('bitwidth',0,3), ('bitwidth',17,3), ('bitwidth',1,3)]:
            b = copy.deepcopy(self.bounds); b[key] = value
            self.failure(self.compile(bounds=b), code)
        for scopes in [[], self.bounds['declarations'][:1],
                       [self.bounds['declarations'][0]]*2,
                       [*self.bounds['declarations'], {'id':999,'size':1,'exact':False}]]:
            b = copy.deepcopy(self.bounds); b['declarations'] = scopes
            self.failure(self.compile(bounds=b), diagnostic='bounds.declarations')
        for objects in [0, 1]:
            b = copy.deepcopy(self.bounds); b['objects'] = objects
            b['declarations'][0].update(size=0,exact=True)
            r = self.compile(bounds=b)
            self.assertEqual((r.returncode, r.stdout, r.stderr), (0,b'',b''))
            self.assertIn(b'exactly 0 cc4', (self.directory/'out.als').read_bytes())

    def test_io_errors_and_atomic_replacement(self):
        self.compile()
        before = (self.directory/'out.als').read_bytes()
        for path in ['missing.json', 'directory']:
            if path == 'directory': (self.directory/path).mkdir()
            self.failure(self.call(['compile-ir',path,'--bounds','bounds.json',
                                   '--output','out.als','--diagnostics','json']), 1, 'io.read')
            self.assertEqual((self.directory/'out.als').read_bytes(),before)
        for path in ['absent/out.als', 'directory']:
            self.failure(self.compile(output=path), 1, 'io.write')
            self.assertEqual(list(self.directory.glob('.clafer-compiler-*.tmp')), [])
        with open('/dev/full', 'wb') as stream:
            r = subprocess.run([str(EXE),'compile-ir','model.json','--bounds','bounds.json',
                                '--output','-','--diagnostics','json'], cwd=self.directory,
                               stdout=stream,stderr=subprocess.PIPE,timeout=10)
        self.assertEqual(r.returncode,1)
        self.assertEqual(json.loads(r.stderr)['code'],'io.write')

    def test_generated_identity_and_json_layout_invariance(self):
        expected = self.compile(output='-').stdout
        rng = random.Random(190021)
        cases = []
        for i in range(24):
            model = copy.deepcopy(self.model); bounds = copy.deepcopy(self.bounds)
            ids = rng.sample(range(1000000),2)
            model['root'] = ids[0]
            for n, row in enumerate(model['declarations']):
                row['id'] = ids[n]
                row['name'] = ['sig', 'same', '😀é\\"\n', 'cc0'][i%4]
                if n: row['parent'] = ids[0]
                bounds['declarations'][n]['id'] = ids[n]
            rng.shuffle(bounds['declarations'])
            pairs = list(model.items()); rng.shuffle(pairs)
            raw = json.dumps(dict(pairs),ensure_ascii=bool(i%2),indent=i%4).encode()
            cases.append((raw,bounds))
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(self.isolated_case,cases))
        for i,(r,output,temporary) in enumerate(results):
            self.assertEqual((r.returncode,r.stdout,r.stderr),(0,b'',b''),i)
            self.assertEqual(output,expected,i)
            self.assertEqual(temporary,[],i)
