"""Native authored parser properties and live pinned Haskell syntax comparisons."""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


# [utest->req~compiler-parser~1]
# [utest->req~compiler-diagnostics~1]
class ParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='parser-', dir=parent))
        print(f'Parser evidence: {cls.output}', flush=True)
        cls.serial = 0
        cls.source = {str(p.relative_to(ROOT)): oracle.digest(p) for p in
                      [*sorted((ROOT / 'ClaferCompiler/Frontend').glob('*.lean')),
                       ROOT / 'tests/ParserNative.lean', Path(__file__)]}
        oracle.write(cls.output / 'source.json', cls.source)
        cls.modules = ['tests.ParserNative', 'ClaferCompiler.Frontend.Parser',
                       'ClaferCompiler.Frontend.Lexer', 'ClaferCompiler.Frontend.Surface',
                       'ClaferCompiler.IR.Structural']
        cls.command(['lake', 'build', *(f'+{m}:c.o' for m in cls.modules)])
        harness = cls.output / 'Harness.lean'
        harness.write_text('import tests.ParserNative\n'
                           'def main (args : List String) : IO Unit := ClaferCompiler.Tests.Parser.run args\n')
        cls.command(['lake', 'env', 'lean', f'--root={cls.output}', '-c',
                     str(cls.output / 'Harness.c'), str(harness)])
        cls.binary = cls.output / 'parser'
        cls.command(['lake', 'env', 'leanc', str(cls.output / 'Harness.c'),
                     *('.lake/build/ir/' + m.replace('.', '/') + '.c.o.export' for m in cls.modules),
                     '-o', str(cls.binary)])

    @classmethod
    def command(cls, cmd):
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=45)
        if p.returncode:
            raise AssertionError(f'{cmd}: {p.returncode}\n{p.stdout}\n{p.stderr}')
        return p

    @classmethod
    def tearDownClass(cls):
        for name, digest in cls.source.items():
            if oracle.digest(ROOT / name) != digest:
                raise AssertionError('Parser source changed during tests: ' + name)
        oracle.write(cls.output / 'evidence-index.json', {
            str(p.relative_to(cls.output)): oracle.digest(p)
            for p in sorted(cls.output.rglob('*')) if p.is_file()})

    @classmethod
    def parse_many(cls, sources):
        files = []
        for source in sources:
            cls.serial += 1
            path = cls.output / f'input-{cls.serial}.cfr'
            path.write_bytes(source.encode('utf-8'))
            files.append(path)
        p = cls.command([str(cls.binary), *map(str, files)])
        if p.stderr:
            raise AssertionError(p.stderr)
        results = p.stdout.split('\nEND\n')
        if results[-1] != '' or len(results) != len(files) + 1:
            raise AssertionError('incomplete native results')
        for path, result in zip(files, results):
            path.with_suffix('.result').write_text(result + '\n')
        return results[:-1]

    def test_authored_declarations_layout_and_braces(self):
        source = ('abstract xor Base\n  child ?\n'
                  'Root\n  `Base 2..*\n  set -> Target +\n  bag ->> Target *\n'
                  '  num -> integer 0..1\n  alias -> int\nTarget\n')
        out = self.parse_many([source])[0]
        self.assertTrue(out.startswith('ok\n'), out)
        self.assertIn('(decl Base true xor _ _ _ [(decl child false _ ? _ _ [])])', out)
        self.assertIn('(use Base false _ 2..* _ _ [])', out)
        self.assertIn('(decl set false _ + _ ->Target [])', out)
        self.assertIn('(decl bag false _ * _ ->>Target [])', out)
        self.assertIn('(decl num false _ 0..1 _ ->integer [])', out)
        self.assertIn('(decl alias false _ _ _ ->int [])', out)
        pairs = [('Root\n  child\n    grand\n  sibling\n', 'Root { child { grand }\n sibling }'),
                 ('Root\n  [some child]\n  child\n', 'Root { [some child] child }'),
                 ('0..* Root\n  x 0\n', '0..* Root { x 0 }')]
        for a, b in pairs:
            left, right = self.parse_many([a, b])
            self.assertTrue(left.startswith('ok\n'), left)
            self.assertEqual(left, right)
        variants = [source, '// heading\n' + source, source.replace('\n', '\r\n'),
                    source.replace('\n', ' // comment\n\n')]
        self.assertEqual(len(set(self.parse_many(variants))), 1)

    def test_cardinality_groups_and_unresolved_names(self):
        groups = ['xor', 'or', 'mux', 'opt', '0..0', '1..*', '2..3']
        cards = ['', '?', '+', '*', '0', '007', '0..0', '2..*', '2..3']
        sources = [f'{g} A\n  child {c}\n' for g in groups for c in cards]
        for source, out in zip(sources, self.parse_many(sources)):
            self.assertTrue(out.startswith('ok\n'), (source, out))
        # Syntax keeps later resolution errors and contradictions inspectable.
        sources = ['A -> Missing', 'A : A', 'A\nA', '5..5 A\n  B 0',
                   'A\n  same\nB\n  same', 'A\n  1..* B', 'A [a][b]',
                   '/* hi */ A\nB', 'A\n: Base', 'A\n?', 'A { B\n -> T }', 'abstract\nType', 'xor\nA', '`\nBase']
        for source, out in zip(sources, self.parse_many(sources)):
            self.assertTrue(out.startswith('ok\n'), (source, out))
        self.assertEqual(self.parse_many(['A\n1..* B'])[0],
                         'ok\n(decl A false _ 1..* _ _ [])\n(decl B false _ _ _ _ [])')
        self.assertEqual(self.parse_many(['A {\n B\n  C\n}'])[0],
                         'ok\n(decl A false _ _ _ _ [(decl B false _ _ _ _ []) (decl C false _ _ _ _ [])])')

    def test_expressions_and_exact_precedence(self):
        cases = {
            'a => b => c': '(=> (=> a b) c)',
            '!a = b && c': '(&& (! (= a b)) c)',
            'a + b ++ c -- d ** e.f': '(+ a (++ b (-- c (** d (. e f)))))',
            '-a ++ b': '(- (++ a b))', '#a.b': '(# (. a b))',
            'a not in b': '(not in a b)', 'not a': '(not a)',
            'some a ++ b': '(some (++ a b))',
            'one a - b': '(one a) (- b)',
            'a = some b - c': '(= a (some b)) (- c)',
            '(some a) + b': '(+ (some a) b)',
            'some (a + b)': '(some (+ a b))',
            'all x : A | some x': '(all x A (some x))',
            'all x : A | all x : x.child | x = x': '(all x A (all x (. x child) (= x x)))',
            'some x : A | no x.child': '(some x A (no (. x child)))',
            'no x : A | !x': '(no x A (! x))',
            'not x : A | x = 1': '(not x A (= x 1))',
            '(a + b) - c': '(- (+ a b) c)',
            'one a lone b no c': '(one a) (lone b) (no c)',
            'a = 1 b = 2': '(= a 1) (= b 2)',
            'this.parent.ref': '(. (. this parent) ref)',
            '': '',
        }
        actual = self.parse_many(['[' + s + ']' for s in cases])
        for (source, expected), out in zip(cases.items(), actual):
            self.assertEqual(out, 'ok\n[' + expected + ']', source)
        # Exhaust all two-operator combinations from the independent precedence table.
        levels = [['<=>'], ['=>'], ['||'], ['xor'], ['&&'],
                  ['=', '!=', '<', '>', '<=', '>=', 'in', 'not in'],
                  ['+', '-'], ['++'], ['--'], ['**'], ['.']]
        ops = [(op, level) for level, group in enumerate(levels) for op in group]
        sources, expected = [], []
        for a, pa in ops:
            for b, pb in ops:
                sources.append(f'[a {a} b {b} c]')
                expected.append(f'({b} ({a} a b) c)' if pa >= pb else f'({a} a ({b} b c))')
        for source, want, got in zip(sources, expected, self.parse_many(sources)):
            self.assertEqual(got, f'ok\n[{want}]', source)

    def test_rejections_do_not_erase_constructs(self):
        malformed = ['A\n\tB', 'A\n  B\n C', 'A { B', 'A }', 'A B', 'A { B C }', '[1.]', '[a + ]', '[all x A | x]',
                     '[a', '/* never closed', 'A 2..1', '2..1 A', '2 A', '_name', "a'\u0301",
                     'λ', '×', '÷', '[some]', '[some a + b]', '[no a ++ b + c]', '[a + some b]', '[a + #b + ]', 'A ->\n B', 'A :\n B', 'abstract\n  B', 'xor\n  B', '`\n  B', 'A 1..\n  2']
        unsupported = ['enum A = B | C', 'A -> string', 'A -> real', 'A -> double',
                       'A -> bool', 'A -> boolean', 'initial A', 'final A', 'finalref A',
                       'finaltarget A', '[X a]', '[always a]', '[a U b]', '[eventually a]',
                       'A --> B', 'A -->> B', 'A -[a]-> B', 'A := 1', 'A = 1', '`Base = 1',
                       'assert [a]', '<< minimize a >>', '[a * b]', '[a / b]', '[a % b]',
                       '[sum a]', '[product a]', '[min a]', '[max a]', '[if a then b else c]',
                       '[let x = a in x]', '[a <: b]', '[a :> b]', '[a,b]', '[a & b]',
                       '[all disj x : A | x]', '[all x; y : A | x]', '[one x : A | x]',
                       '[lone x : A | x]', '[1.2]', '[1.2e-3]', '["abc"]',
                       'A -> B ++ C', 'A : B.c', 'A -> (B)', '`A\\B', '[alloy| sig A {} |]',
                       '[choco| anything |]', '//# OPTIONS --flatten-inheritance\nA']
        for expected, inputs in [('malformed', malformed), ('unsupported', unsupported)]:
            for source, out in zip(inputs, self.parse_many(inputs)):
                self.assertTrue(out.startswith(expected + '|'), (source, out))

    def test_unicode_and_crlf_original_byte_diagnostics(self):
        accepted = ['À', 'Ö', 'Ø', 'ÿ', "Café_1'", 'integer', 'int', 'this', 'parent']
        for source, out in zip(accepted, self.parse_many(accepted)):
            self.assertTrue(out.startswith('ok\n'), (source, out))
        source = 'Café\r\n  [a * b]\r\n'
        out = self.parse_many([source])[0]
        self.assertEqual(out, 'unsupported|parser.arithmetic|parser|12|13|2|6')
        for name in ['Ā', '中文', '🙂', 'a\u0301', '١']:
            self.assertTrue(self.parse_many([name])[0].startswith('malformed|lexer.character|'))

    def test_generated_layout_and_malformed_inputs(self):
        # Finite property domain: depth 1..16, indentation width 1..4, cardinality variants.
        sources = []
        for depth in range(1, 17):
            for width in range(1, 5):
                lines = [' ' * (level * width) + f'n{level}' for level in range(depth)]
                sources.extend(['\n'.join(lines), ''.join(f'n{level} {{ ' for level in range(depth)) + '}' * depth])
        results = self.parse_many(sources)
        for i in range(0, len(results), 2):
            self.assertTrue(results[i].startswith('ok\n'), sources[i])
            self.assertEqual(results[i], results[i + 1])
        # Reproducible malformed mutations, never assume random text is invalid.
        rng = random.Random(160016)
        valid = [f'[all x : A | (x = {rng.randrange(1000)}) && some x]' for _ in range(128)]
        for out in self.parse_many(valid):
            self.assertTrue(out.startswith('ok\n'), out)
        mutations = [s[:-1] for s in valid] + [s + ' }' for s in valid]
        for out in self.parse_many(mutations):
            self.assertTrue(out.startswith('malformed|'), out)
        # Arbitrary inputs must terminate with a well-formed result or diagnostic.
        alphabet = 'abc01 []{}().+-*:#\n\t/!éλ'
        fuzz = [''.join(rng.choices(alphabet, k=rng.randrange(0, 120))) for _ in range(256)]
        for out in self.parse_many(fuzz):
            self.assertTrue(out.startswith(('ok\n', 'malformed|', 'unsupported|')), out)

    def test_live_pinned_haskell_parsing(self):
        api = oracle.adapters()
        tools = os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools:
            raise RuntimeError('CLAFER_ORACLE_TOOLS is required; parser comparison cannot skip')
        exporter, build, _ = oracle.load_tools(tools, api)
        oracle.write(self.output / 'reference-tools.json', {
            'exporter': oracle.digest(exporter), 'build': json.loads(build.read_text()),
            'scope': 'syntax only; unsupported capture audit is evidence of successful parsing'})
        positives = ['A', 'A\n  B ?', 'abstract Base\nA : Base',
                     'Target\nOwner\n  ref -> Target *', 'Target\nOwner\n  ref ->> Target *',
                     'xor A\n  B\n  C', 'A { B\n C }', 'À\n  Café',
                     '/* comment */ A', 'A\n1..* B', 'A\n?', 'A\n: Base', 'A { B\n -> T }', '[a][b]', 'A [some A]', 'A {\n B\n  C\n}',
                     '[all x : A | some x]', '[a + b = c]', '[a => b => c]',
                     '[a ++ b -- c ** d]', '[one a - b]', '[a = some b - c]', '[(some a) + b]', '[a not in b]', '[]', '`Base ?']
        negatives = ['[a + ]', '[all x A | x]', '/* unfinished', '_name', 'A B', 'abstract\n  B', 'A ->\n B', '[some a + b]', '[no a ++ b + c]']
        observations = []
        for expected, inputs in [(True, positives), (False, negatives)]:
            ours = self.parse_many(inputs)
            for source, our in zip(inputs, ours):
                path = self.output / f'reference-{len(observations)}.cfr'
                path.write_text(source)
                p = self.command([str(exporter), str(path)])
                ref = json.loads(p.stdout)
                path.with_suffix('.json').write_text(p.stdout)
                errors = str(ref.get('errors', ''))
                # C.parse errors are distinct from later resolution/type errors.
                parsed = ref['status'] in ('captured', 'unsupported') or (
                    ref['status'] == 'compiler_rejected' and 'ParseErr' not in errors)
                observations.append({'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
                                     'ours': our, 'reference_parsed': parsed, 'expected': expected})
                self.assertEqual(parsed, expected, (source, ref))
                self.assertEqual(our.startswith('ok\n'), expected, (source, our))
                if ref['status'] == 'captured':
                    inventory = dict(ref['source_audit']['constructors'])
                    self.assertEqual(inventory.get('Clafer', 0), our.count('(decl '))
                    self.assertEqual(inventory.get('ReferenceBag', 0), our.count('->>'))
                    self.assertEqual(inventory.get('ReferenceSet', 0), our.count('->') - our.count('->>'))
        # Known reference EOF crashes remain tool errors, never parse agreement.
        for source in ['A {', '[a', 'A ->']:
            path = self.output / f'reference-crash-{len(observations)}.cfr'
            path.write_text(source)
            p = subprocess.run([str(exporter), str(path)], capture_output=True, text=True, timeout=15)
            path.with_suffix('.stdout').write_text(p.stdout)
            path.with_suffix('.stderr').write_text(p.stderr)
            self.assertEqual(p.returncode, 1)
            self.assertTrue(p.stderr.startswith('clafer-capture: EOF'))
            ours = self.parse_many([source])[0]
            self.assertTrue(ours.startswith('malformed|'))
            observations.append({'source': source, 'reference': 'tool_error', 'ours': ours})
        # Adopted profile exclusions and strict layout deliberately differ from Haskell.
        for source in ['A\n\tB', 'A\n  B\n C', '[a * b]', 'A -> string']:
            path = self.output / f'reference-profile-{len(observations)}.cfr'
            path.write_text(source)
            p = self.command([str(exporter), str(path)])
            path.with_suffix('.json').write_text(p.stdout)
            ref = json.loads(p.stdout)
            self.assertIn(ref['status'], ('captured', 'unsupported'))
            ours = self.parse_many([source])[0]
            self.assertTrue(ours.startswith(('malformed|', 'unsupported|')))
            observations.append({'source': source, 'reference': 'parsed', 'ours': ours,
                                 'disposition': 'adopted architecture profile'})
        oracle.write(self.output / 'reference-comparison.json', observations)
