"""Behavioral grammar, original spans, static separation and pinned syntax probes."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import test_parser
from test_parser import oracle, ROOT


# [utest->req~compiler-behavioral-frontend~1]
class BehavioralParserTests(unittest.TestCase):
    command = classmethod(test_parser.ParserTests.command.__func__)
    parse_many = classmethod(test_parser.ParserTests.parse_many.__func__)
    tearDownClass = classmethod(test_parser.ParserTests.tearDownClass.__func__)

    @classmethod
    def setUpClass(cls):
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='behavioral-parser-', dir=parent))
        print(f'Behavioral parser evidence: {cls.output}', flush=True)
        cls.serial = 0
        cls.source = {str(p.relative_to(ROOT)): oracle.digest(p) for p in [
            *sorted((ROOT / 'ClaferCompiler/Frontend').rglob('*.lean')),
            ROOT / 'tests/BehavioralParserNative.lean', ROOT / 'tests/ParserNative.lean', Path(__file__)]}
        oracle.write(cls.output / 'source.json', cls.source)
        cls.modules = ['ClaferCompiler.IR.Structural', 'ClaferCompiler.Frontend.Surface',
                       'ClaferCompiler.Frontend.Defaults', 'ClaferCompiler.IR.BehavioralStructural',
                       'ClaferCompiler.Frontend.Lexer', 'ClaferCompiler.Frontend.Parser',
                       'ClaferCompiler.Frontend.Behavioral.Surface',
                       'ClaferCompiler.Frontend.Behavioral.Parser',
                       'tests.ParserNative', 'tests.BehavioralParserNative']
        cls.command(['lake', 'build', *(f'+{m}:c.o' for m in cls.modules)])
        harness = cls.output / 'Harness.lean'
        harness.write_text('import tests.BehavioralParserNative\n'
                           'def main (args : List String) : IO Unit := ClaferCompiler.Tests.BehavioralParser.run args\n')
        cls.command(['lake', 'env', 'lean', f'--root={cls.output}', '-c',
                     str(cls.output / 'Harness.c'), str(harness)])
        cls.binary = cls.output / 'parser'
        cls.command(['lake', 'env', 'leanc', str(cls.output / 'Harness.c'),
                     *('.lake/build/ir/' + m.replace('.', '/') + '.c.o.export' for m in cls.modules),
                     '-o', str(cls.binary)])

    def test_complete_patterns_anchors_and_signs(self):
        rows = ['never p', 'sometime p', 'lonce p', 'always p', 's must precede p', 's must follow p']
        expected_rows = ['never p', 'sometime p', 'lonce p', 'always p', 'precede s p', 'follow s p']
        scopes = ['', 'before r', 'after q', 'between q and r', 'after q until r']
        scope_shapes = ['suffix', 'before r', 'after q', 'between q r', 'after until q r']
        sources, wanted = [], []
        for row, shape in zip(rows, expected_rows):
            for scope, scope_shape in zip(scopes, scope_shapes):
                expr, tree = f'{row} {scope}', f'({shape} @{scope_shape})'
                for spelling, expected in [(expr, tree), (f'!({expr})', f'(! {tree})'),
                                            (f'initially ({expr})', f'(initially {tree})')]:
                    sources.append(f'[{spelling}]')
                    wanted.append(f'ok\n[{expected}]')
        self.assertEqual(self.parse_many(sources), wanted)

    def test_precedence_transitions_binders_and_aliases(self):
        cases = {
            'a --> b --> c': '(--> a  | (--> b  | c))',
            'a -[g]-> b -[h]->> c': '(--> a g | (-->> b h | c))',
            'a => b --> c && d': '(--> (=> a b)  | (&& c d))',
            'a U b W c && d': '(&& (U a (W b c)) d)',
            'F G X !a = b': '(F (G (X (! (= a b)))))',
            'eventually globally next a': '(eventually (globally (next a)))',
            'a until b weakuntil c': '(until a (weakuntil b c))',
            'initially a => b': '(initially (=> a b))',
            'finally a': '(finally a)',
            'all disj x; y : A | X (x = y)': '(all disj x;y A (X (= x y)))',
            'one x; y : A | x = y': '(one x;y A (= x y))',
            'lone x : A | !(F x)': '(lone x A (! (F x)))',
            'not x : A | X x': '(not x A (X x))',
            'let x = A in X x': '(let x A (X x))',
            'if p then X a else F b': '(if p (X a) (F b))',
            'sum a ++ b * 2 + min c': '(+ (* (sum (++ a b)) 2) (min c))',
            'product a / 2 % 3': '(% (/ (product a) 2) 3)',
            'a <: b :> c, d & e.f': '(<: a (:> b (, c (. (& d e) f))))',
        }
        for source, actual in zip(cases, self.parse_many([f'[{s}]' for s in cases])):
            self.assertEqual(actual, f'ok\n[{cases[source]}]', source)
        # Independent grammar categories: all ordinary binary operators associate left.
        levels = [['<=>'], ['=>'], ['||'], ['xor'], ['&&'], ['U', 'until'], ['W', 'weakuntil'],
                  ['=', '!=', '<', '>', '<=', '>=', 'in', 'not in'], ['+', '-'], ['*', '/', '%'],
                  ['<:'], [':>'], ['++', ','], ['--'], ['**'], ['.', '&']]
        ops = [(op, level) for level, group in enumerate(levels) for op in group]
        sources, wanted = [], []
        for a, pa in ops:
            for b, pb in ops:
                sources.append(f'[a {a} b {b} c]')
                tree = f'({b} ({a} a b) c)' if pa >= pb else f'({a} a ({b} b c))'
                wanted.append(f'ok\n[{tree}]')
        self.assertEqual(self.parse_many(sources), wanted)

    def test_modifiers_enums_initializers_attachment_and_layout(self):
        sources = []
        for mods in ['finalref finaltarget', 'finaltarget finalref', 'finalref finalref finaltarget',
                     'initial final finaltarget finalref']:
            for tail in ['-> T', ': Base']:
                sources.append(f'abstract Base -> T\nT\n{mods} ref {tail}\n')
        for source, out in zip(sources, self.parse_many(sources)):
            self.assertTrue(out.startswith('ok\n'), (source, out))
            mods = source.splitlines()[2].split(' ref ')[0].replace(' ', ',')
            self.assertIn(f'decl ref false {mods} ', out)
        source = ('enum Mode = Idle | Busy\n'
                  'machine\n  initial idle -[coin]-> busy --> idle\n'
                  '    assert [X busy]\n  busy\n  coin ?\n  value -> int = 2\n'
                  '[initially (machine.idle --> machine.busy)]\n')
        out = self.parse_many([source])[0]
        self.assertTrue(out.startswith('ok\n'), out)
        self.assertIn('(enum Mode Idle|Busy)', out)
        self.assertIn('assert[(X busy)]', out)
        self.assertIn('->int = 2', out)
        variants = [source, source.replace('\n', '\r\n'), '// Café\n' + source,
                    source.replace('\n', ' // comment\n\n')]
        self.assertEqual(len(set(self.parse_many(variants))), 1)
        for depth in [1, 2, 8, 16]:
            indented = '\n'.join('  ' * i + f'final node{i}' for i in range(depth))
            braced = ''.join(f'final node{i} {{ ' for i in range(depth)) + '}' * depth
            a, b = self.parse_many([indented, braced])
            self.assertTrue(a.startswith('ok\n'), a)
            self.assertEqual(a, b)

    def test_malformed_and_excluded_forms(self):
        malformed = ['[a -->]', '[a -[g] b]', '[never a between q]', '[a must b]',
                     '[all disj x; : A | x]', '[let x = A]', '[if a then b]',
                     '[X]', '[one x : A |]', 'enum E =', 'A\n  enum E = B',
                     'A\n\tinitial B', 'A\n  B\n C', 'assert a', '[!X a]',
                     '[always p && initially q]', 'initial\n  A']
        unsupported = ['A := 1', '[alloy| x |]', '//# OPTIONS\nA', 'A -> string',
                       '[1.2]', 'A -> B ++ C', 'A : B.c', '<< minimize A >>', '["str"]', '`A\\B']
        for expected, sources in [('malformed', malformed), ('unsupported', unsupported)]:
            for source, out in zip(sources, self.parse_many(sources)):
                self.assertTrue(out.startswith(expected + '|'), (source, out))
        out = self.parse_many(['Café\r\n  [a / ]\r\n'])[0]
        self.assertEqual(out, 'malformed|behavioral.expression|parser|14|15|2|8')

    def test_live_pinned_syntax_comparison(self):
        import temporal
        tools_file = os.environ.get('CLAFER_TEMPORAL_TOOLS')
        if not tools_file:
            raise RuntimeError('CLAFER_TEMPORAL_TOOLS is required; syntax comparison cannot skip')
        # Reuse receipt checks; later compiler errors still establish parsing only.
        loaded = temporal.load_tools(tools_file)
        exporter = loaded['exporter']
        oracle.write(self.output / 'reference-tools.json', loaded['tools'])
        positives = ['initial final A', 'finalref finaltarget r -> T\nT',
                     'finaltarget finalref r : Base\nabstract Base -> T\nT',
                     'finalref finalref r -> T\nT',
                     '[a --> b --> c]', '[a -[g]-> b -[h]->> c]',
                     '[all disj x; y : A | X (x = y)]', '[one x; y : A | x = y]',
                     '[if a then X b else F c]',
                     'A --> B\n  assert [X B]\nB', 'enum E = A | B',
                     '[s must follow p between q and r]', '[s must precede p after q]',
                     '[never p after q until r]', '[initially (sometime p)]',
                     '[sum a ++ b * 2 + min c]', '[a <: b :> c, d & e.f]']
        negatives = ['[a -->]', '[a -[g] b]', '[never a between q]', '[!X a]', '[if a then b]']
        observations = []
        for expected, sources in [(True, positives), (False, negatives)]:
            for source, ours in zip(sources, self.parse_many(sources)):
                path = self.output / f'reference-{len(observations)}.cfr'
                path.write_text(source)
                p = subprocess.run([str(exporter), str(path)], capture_output=True, text=True, timeout=30)
                path.with_suffix('.stdout').write_text(p.stdout)
                path.with_suffix('.stderr').write_text(p.stderr)
                self.assertEqual(p.returncode, 0, (source, p.stderr))
                ref = json.loads(p.stdout)
                parsed = ref['status'] != 'malformed' or 'ParseErr' not in ref.get('detail', '')
                observations.append({'source': source, 'ours': ours, 'reference_parsed': parsed,
                                     'status': ref['status'], 'expected': expected})
                self.assertEqual(parsed, expected, (source, ref))
                self.assertEqual(ours.startswith('ok\n'), expected, (source, ours))
        # The pinned exporter crashes after parsing LetExp. Preserve tool failure;
        # it does not establish successful compilation or semantic agreement.
        source = '[let x = A in X x]'
        path = self.output / 'reference-let-crash.cfr'
        path.write_text(source)
        p = subprocess.run([str(exporter), str(path)], capture_output=True, text=True, timeout=30)
        path.with_suffix('.stdout').write_text(p.stdout)
        path.with_suffix('.stderr').write_text(p.stderr)
        self.assertEqual(p.returncode, 1)
        self.assertIn('Desugarer', p.stderr)
        self.assertIn('LetExp', p.stderr)
        ours = self.parse_many([source])[0]
        self.assertTrue(ours.startswith('ok\n'), ours)
        observations.append({'source': source, 'ours': ours, 'reference': 'tool_error',
                             'stage': 'desugar', 'syntax_agreement_claimed': False})
        oracle.write(self.output / 'reference-comparison.json', observations)
