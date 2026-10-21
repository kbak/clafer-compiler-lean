"""Native elaboration against the kernel-checked pinned manual inventory."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


# [utest->req~compiler-constraint-elaboration~1]
# [utest->req~compiler-diagnostics~1]
class ConstraintTests(unittest.TestCase):
    @classmethod
    def command(cls, args):
        result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=45)
        if result.returncode:
            raise AssertionError(f'{args}: {result.returncode}\n{result.stdout}\n{result.stderr}')
        return result.stdout

    @classmethod
    def setUpClass(cls):
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='constraints-', dir=parent))
        print(f'Constraint evidence: {cls.output}', flush=True)
        cls.serial = 0
        cls.modules = ['tests.ConstraintsNative', 'ClaferCompiler.IR.Structural', 'ClaferCompiler.IR.Expr',
                       *(f'ClaferCompiler.Frontend.{m}' for m in
                         ['Surface', 'Lexer', 'Parser', 'Defaults', 'Resolve', 'ConstraintsSupport',
                          'ConstraintsRules', 'ConstraintsNames', 'ConstraintsCoercions', 'ConstraintsOps', 'Constraints'])]
        files = [*(ROOT / (m.replace('.', '/') + '.lean') for m in cls.modules),
                 ROOT / 'tests/ConstraintsInventory.lean', ROOT / 'ClaferCompiler/SemanticsBridge/Constraints.lean',
                 ROOT / 'tests/fixtures/constraints/telematics.cfr', Path(__file__)]
        cls.source = {str(p.relative_to(ROOT)): oracle.digest(p) for p in files}
        oracle.write(cls.output / 'source.json', cls.source)
        cls.command(['lake', 'build', *(f'+{m}:c.o' for m in cls.modules)])
        harness = cls.output / 'Harness.lean'
        harness.write_text('import tests.ConstraintsNative\n'
                           'def main (args : List String) : IO Unit := ClaferCompiler.Tests.Constraints.run args\n')
        cls.command(['lake', 'env', 'lean', f'--root={cls.output}', '-c', str(cls.output / 'Harness.c'), str(harness)])
        cls.binary = cls.output / 'constraints'
        cls.command(['lake', 'env', 'leanc', str(cls.output / 'Harness.c'),
                     *('.lake/build/ir/' + m.replace('.', '/') + '.c.o.export' for m in cls.modules), '-o', str(cls.binary)])

    @classmethod
    def tearDownClass(cls):
        for name, digest in cls.source.items():
            if oracle.digest(ROOT / name) != digest:
                raise AssertionError('Constraint source changed during tests: ' + name)
        oracle.write(cls.output / 'evidence-index.json', {
            str(p.relative_to(cls.output)): oracle.digest(p)
            for p in sorted(cls.output.rglob('*')) if p.is_file()})

    @classmethod
    def compile(cls, source):
        cls.serial += 1
        path = cls.output / f'input-{cls.serial}.cfr'
        path.write_bytes(source.encode())
        result = cls.command([str(cls.binary), str(path)])
        path.with_suffix('.result').write_text(result)
        if not result.endswith('\nEND\n'):
            raise AssertionError('Incomplete native result')
        return result[:-5]

    def rows(self, source):
        result = self.compile(source)
        self.assertTrue(result.startswith('ok\n'), result)
        return [line.split('|', 5) for line in result.splitlines()[1:]]

    def shape(self, source):
        return [row[5] for row in self.rows(source)]

    def test_all_twelve_manual_bodies_and_attachment_positions(self):
        projection = self.output / 'Manual.lean'
        projection.write_text('import tests.ConstraintsInventory\n'
                              '#eval IO.println (String.intercalate "\\n" ClaferCompiler.Tests.ConstraintInventory.expected)\n')
        expected = self.command(['lake', 'env', 'lean', str(projection)]).strip().splitlines()
        self.assertEqual(len(expected), 12)
        source = (ROOT / 'tests/fixtures/constraints/telematics.cfr').read_text()
        rows = self.rows(source)
        expected_order = expected[9:] + expected[:9]  # root, then source declaration order
        self.assertEqual([r[5] for r in rows], expected_order)
        self.assertEqual([int(r[0]) for r in rows], [0, 0, 0, 1, 11, 15, 15, 19, 19, 19, 19, 19])
        self.assertEqual([int(r[1]) for r in rows], [0, 1, 2, 0, 0, 0, 1, 0, 1, 2, 3, 4])
        for row in rows:
            a, b = map(int, row[3:5])
            self.assertEqual(source.encode()[a-1:a], b'[')
            self.assertEqual(source.encode()[b:b+1], b']')
        oracle.write(self.output / 'manual-comparison.json', {'expected': expected_order, 'actual': [r[5] for r in rows]})
        for before, after in [('server = parent', 'server != parent'),
                              ('version >= server.version', 'version <= server.version'),
                              ('#ECU1.plaDisplay = 2', '#ECU1.plaDisplay = 1'),
                              ('cache.size.fixed', 'cache.size')]:
            changed = self.shape(source.replace(before, after))
            self.assertNotEqual(changed, expected_order)

    def test_head_counts_numeric_values_and_definedness_obligations(self):
        self.assertEqual(self.shape('[1 = 1]\n'), ['eq(1,1)'])
        source = 'Target\nOwner\n  r ->> Target *\n  n ->> int *\n  [#r = 2]\n  [#r.dref = 1]\n  [n > 1000000000000000000000000]\n'
        shapes = self.shape(source)
        self.assertNotIn('dref', shapes[0])
        self.assertIn('count(image(image(this,head3),dref3))', shapes[1])
        self.assertIn('int(image(image(this,head4),dref4))', shapes[2])
        # Zero/many multiplicities and huge integers remain typed; the backend
        # must discharge extraction, finite observation and overflow obligations.
        self.assertEqual(self.shape('A\n  r -> A *\n  [r = r]\n')[0].count('dref2'), 2)

    def test_binders_shadowing_and_domain_scope(self):
        shapes = self.shape('A *\n[all x : A | all x : x | x = x]\n')
        self.assertIn('all[1:1](extent1,all[2:1](var0,eq(var0,var0)))', shapes[0])
        self.assertIn('all[2:1](extent1,eq(var1,var0))', self.shape('A *\n[all x : A | all y : A | x = y]\n')[0])
        for quant in ['some', 'no', 'not']:
            self.rows(f'A *\n[{quant} x : A | some x]\n')
        self.assertIn('constraint.missing-name', self.compile('A\n[all x : x | some x]\n'))

    def test_operators_and_nested_paths(self):
        source = 'A *\n' + ''.join(f'[{body}]\n' for body in [
            '!A', 'some A', 'no A', 'not A', 'one A', 'lone A',
            'A && A', 'A || A', 'A xor A', 'A => A', 'A <=> A',
            'A = A', 'A != A', 'A in A', 'A not in A',
            '#(A ++ A) = 1', '#(A -- A) = 0', '#(A ** A) = 1',
            '-2 + 3 - 1 <= 0', '2 > 1', '2 >= 1', '1 < 2'])
        shapes = self.shape(source)
        self.assertEqual(len(shapes), 22)
        self.assertEqual('not(lt(0,sub(add(sub(0,2),3),1)))', shapes[-4])
        self.rows('A\n  B\n    C\n[A.(B.C)]\n')

    def test_diagnostics_and_ambiguous_or_wrong_endpoints(self):
        cases = [
            ('A\nB\n[A = B]\n', 'constraint.incompatible-endpoints'),
            ('A\n[1.A]\n', 'constraint.join-endpoint'),
            ('A\n[parent]\n', 'constraint.no-parent'),
            ('A\n[A.dref]\n', 'constraint.not-reference'),
            ('A\n  x\nB\n  x\n[x]\n', 'constraint.ambiguous-name'),
            ('A\n[A.unknown]\n', 'constraint.missing-navigation'),
            ('A\n[int]\n', 'constraint.infinite-primitive-extent'),
            ('A\n[1 && A]\n', 'constraint.type-mismatch'),
            ('A\n[all x : 1 | A]\n', 'constraint.binder-domain'),
            ('A\n[all this : A | A]\n', 'constraint.reserved-binder'),
        ]
        for source, code in cases:
            with self.subTest(source=source):
                self.assertIn(code, self.compile(source))
        source = '// café\r\nA\r\n[A.missing]\r\n'
        result = self.compile(source).split('|')
        self.assertEqual(int(result[2]), source.encode().index(b'missing'))
        self.assertEqual(int(result[3]), source.encode().index(b'missing') + len('missing'))
        self.assertEqual([int(result[4]), int(result[5])], [3, 4])

    def test_generated_inheritance_and_context_climbs(self):
        for depth in range(1, 13):
            declarations = 'abstract Base\n  field\n'
            for i in range(depth):
                declarations += f'abstract T{i} : {"Base" if i == 0 else "T" + str(i-1)}\n'
            source = declarations + f'Instance : T{depth-1}\n  [field]\n'
            shape = self.shape(source)[0]
            self.assertIn('head2', shape)
            self.assertEqual(shape.count('super'), depth + 1)
        rows = self.rows('Owner\n  sibling\n  child\n    nested\n      [sibling]\n')
        self.assertIn('image(image(image(this,parent4),parent3),head2)', rows[0][5])

    def test_empty_multiple_and_deterministic_source_occurrences(self):
        self.assertEqual(self.rows('A\n[]\n'), [])
        source = 'A\n  [A A]\n[A]\n'
        rows = self.rows(source)
        self.assertEqual([r[:3] for r in rows], [['0', '0', '0'], ['1', '0', '0'], ['1', '0', '1']])
        self.assertEqual(self.shape(source), self.shape('// comment\r\n' + source.replace('\n', '\r\n')))

    def test_reference_chains_and_common_super_coercions(self):
        source = 'Target\n  leaf\nr2 -> Target\nr1 -> r2\n  [leaf]\n'
        shape = self.shape(source)[0]
        self.assertIn('image(image(image(this,dref4),dref3),head2)', shape)
        source = 'Target\na -> Target\nb -> Target\n[some (a ++ b)]\n'
        self.assertIn('union(image(extent2,dref2),image(extent3,dref3))', self.shape(source)[0])
        source = 'abstract Base\nA : Base\nB : Base\n[some (A ++ B)]\n'
        self.assertIn('union(super2(extent2),super3(extent3))', self.shape(source)[0])
        # A field on a reference head wins over one on its target.
        source = 'Target\n  field\nr -> Target\n  field\n  [field]\n'
        self.assertIn('head4', self.shape(source)[0])
        self.assertNotIn('dref', self.shape(source)[0])
        source = 'abstract Base\n  field\nDerived : Base\n  field\n  [field]\n'
        self.assertIn('head4', self.shape(source)[0])
        self.assertNotIn('super', self.shape(source)[0])

    def test_generated_alpha_renaming_and_parentheses(self):
        for depth in range(1, 13):
            binders = ''.join(f'all x{i} : A | ' for i in range(depth))
            expression = binders + f'x0 = x{depth-1}'
            source = f'A *\n[{expression}]\n'
            expected = self.shape(source)
            renamed = source.replace('x', 'bound')
            self.assertEqual(expected, self.shape(renamed))
            self.assertEqual(expected, self.shape(f'A *\n[({expression})]\n'))
