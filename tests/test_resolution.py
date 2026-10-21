"""Source resolution/default properties and pinned, fieldwise importer comparisons."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


# [utest->req~compiler-resolution~1]
# [utest->req~compiler-defaults~1]
# [utest->req~compiler-diagnostics~1]
class ResolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='resolution-', dir=parent))
        print(f'Resolution evidence: {cls.output}', flush=True)
        cls.serial = 0
        cls.modules = ['tests.ResolveNative', 'ClaferCompiler.Frontend.Resolve',
                       'ClaferCompiler.Frontend.Defaults', 'ClaferCompiler.Frontend.Parser',
                       'ClaferCompiler.Frontend.Lexer', 'ClaferCompiler.Frontend.Surface',
                       'ClaferCompiler.IR.Structural']
        cls.source = {str(p.relative_to(ROOT)): oracle.digest(p) for p in
                      [*(ROOT / (m.replace('.', '/') + '.lean') for m in cls.modules),
                       ROOT / 'ClaferCompiler/SemanticsBridge/Resolution.lean', Path(__file__)]}
        oracle.write(cls.output / 'source.json', cls.source)
        cls.command(['lake', 'build', *(f'+{m}:c.o' for m in cls.modules)])
        harness = cls.output / 'Harness.lean'
        harness.write_text('import tests.ResolveNative\n'
                           'def main (args : List String) : IO Unit := ClaferCompiler.Tests.Resolve.run args\n')
        cls.command(['lake', 'env', 'lean', f'--root={cls.output}', '-c',
                     str(cls.output / 'Harness.c'), str(harness)])
        cls.binary = cls.output / 'resolve'
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
                raise AssertionError('Resolution source changed during tests: ' + name)
        oracle.write(cls.output / 'evidence-index.json', {
            str(p.relative_to(cls.output)): oracle.digest(p)
            for p in sorted(cls.output.rglob('*')) if p.is_file()})

    @classmethod
    def resolve_many(cls, sources):
        files = []
        for source in sources:
            cls.serial += 1
            path = cls.output / f'input-{cls.serial}.cfr'
            path.write_bytes(source.encode())
            files.append(path)
        out = cls.command([str(cls.binary), *map(str, files)]).stdout.split('\nEND\n')
        if out[-1] != '' or len(out) != len(files) + 1:
            raise AssertionError('incomplete native results')
        for path, result in zip(files, out):
            path.with_suffix('.result').write_text(result)
        return out[:-1]

    def rows(self, source, m1=None):
        out = self.resolve_many([source])[0]
        self.assertTrue(out.startswith('ok\n'), (source, out))
        lines = out.splitlines()
        if m1 is not None:
            self.assertEqual(lines[1] == 'm1|ok', m1, out)
        return [r.split('|') for r in lines[2:]]

    def test_identity_lookup_forward_cycles_and_shadowing(self):
        rows = self.rows('Owner\n  Target\n  ref -> Target\nOther\n  Target\n  ref ->> Target\n', True)
        self.assertEqual([r[0] for r in rows], list(map(str, range(7))))
        self.assertEqual(rows[3][5:7], ['set', '2'])
        self.assertEqual(rows[6][5:7], ['bag', '5'])
        rows = self.rows('A -> B\nB -> A\n', True)
        self.assertEqual([r[6] for r in rows[1:]], ['2', '1'])
        rows = self.rows('ref -> Deep\nOwner\n  Deep\n', True)
        self.assertEqual(rows[1][6], '3')
        rows = self.rows('abstract Base\nOwner\n  `Base ?\n', True)
        self.assertEqual(rows[3][3:5], ['2', '1'])
        self.assertEqual(rows[3][8], '0..1')
        # Comments and line endings do not enter identity, lookup or defaults.
        source = 'A\n  r -> B\nB\n'
        self.assertEqual(self.resolve_many([source])[0], self.resolve_many(['// comment\r\n' + source.replace('\n', '\r\n')])[0])

    def test_default_matrix_overrides_and_inherited_provenance(self):
        groups = [('xor', '1..1', '0..1'), ('or', '1..*', '0..1'),
                  ('mux', '0..1', '0..1'), ('opt', '0..*', '0..1'),
                  ('1..1', '1..1', '1..1'), ('0..1', '0..1', '1..1'),
                  ('0..*', '0..*', '1..1'), ('', '0..*', '1..1')]
        for spelling, bound, child in groups:
            with self.subTest(group=spelling):
                rows = self.rows(f'{spelling} Owner\n  child\n  override 2..*\n'.lstrip(), True)
                self.assertEqual(rows[1][9], bound)
                self.assertEqual(rows[2][8], child)
                self.assertEqual(rows[3][8], '2..*')
                rows = self.rows(f'abstract {spelling} Base\n  field\nOwner : Base\n  local\n'.replace('  Base', ' Base'), False)
                self.assertEqual(rows[2][7:9], ['true', child])
                self.assertEqual(rows[1][13], 'true')
                self.assertEqual(rows[2][13:15], ['false', '_'])
                self.assertEqual(rows[3][9:11], rows[1][9:11])
                self.assertEqual(rows[4][8], child)
        rows = self.rows('abstract xor Base\n  field\nopt Owner : Base\n  local\n', False)
        self.assertEqual(rows[3][9:11], ['0..*', 'opt'])
        self.assertEqual(rows[4][8], '0..1')
        self.rows('xor Empty\n', False)  # impossible group retained, M1 guard remains exact

    def test_primitives_and_constraint_occurrences_are_not_erased(self):
        rows = self.rows('[some A]\nA\n  n -> int\n  m ->> integer\n  [n = m]\n', False)
        self.assertEqual(rows[2][6], rows[3][6])
        self.assertEqual(rows[4][1:4], ['int', 'int', '0'])
        self.assertEqual(rows[0][11], '1')
        self.assertEqual(rows[1][11], '1')
        rows = self.rows('abstract Base\n  field\n    [some field]\nOwner : Base\n', False)
        self.assertEqual(rows[2][11], '1')
        self.assertEqual(rows[3][11], '0')  # inherited view keeps original attachment
        out = self.resolve_many(['[]\nA\n'])[0]
        self.assertIn('m1|resolve.m1-constraints', out)

    def test_diagnostics_and_mutations(self):
        cases = [
            ('A -> Missing', 'missing-name'),
            ('A\n  Field\nB\n  Field\nr -> Field', 'ambiguous-name'),
            ('A\n  Field\n  Field', 'duplicate-name'),
            ('abstract A : B\nabstract B : A', 'inheritance-cycle'),
            ('abstract A : A', 'inheritance-cycle'),
            ('A\n  abstract B', 'nested-abstract'),
            ('abstract A\nr : A -> A', 'reference-inheritance'),
            ('abstract A -> A', 'abstract-reference'),
            ('A : int', 'primitive-super'),
            ('abstract A\n  B : A', 'realization-cycle'),
            ('Sing', 'reserved-name'), ('int', 'reserved-name'),
            ('integer', 'reserved-name'), ('A -> this', 'reserved-target')]
        for (source, code), out in zip(cases, self.resolve_many([s for s, _ in cases])):
            self.assertTrue(out.startswith('error|resolve.' + code + '|'), (source, out))
        out = self.resolve_many(['Café\r\n  r -> Absent\r\n'])[0].split('|')
        self.assertEqual(out[1:6], ['resolve.missing-name', '14', '20', '2', '8'])
        out = self.resolve_many(['A\n  Field\nB\n  Field\nr -> Field'])[0].split('|')
        self.assertEqual(out[-1], '2')

    def test_retained_haskell_default_disagreements(self):
        api = oracle.adapters()
        tools = os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools:
            raise RuntimeError('CLAFER_ORACLE_TOOLS is required')
        exporter, build, _ = oracle.load_tools(tools, api)
        observations = []
        for index, (source, ours_card, theirs_card) in enumerate([
                ('opt Owner\n  child\n', '0..1', [1, 1]),
                ('1..1 Owner\n  child\n', '1..1', [0, 1])]):
            rows = self.rows(source, True)
            path = self.output / f'default-difference-{index}.cfr'
            path.write_text(source)
            raw = json.loads(self.command([str(exporter), str(path)]).stdout)
            self.assertEqual(raw['status'], 'captured')
            nodes, _ = api['protocol'].decode_ir(json.loads(raw['json']))
            core, metadata = api['capture'].capture(path, exporter, build,
                {'root': 1, **{n['uid']: 4 for n in nodes}}, self.output / f'difference-{index}')
            self.assertEqual(rows[2][8], ours_card)
            self.assertEqual(core['declarations'][1]['card'], theirs_card)
            observations.append({'source': source, 'ours': rows, 'reference': core,
                'metadata': metadata, 'disposition': 'adopted upstream Defaults; expected disagreement'})
        oracle.write(self.output / 'default-disagreements.json', observations)

    def test_generated_depth_and_super_chains(self):
        for depth in range(1, 17):
            source = ''.join('  ' * i + f'N{i}\n' for i in range(depth))
            rows = self.rows(source, True)
            self.assertEqual([r[3] for r in rows[1:]], list(map(str, range(depth))))
            source = ''.join(f'abstract T{i}' + (f' : T{i+1}' if i+1 < depth else '') + '\n'
                             for i in range(depth)) + 'Owner : T0\n'
            rows = self.rows(source, True)
            self.assertEqual([r[4] for r in rows[1:depth]], list(map(str, range(2, depth+1))))
            self.assertEqual(rows[-1][4], '1')

    def test_pinned_importer_fieldwise_common_domain(self):
        api = oracle.adapters()
        tools = os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools:
            raise RuntimeError('CLAFER_ORACLE_TOOLS is required; resolution comparison cannot skip')
        exporter, build, _ = oracle.load_tools(tools, api)
        sources = ['A', 'abstract Base\nA : Base', 'A -> B\nB -> A',
                   'T\nOwner\n  a -> T *\n  b ->> T *', 'xor A\n  B\n  C',
                   'A\n  Field ?\nB\n  Field +']
        observations = []
        for index, source in enumerate(sources):
            rows = self.rows(source, True)[1:]
            path = self.output / f'reference-{index}.cfr'
            path.write_text(source)
            # Obtain UIDs only to choose explicit bounds; receipt/import pairs are regenerated.
            raw = json.loads(self.command([str(exporter), str(path)]).stdout)
            self.assertEqual(raw['status'], 'captured')
            nodes, _ = api['protocol'].decode_ir(json.loads(raw['json']))
            bounds = {'root': 1, **{n['uid']: 4 for n in nodes}}
            core, metadata = api['capture'].capture(path, exporter, build, bounds,
                                                     self.output / f'capture-{index}')
            nodes = core['declarations']
            self.assertEqual(len(nodes), len(rows))
            ids = {n['uid']: str(i + 1) for i, n in enumerate(nodes)}
            for ours, ref in zip(rows, nodes):
                interval = lambda xs: f'{xs[0]}..{xs[1] if xs[1] >= 0 else "*"}'
                parent = '_' if ref['abstract'] else ids.get(ref['parent'], '0')
                expected = [ref['name'], 'user', parent, ids.get(ref['super'], '_'),
                            ref['mode'], ids.get(ref['target'], '_'), str(ref['abstract']).lower()]
                self.assertEqual(ours[1:8], expected)
                # Parentless abstract fiber slots are irrelevant: source Defaults uses one;
                # importer uses unrestricted. The explicit M1 projection normalizes them.
                self.assertEqual(ours[8], '1..1' if ref['abstract'] else interval(ref['card']))
                self.assertEqual(ours[9], interval(ref['group']))
            observations.append({'source': source, 'ours': rows, 'imported': core,
                                 'metadata': metadata, 'status': 'fieldwise-agreement',
                                 'differences': ['IDs/root representation', 'parentless abstract local slot']})
        oracle.write(self.output / 'reference-comparison.json', observations)
