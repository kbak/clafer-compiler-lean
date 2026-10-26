"""Exact inherited/source candidates, independent structural checks and replays.

The body evaluator is justified at the finite-observation boundary by
Pipeline.candidate_constraint_iff. It is not a whole infinite-model checker.
Haskell's guarded M1 checker is deliberately absent from this extension.
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


def rows(path):
    return [[int(n) for n in line.split()] for line in path.read_text().splitlines()]


def schema(directory):
    sigs, fields = {}, {}
    for row in rows(directory / 'schema.rows'):
        if row[0] == 0:
            _, i, parent, abstract, scalar = row
            sigs[i] = dict(parent=None if parent == 0 else parent - 1,
                           abstract=bool(abstract), scalar=bool(scalar))
        else:
            _, i, owner, target = row
            fields[i] = dict(owner=owner, target=target)
    return dict(signatures=sigs, fields=fields)


def witness(path, spec):
    """Read Alloy XML's explicit signature tree, preserving opaque atom names."""
    instance = ET.parse(path).getroot().find('instance')
    sigs = {int(s.attrib['label'].removeprefix('this/cc')) // 4:
            [a.attrib['label'] for a in s.findall('atom')]
            for s in instance.findall('sig') if s.attrib['label'].startswith('this/cc')}
    if set(sigs) != set(spec['signatures']):
        raise ValueError('signature inventory')
    def extent(i):
        result = list(sigs[i])
        for child, decl in spec['signatures'].items():
            if decl['parent'] == i:
                result.extend(extent(child))
        return sorted(set(result))
    atoms = extent(0)
    labels = {a: i for i, a in enumerate(atoms)}
    signatures = [[labels[a] for a in extent(i)] for i in range(len(sigs))]
    fields = [[] for _ in spec['fields']]
    values = [[] for _ in sigs]
    seen_fields, seen_values = set(), set()
    for f in instance.findall('field'):
        name = f.attrib['label']
        if not name.startswith('cc'):
            raise ValueError('field name')
        number = int(name[2:])
        pairs = [[a.attrib['label'] for a in t.findall('atom')] for t in f.findall('tuple')]
        if any(len(pair) != 2 for pair in pairs):
            raise ValueError('tuple arity')
        if number % 4 == 1:
            i = number // 4
            if i not in spec['fields'] or i in seen_fields:
                raise ValueError('field inventory')
            seen_fields.add(i)
            fields[i] = [[labels[a], labels[b]] for a, b in pairs]
        elif number % 4 == 3:
            i = number // 4
            if not spec['signatures'][i]['scalar'] or i in seen_values:
                raise ValueError('scalar inventory')
            seen_values.add(i)
            values[i] = [[labels[a], int(b)] for a, b in pairs]
        else:
            raise ValueError('field namespace')
    if seen_fields != set(spec['fields']) or seen_values != {
            i for i, s in spec['signatures'].items() if s['scalar']}:
        raise ValueError('missing field')
    return dict(signatures=signatures, fields=fields, values=values)


def tables(candidate):
    out = [[len(candidate['signatures']), len(candidate['fields'])]]
    out += [[0, *xs] for xs in candidate['signatures']]
    out += [[1, i, a, b] for i, xs in enumerate(candidate['fields']) for a, b in xs]
    out += [[2, i, a, z] for i, xs in enumerate(candidate['values']) for a, z in xs]
    return ''.join(' '.join(map(str, row)) + '\n' for row in out)


def pin(candidate, spec):
    names = {a: f'pipeline_atom_{a}' for a in candidate['signatures'][0]}
    union = lambda xs, empty='none': ' + '.join(xs) or empty
    clauses = [f'cc{4*i} = ({union([names[a] for a in xs])})'
               for i, xs in enumerate(candidate['signatures'])]
    clauses += [f'@cc{4*i+1} = ({union([names[a]+"->"+names[b] for a,b in xs], "none->none")})'
                for i, xs in enumerate(candidate['fields'])]
    clauses += [f'@cc{4*i+3} = ({union([names[a]+"->("+str(z)+")" for a,z in xs], "none->none")})'
                for i, xs in enumerate(candidate['values']) if spec['signatures'][i]['scalar']]
    return 'fact { some disj ' + ', '.join(names.values()) + ': cc0 | {\n' + '\n'.join(clauses) + '\n} }\n'


def bounds(counts, objects, integer=None, width=5):
    return dict(version='clafer-bounds/2', objects=objects, bitwidth=width,
                declarations=[dict(id=i, size=n, exact=True) for i, n in enumerate(counts)],
                integers=[] if integer is None else [dict(id=integer, lower=0, upper=1)])


# [utest->req~compiler-pipeline-correctness~1]
# [utest->req~compiler-telematics~1]
# [utest->req~compiler-defaults~1]
class SourcePipelineTests(unittest.TestCase):
    def test_exact_candidates_and_mutation_replays(self):
        api = oracle.adapters()
        config = os.environ.get('CLAFER_ORACLE_TOOLS')
        self.assertTrue(config, 'CLAFER_ORACLE_TOOLS is required')
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='source-pipeline-', dir=parent))
        print(f'Source pipeline evidence: {output}', flush=True)
        sources = [*sorted((ROOT / 'ClaferCompiler').rglob('*.lean')),
                   ROOT / 'tests/PipelineNative.lean', ROOT / 'tests/ComparisonNative.lean',
                   Path(__file__), ROOT / 'scripts/oracles/oracle.py',
                   ROOT / 'scripts/oracles/AlloyArithmeticBridge.java',
                   ROOT / 'scripts/oracles/AlloyTextBridge.java',
                   *sorted((ROOT / 'tests/fixtures/pipeline').glob('*')),
                   ROOT / 'tests/fixtures/constraints/telematics.cfr',
                   ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json', ROOT / 'lakefile.toml',
                   ROOT / 'schemas/clafer-bounds-2.schema.json']
        for p in sources:
            dest = output / 'source' / p.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(p.read_bytes())
        oracle.write(output / 'source.json', {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / 'runtime.json', runtime['identity'])
        executable = ROOT / '.lake/build/bin/clafer-compiler'
        oracle.write(output / 'binary.json', oracle.digest(executable))
        env = api['alloy_runtime'].java_env()

        def run(name, command, cwd=output):
            oracle.write(output / (name + '-command.json'), list(map(str, command)))
            r = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                               capture_output=True, text=True, timeout=45)
            (output / (name + '-stdout.log')).write_text(r.stdout)
            (output / (name + '-stderr.log')).write_text(r.stderr)
            self.assertEqual(r.returncode, 0, name + ': ' + r.stdout + r.stderr)

        run('build', ['lake', 'build', '+tests.PipelineNative'], ROOT)
        harness = output / 'Harness.lean'
        harness.write_text('import tests.PipelineNative\ndef main (args : List String) : IO Unit := '
                           'ClaferCompiler.Tests.PipelineNative.run args\n')
        classpath = os.pathsep.join(map(str, [output, runtime['classes'], runtime['jar']]))
        run('javac', [runtime['java'].with_name('javac'), '--release', '17', '-cp', classpath,
                      '-d', output, ROOT / 'scripts/oracles/AlloyTextBridge.java',
                      ROOT / 'scripts/oracles/AlloyArithmeticBridge.java'])

        def native(label, source, limits, candidate=None, mutation='none'):
            folder = output / label
            folder.mkdir()
            (folder / 'model.cfr').write_text(source)
            oracle.write(folder / 'bounds.json', limits)
            table = '-'
            if candidate is not None:
                table = folder / 'tables.rows'
                table.write_text(tables(candidate))
                oracle.write(folder / 'candidate.json', candidate)
            run(label, ['lake', 'env', 'lean', '--run', harness, folder / 'model.cfr',
                        folder / 'bounds.json', folder, table, mutation], ROOT)
            return folder

        def solve(label, items):
            folder = output / label
            folder.mkdir()
            manifest = []
            for i, (text, expected) in enumerate(items):
                (folder / f'case_{i}.als').write_text(text)
                manifest.append(dict(id=f'case_{i}', expected=expected, reference=False))
            oracle.write(folder / 'manifest.json', manifest)
            run(label, [runtime['java'], '-Xmx512m', '-cp', classpath,
                        'AlloyArithmeticBridge', folder], folder)
            return folder

        telematics = (ROOT / 'tests/fixtures/constraints/telematics.cfr').read_text()
        telematics_bounds = json.loads((ROOT / 'tests/fixtures/pipeline/telematics.bounds.json').read_text())
        definitions = [
            ('telematics', telematics, telematics_bounds, 'none'),
            ('version', 'a -> int\nb -> int\n[a >= b]\n', bounds([1,1,1,2],3,3), 'none'),
            ('display', 'box\n  item *\n[#box.item = 2]\n', bounds([1,1,2,0],4,3), 'none'),
            ('parent', 'abstract Node\n  child -> Node\n    [this = parent]\nleft : Node\nright : Node\n',
             bounds([1,2,2,1,1,0],5,5), 'none'),
            ('omitted', 'a -> int\n[a = 0]\n', bounds([1,1,1],2,2), 'none'),
            ('inherited', 'abstract Base\n  xor choice\n    a\n    b\nitem : Base\n',
             bounds([1,1,1,0,0,1],3), 'drop-inherited-group')]
        prepared = [native('seed-'+name, source, limits, mutation=mutation)
                    for name, source, limits, mutation in definitions]
        seed = solve('seed-analyzer', [(p.joinpath('generated.als').read_text(), True) for p in prepared])
        checks, results = [], []
        for index, ((name, source, limits, _), prep) in enumerate(zip(definitions, prepared)):
            spec = schema(prep)
            c = witness(seed / f'case_{index}.xml', spec)
            mapping = {d: (s, h-1, r-1) for d,s,h,r in rows(prep / 'mapping.rows')}
            if name == 'version':
                # The exact positive has a=1 and b=0, so reversing order changes truth.
                scalar = mapping[3][0]
                c['values'][scalar] = [[a, z] for z, a in enumerate(c['signatures'][scalar])]
                for d, z in [(1,1),(2,0)]:
                    c['fields'][mapping[d][2]] = [[c['signatures'][mapping[d][0]][0], c['values'][scalar][z][0]]]
            if name == 'omitted':
                scalar = mapping[2][0]
                c['values'][scalar][0][1] = 1
            original = native(name+'-original', source, limits, c)
            observed = original.joinpath('evaluation.rows').read_text().splitlines()
            expected = name not in ('omitted', 'inherited')
            self.assertEqual(observed[0], 'target '+str(expected).lower())
            self.assertEqual(observed[1], 'inherited '+str(name != 'inherited').lower())
            self.assertEqual(observed[2], 'numeric true')
            if name == 'telematics':
                self.assertEqual(len(observed[3:]), 12)
                self.assertTrue(all(line.endswith(' true') for line in observed[3:]))
                self.assertEqual(rows(original/'bodies.rows'), [[i,o] for i,o in enumerate([0,0,0,1,11,15,15,19,19,19,19,19])])
            original_text = original.joinpath('generated.als').read_text() + pin(c, spec)
            checks.append((original_text, expected))
            if name == 'telematics':
                results.append(dict(name=name, original=expected, bodies=12))
                continue
            changed_source, mutation = source, 'none'
            if name == 'version': changed_source = source.replace('>=', '<=')
            if name == 'display': changed_source = source.replace('= 2', '= 1')
            if name == 'parent': changed_source = source.replace('= parent', '= left')
            if name == 'omitted': mutation = 'drop-constraint:0'
            if name == 'inherited': mutation = 'drop-inherited-group'
            changed = native(name+'-mutated', changed_source, limits, c, mutation)
            self.assertEqual(changed.joinpath('evaluation.rows').read_text().splitlines()[0],
                             'target '+str(not expected).lower())
            changed_text = changed.joinpath('generated.als').read_text() + pin(c, spec)
            checks.append((changed_text, not expected))
            # Exact replay retains source, bounds, all tuples and scalar payloads.
            replay = native(name+'-replay', changed_source, limits, copy.deepcopy(c), mutation)
            self.assertEqual(replay.joinpath('generated.als').read_bytes(), changed.joinpath('generated.als').read_bytes())
            self.assertEqual(replay.joinpath('evaluation.rows').read_bytes(), changed.joinpath('evaluation.rows').read_bytes())
            checks.append((replay.joinpath('generated.als').read_text()+pin(c,spec), not expected))
            # Enumerate every object deletion. Each violates an explicit exact
            # original-declaration scope, so none remains a fitting candidate.
            # This is minimality under object deletion with these fixed bounds,
            # not a claim of global or source-syntax minimality.
            deletions = []
            for atom in c['signatures'][0]:
                witnesses = [d for d, (sig, _, _) in mapping.items()
                             if atom in c['signatures'][sig] and limits['declarations'][d]['exact']
                             and len(c['signatures'][sig]) == limits['declarations'][d]['size']]
                self.assertTrue(witnesses, (name, atom, 'deletion not ruled out by exact scope'))
                deletions.append(dict(atom=atom, violated_exact_declaration=min(witnesses)))
            oracle.write(replay/'minimization.json', dict(
                order='single object deletion; bounds fixed', deletion_minimal=True,
                checked=deletions, source_reduction='standalone mutation witness'))
            results.append(dict(name=name, original=expected, mutated=not expected,
                                replay=True, objects=len(c['signatures'][0]),
                                reduction='standalone source removes unrelated Appendix 6 declarations'))
        # A numeric exactly-one group must admit either unannotated child,
        # and reject neither/both with matching exact scopes. Compare the native
        # target evaluator, independent structural checker and actual Alloy.
        source = '1..1 Owner\n  a\n  b\n'
        for a, b in [(0, 0), (1, 0), (0, 1), (1, 1)]:
            label = f'numeric-choice-{a}-{b}'
            limits = bounds([1, 1, a, b], 2 + a + b)
            prep = native(label + '-prepare', source, limits)
            spec = schema(prep)
            mapping = {d: (s, h-1, r-1) for d,s,h,r in rows(prep / 'mapping.rows')}
            self.assertEqual(set(mapping), {0, 1, 2, 3})
            heads = [[0], [1], [2] if a else [], [2 + a] if b else []]
            c = dict(signatures=[[] for _ in spec['signatures']],
                     fields=[[] for _ in spec['fields']],
                     values=[[] for _ in spec['signatures']])
            for d, atoms in enumerate(heads):
                sig, field, _ = mapping[d]
                while sig is not None:
                    c['signatures'][sig] = sorted(set(c['signatures'][sig] + atoms))
                    sig = spec['signatures'][sig]['parent']
                if d:
                    c['fields'][field] = [[0 if d == 1 else 1, x] for x in atoms]
            evaluated = native(label, source, limits, c)
            expected = a + b == 1
            self.assertEqual(evaluated.joinpath('evaluation.rows').read_text().splitlines(),
                             ['target ' + str(expected).lower(),
                              'inherited ' + str(expected).lower(), 'numeric true'])
            checks.append((evaluated.joinpath('generated.als').read_text() + pin(c, spec), expected))
            cli_text = evaluated / 'cli.als'
            run(label + '-cli', [executable, 'compile-source', evaluated / 'model.cfr',
                                 '--bounds', evaluated / 'bounds.json', '--output', cli_text])
            checks.append((cli_text.read_text() + pin(c, spec), expected))
            results.append(dict(name=label, accepted=expected, exact_counts=[1, 1, a, b],
                                native_cli=True))
        solve('exact-analyzer', checks)
        oracle.write(output / 'results.json', results)
        oracle.write(output / 'evidence-index.json', {str(p.relative_to(output)): oracle.digest(p)
                     for p in sorted(output.rglob('*')) if p.is_file()})


if __name__ == '__main__':
    unittest.main()
