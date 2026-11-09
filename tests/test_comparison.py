"""Real three-way candidate tests, complete tiny domain, seeds and mutation replay."""
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/comparison'))
import compare as comparison
oracle = comparison.oracle


def bag_candidate():
    return dict(objects=[0,1,2,3], root=0,
                members=[['root',0], ['Target',1], ['refs',2], ['refs',3]],
                containment=[['Target',[0,1]], ['refs',[0,2]], ['refs',[0,3]]],
                references=[['refs',[2,1]], ['refs',[3,1]]])


# [utest->req~compiler-differential~1]
# [utest->req~compiler-instance-decode~1]
class ComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tools = os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools: raise RuntimeError('CLAFER_ORACLE_TOOLS required')
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='three-way-', dir=parent))
        print(f'Three-way evidence: {cls.output}', flush=True)
        cls.runtime = comparison.Runtime(tools, cls.output / 'runtime')
        cls.bundles = {}
        items = json.loads(oracle.CORPUS.read_text())['fixtures']
        for name in ('bag','set','groups','overlap','inheritance','cycles','shadowing',
                     'collisions','renamed-inheritance'):
            item = next(i for i in items if i['id'] == name)
            source = oracle.fixture_path(item)
            capture = cls.output / ('capture-' + name)
            r = oracle.capture_case(source, item['bounds'], capture, cls.runtime.api,
                                    cls.runtime.exporter, cls.runtime.build)
            if r['status'] != 'admitted': raise RuntimeError(r)
            cls.bundles[name] = capture / 'capture'
        capture = cls.output / 'capture-tiny'
        r = oracle.capture_case(ROOT / 'tests/fixtures/comparison/tiny.cfr', {'root':1,'A':1},
            capture, cls.runtime.api, cls.runtime.exporter, cls.runtime.build)
        if r['status'] != 'admitted': raise RuntimeError(r)
        cls.bundles['tiny'] = capture / 'capture'

    def compare(self, name, candidate, label, **kwargs):
        result = comparison.compare(self.runtime, self.bundles[name],
            self.runtime.api['protocol'].encoded(candidate), self.output / label, **kwargs)
        if result['category'].startswith('agree_'):
            self.assertTrue(result['complete'], result)
        return result

    def test_actual_decode_and_negative_mutations(self):
        candidate = bag_candidate()
        r = self.compare('bag', candidate, 'bag')
        self.assertEqual(r['category'], 'agree_satisfies', r)
        decoded = json.loads((self.output / 'bag/decoded.json').read_text())
        self.assertEqual(len(self.runtime.relation.occurrences(decoded)), 2)
        self.assertEqual(len({row[1][0] for row in decoded['references']}), 2)
        self.assertEqual(self.compare('set', candidate, 'set')['category'], 'agree_violates')
        distinct = copy.deepcopy(candidate)
        distinct['objects'].append(4)
        distinct['members'].append(['Target', 4])
        distinct['containment'].append(['Target', [0, 4]])
        distinct['references'][1] = ['refs', [3, 4]]
        self.assertEqual(self.compare('set', distinct, 'set-distinct')['category'],
                         'agree_satisfies')
        print('Bag: two heads sharing one target pass. Set: the same candidate fails '
              'target uniqueness; distinct targets pass.', flush=True)
        for mutation, category in [('collapse-occurrence','pin_decode_failure'),
                                   ('swap-endpoints','checker_accepts_compiler_rejects'),
                                   ('reject-all','checker_accepts_compiler_rejects')]:
            r = self.compare('bag', candidate, mutation, mutation=mutation)
            self.assertEqual(r['category'], category, r)
        too_many = dict(objects=[0,1,2,3],root=0,
            members=[['root',0], *[['Target',n] for n in (1,2,3)]],
            containment=[['Target',[0,n]] for n in (1,2,3)], references=[])
        self.assertEqual(self.compare('bag',too_many,'cardinality-negative')['category'], 'agree_violates')
        self.assertEqual(self.compare('bag',too_many,'drop-cardinality',mutation='drop-cardinality')['category'],
                         'compiler_accepts_checker_rejects')
        group = dict(objects=[0,1],root=0,members=[['root',0],['box',1]],
                     containment=[['box',[0,1]]],references=[])
        self.assertEqual(self.compare('groups',group,'group-negative')['category'], 'agree_violates')
        self.assertEqual(self.compare('groups',group,'drop-group',mutation='drop-group')['category'],
                         'compiler_accepts_checker_rejects')
        overlap = dict(objects=[0,1],root=0,members=[['root',0],['x',1],['y',1]],
                       containment=[['x',[0,1]],['y',[0,1]]],references=[])
        self.assertEqual(self.compare('overlap',overlap,'overlap-negative')['category'], 'agree_violates')
        r = self.compare('overlap',overlap,'drop-disjointness',mutation='drop-disjointness')
        self.assertEqual(r['category'], 'compiler_accepts_checker_rejects', r)
        # Exact replay rechecks all input/output digests and current source/tool identity.
        r = comparison.replay(self.runtime,self.output/'bag',self.output/'bag-replay')
        self.assertEqual(r['category'],'agree_satisfies')
        comparison.run([sys.executable, ROOT/'scripts/comparison/compare.py', 'replay',
            '--tools',self.runtime.tools,self.output/'bag',self.output/'cli-replay'],
            self.output,'cli-replay',timeout=45)
        self.assertEqual(json.loads((self.output/'cli-replay/result.json').read_text())['category'],
                         'agree_satisfies')
        m = comparison.minimize(self.runtime,self.output/'reject-all',self.output/'minimized')
        self.assertTrue(m['deletion_minimal'])
        self.assertEqual(m['category'],'checker_accepts_compiler_rejects')
        shutil.copytree(self.output/'bag',self.output/'tampered')
        (self.output/'tampered/decoded.json').write_text('{}')
        with self.assertRaisesRegex(ValueError,'identity changed'):
            comparison.replay(self.runtime,self.output/'tampered',self.output/'tampered-replay')

    def test_complete_tiny_domain_and_seeded_generation(self):
        p = self.runtime.api['protocol']
        core, meta = p.import_bundle(self.bundles['tiny'])
        candidates = list(self.runtime.candidates.domain(core,meta['bounds']))
        self.assertEqual(len(candidates),4)
        results = [self.compare('tiny',c,f'exhaustive-{i}',search=dict(mode='exhaustive',index=i))
                   for i,c in enumerate(candidates)]
        self.assertEqual([r['category'] for r in results],
                         ['agree_satisfies','agree_violates','agree_violates','agree_satisfies'])
        core, meta = p.import_bundle(self.bundles['bag'])
        generated = list(self.runtime.candidates.generated(core,meta['bounds'],120021,6))
        self.assertEqual(generated,list(self.runtime.candidates.generated(core,meta['bounds'],120021,6)))
        for i,c in enumerate(generated):
            r = self.compare('bag',c,f'seeded-{i}',search=dict(mode='seeded',seed=120021,count=6,index=i))
            self.assertTrue(r['complete'],r)
            self.assertIn(r['category'],('agree_satisfies','agree_violates'),r)
        # Malformed bytes are retained verbatim; no solver verdict is fabricated.
        raw = b'{"root":0,"root":1}'
        r = comparison.compare(self.runtime,self.bundles['bag'],raw,self.output/'malformed')
        self.assertEqual(r['category'],'malformed')
        self.assertIsNone(r['compiler'])
        self.assertEqual((self.output/'malformed/candidate.json').read_bytes(),raw)
        r = self.compare('bag',bag_candidate(),'unsupported-width',bitwidth=1)
        self.assertEqual(r['category'],'unsupported')
        self.assertFalse(r['complete'])

    def test_inheritance_cycles_and_shadowed_names(self):
        fixtures = {
            'inheritance': dict(objects=[0,1],root=0,
                members=[['root',0],['Base',1],['Middle',1],['left',1]],
                containment=[['left',[0,1]]],references=[]),
            'cycles': dict(objects=[0,1,2],root=0,
                members=[['root',0],['a',1],['b',2]],
                containment=[['a',[0,1]],['b',[0,2]]],
                references=[['a',[1,2]],['b',[2,1]]]),
            'shadowing': dict(objects=[0,1,2,3,4,5],root=0,
                members=[['root',0],['left',1],['right',2],['Base',3],
                         ['left__same',3],['right__same',4],['links',5]],
                containment=[['left',[0,1]],['right',[0,2]],['left__same',[1,3]],
                             ['right__same',[2,4]],['links',[2,5]]],
                references=[['links',[5,3]]])}
        for name,c in fixtures.items():
            r=self.compare(name,c,name,bitwidth=10)
            self.assertEqual(r['category'],'agree_satisfies',r)
            decoded=json.loads((self.output/name/'decoded.json').read_text())
            self.assertIsNotNone(self.runtime.relation.isomorphism(c,decoded))
        # Declared root identity is pinned even for a semantic negative.
        c=dict(objects=[0,1],root=1,members=[['root',0]],containment=[],references=[])
        r=self.compare('tiny',c,'wrong-root')
        self.assertEqual(r['category'],'agree_violates',r)

    def test_strict_decoder_and_timeout(self):
        # This test is independent of method execution order.
        r = self.compare('bag',bag_candidate(),'decoder-base')
        self.assertEqual(r['category'],'agree_satisfies',r)
        spec = json.loads((self.output/'decoder-base/layout.json').read_text())
        good = r['compiler']['witness']
        mutations=[]
        x=copy.deepcopy(good);x['signatures']['unexpected']=[];mutations.append(x)
        x=copy.deepcopy(good);x['signatures']['cc0'].append(x['signatures']['cc0'][0]);mutations.append(x)
        x=copy.deepcopy(good);x['signatures']['cc4']=['absent'];mutations.append(x)
        x=copy.deepcopy(good);x['fields']['cc9'][0].append('extra');mutations.append(x)
        x=copy.deepcopy(good);x['fields']['cc9'].append(x['fields']['cc9'][0]);mutations.append(x)
        x=copy.deepcopy(good);x['fields']['cc9'][0].reverse();mutations.append(x)
        for witness in mutations:
            with self.assertRaises(ValueError): comparison.witness_tables(witness,spec)
        # Exercise the actual process deadline on a deliberately stalled executable.
        stalled=self.output/'stalled-java'
        stalled.write_text('#!/bin/sh\nexec sleep 3\n');stalled.chmod(0o755)
        timed=self.output/'timeout';timed.mkdir()
        with patch.dict(self.runtime.alloy,java=stalled):
            result=comparison.solve(self.runtime,timed,1,512)
        self.assertEqual(result['status'],'timeout')
        self.assertIsNone(result.get('outcome'))

    def test_057_names_and_unused_abstracts(self):
        p = self.runtime.api['protocol']
        core, meta = p.import_bundle(self.bundles['collisions'])
        ids = {d['uid']: i + 1 for i, d in enumerate(core['declarations'])}
        value = dict(objects=[0, *ids.values()], root=0,
            members=[['root',0], *[[u,i] for u,i in ids.items()]],
            containment=[[d['uid'],[0 if d['parent']=='root' else ids[d['parent']],ids[d['uid']]]]
                         for d in core['declarations']],
            references=[['sig',[ids['sig'],ids['x']]]])
        self.assertEqual(meta['signatures']['sig'], 'sig_1')
        self.assertIn('a_prime', ids)
        self.assertIn('a_prime__2', ids)
        for label, candidate, expected in [
                ('names-positive', value, 'agree_satisfies'),
                ('names-missing-ref', dict(value, references=[]), 'agree_violates')]:
            result = self.compare('collisions', candidate, label, bitwidth=10)
            self.assertEqual(result['category'], expected, result)
        decoded = p.loads((self.output/'names-positive/decoded.json').read_bytes())
        self.assertIsNotNone(self.runtime.relation.isomorphism(value, decoded))
        layout = p.loads((self.output/'names-positive/layout.json').read_bytes())
        # Native numeric names and Haskell's renamed symbols both decode to UIDs.
        self.assertEqual(set(layout['maps']), {'root', *ids})
        self.assertNotEqual(layout['maps']['sig']['signature'], meta['signatures']['sig'])
        field = layout['fields'][layout['maps']['sig']['references']]
        self.assertEqual(field['owner'], layout['maps']['sig']['signature'])
        self.assertEqual(field['target'], layout['maps']['x']['signature'])
        replay = comparison.replay(self.runtime, self.output/'names-positive', self.output/'names-replay')
        self.assertEqual(replay['category'], 'agree_satisfies', replay)

        value = dict(objects=[0,1,2,3],root=0,
            members=[['root',0],['plus',1],['x',1],['refs',2],['refs',3]],
            containment=[['x',[0,1]],['refs',[0,2]],['refs',[0,3]]],
            references=[['refs',[2,1]],['refs',[3,1]]])
        receipt = p.loads((self.bundles['renamed-inheritance']/'generation.json').read_bytes())
        self.assertEqual(receipt['scopes'], [['sig',0]])
        self.assertIn('0 sig_1', receipt['alloy'])
        unused = dict(objects=[0,1],root=0,members=[['root',0],['sig',1]],
                      containment=[],references=[])
        for label, candidate, expected in [
                ('renamed-inheritance-positive', value, 'agree_satisfies'),
                ('renamed-inheritance-missing-ref', dict(value, references=value['references'][:1]), 'agree_violates'),
                ('unused-abstract-negative', unused, 'agree_violates')]:
            result = self.compare('renamed-inheritance', candidate, label)
            self.assertEqual(result['category'], expected, result)
