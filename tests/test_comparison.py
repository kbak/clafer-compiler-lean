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
                members=[['root',0], ['c0_Target',1], ['c0_refs',2], ['c0_refs',3]],
                containment=[['c0_Target',[0,1]], ['c0_refs',[0,2]], ['c0_refs',[0,3]]],
                references=[['c0_refs',[2,1]], ['c0_refs',[3,1]]])


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
        for name in ('bag','set','groups','overlap','inheritance','cycles','shadowing'):
            item = next(i for i in items if i['id'] == name)
            source = oracle.fixture_path(item)
            capture = cls.output / ('capture-' + name)
            r = oracle.capture_case(source, item['bounds'], capture, cls.runtime.api,
                                    cls.runtime.exporter, cls.runtime.build)
            if r['status'] != 'admitted': raise RuntimeError(r)
            cls.bundles[name] = capture / 'capture'
        capture = cls.output / 'capture-tiny'
        r = oracle.capture_case(ROOT / 'tests/fixtures/comparison/tiny.cfr', {'root':1,'c0_A':1},
            capture, cls.runtime.api, cls.runtime.exporter, cls.runtime.build)
        if r['status'] != 'admitted': raise RuntimeError(r)
        cls.bundles['tiny'] = capture / 'capture'

    def compare(self, name, candidate, label, **kwargs):
        result = comparison.compare(self.runtime, self.bundles[name],
            self.runtime.api['protocol'].encoded(candidate), self.output / label, **kwargs)
        return result

    def test_actual_decode_and_negative_mutations(self):
        candidate = bag_candidate()
        r = self.compare('bag', candidate, 'bag')
        self.assertEqual(r['category'], 'agree_satisfies', r)
        decoded = json.loads((self.output / 'bag/decoded.json').read_text())
        self.assertEqual(len(self.runtime.relation.occurrences(decoded)), 2)
        self.assertEqual(len({row[1][0] for row in decoded['references']}), 2)
        self.assertEqual(self.compare('set', candidate, 'set')['category'], 'agree_violates')
        for mutation, category in [('collapse-occurrence','pin_decode_failure'),
                                   ('swap-endpoints','checker_accepts_compiler_rejects'),
                                   ('reject-all','checker_accepts_compiler_rejects')]:
            r = self.compare('bag', candidate, mutation, mutation=mutation)
            self.assertEqual(r['category'], category, r)
        too_many = dict(objects=[0,1,2,3],root=0,
            members=[['root',0], *[['c0_Target',n] for n in (1,2,3)]],
            containment=[['c0_Target',[0,n]] for n in (1,2,3)], references=[])
        self.assertEqual(self.compare('bag',too_many,'cardinality-negative')['category'], 'agree_violates')
        self.assertEqual(self.compare('bag',too_many,'drop-cardinality',mutation='drop-cardinality')['category'],
                         'compiler_accepts_checker_rejects')
        group = dict(objects=[0,1],root=0,members=[['root',0],['c0_box',1]],
                     containment=[['c0_box',[0,1]]],references=[])
        self.assertEqual(self.compare('groups',group,'group-negative')['category'], 'agree_violates')
        self.assertEqual(self.compare('groups',group,'drop-group',mutation='drop-group')['category'],
                         'compiler_accepts_checker_rejects')
        overlap = dict(objects=[0,1],root=0,members=[['root',0],['c0_x',1],['c0_y',1]],
                       containment=[['c0_x',[0,1]],['c0_y',[0,1]]],references=[])
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
                members=[['root',0],['c0_Base',1],['c0_Middle',1],['c0_left',1]],
                containment=[['c0_left',[0,1]]],references=[]),
            'cycles': dict(objects=[0,1,2],root=0,
                members=[['root',0],['c0_a',1],['c0_b',2]],
                containment=[['c0_a',[0,1]],['c0_b',[0,2]]],
                references=[['c0_a',[1,2]],['c0_b',[2,1]]]),
            'shadowing': dict(objects=[0,1,2,3,4,5],root=0,
                members=[['root',0],['c0_left',1],['c0_right',2],['c0_Base',3],
                         ['c0_same',3],['c1_same',4],['c0_links',5]],
                containment=[['c0_left',[0,1]],['c0_right',[0,2]],['c0_same',[1,3]],
                             ['c1_same',[2,4]],['c0_links',[2,5]]],
                references=[['c0_links',[5,3]]])}
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
