"""Fresh revision delta runs; bounded evidence is distinct from source equivalence."""
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import copy
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts/oracles'))
import oracle
import pr113
import pr113_protocol as protocol
import temporal


# [utest->req~compiler-temporal-oracles~1]
class PR113Oracles(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for name in ('CLAFER_PR113_TOOLS','CLAFER_TEMPORAL_TOOLS'):
            if not os.environ.get(name): raise RuntimeError('Prepare and set '+name+'; no skipped candidate gates')
        cls.tools = pr113.load_tools(os.environ['CLAFER_PR113_TOOLS'])
        cls.tools['old'] = temporal.load_tools(os.environ['CLAFER_TEMPORAL_TOOLS'])
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='pr113-',dir=parent))
        print('PR113 oracle evidence: '+str(cls.output),flush=True)
        cls.cases = pr113.read(pr113.CORPUS)['cases']
        def run(case):
            return case['id'], pr113.run_case(cls.tools,case,cls.output/case['id'])
        cpus = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else (os.cpu_count() or 1)
        with ThreadPoolExecutor(max_workers=max(1, min(3, cpus))) as pool:
            cls.results = dict(pool.map(run,cls.cases))
        oracle.write(cls.output/'summary.json',cls.results)

    def generation(self, name, form='original'):
        return pr113.read(self.output/name/form/'generation.json')

    def trace(self, name, form='original-query-0'):
        return pr113.read(self.output/name/form/'result.json')['trace']

    def test_complete_inventory_and_source_delta(self):
        source = self.tools['build'].parent/'compiler'
        upstream = {c['entry'] for c in self.cases if c['origin']=='haskell'}
        self.assertEqual({p.name for p in (source/'test/positive').glob('tmp_*.cfr')},upstream)
        self.assertEqual(65,len(upstream))
        delta = pr113.read(pr113.CORPUS.parent/'delta.json')
        self.assertEqual(10,len(delta['commits']))
        self.assertEqual(delta['candidate'],self.tools['tools']['profile']['haskell_commit'])
        old_source = self.tools['old']['build'].parent/'compiler'
        for entry in delta['reviewed_sources']:
            for which,tree in [('base',old_source),('candidate',source)]:
                path = tree/entry['path']
                with self.subTest(path=entry['path'],revision=which):
                    if entry[which] is None: self.assertFalse(path.exists())
                    else: self.assertEqual(entry[which],oracle.digest(path))

    def test_fresh_corpus_fixed_points_and_bounded_queries(self):
        for case in self.cases:
            with self.subTest(case=case['id']):
                result = self.results[case['id']]
                self.assertEqual(case.get('expected_status','ok'),result['status'],result)
                if result['status']!='ok':
                    self.assertFalse(result['checks'])
                    continue
                self.assertTrue(result['fixed_point'])
                self.assertTrue(result['agreement'])
                if 'expected' in case: self.assertTrue(result['expected_match'])
                if 'old_expected' in case:
                    self.assertEqual(case['old_expected'],result['historical']['outcome'])
                if len(result['checks'])>1: self.assertTrue(result['assertions_nonvacuous'])
                g = self.generation(case['id'])
                if case['origin']=='local': self.assertEqual(3 if case['id']=='names' else 4,g['trace_length'])
                if case['id']!='tmp_TrafficLight5': self.assertEqual('unsupported',g['outputs']['Choco']['status'])
                for n,check in enumerate(result['checks']):
                    a = pr113.read(self.output/case['id']/('original-query-'+str(n))/'request.json')
                    b = pr113.read(self.output/case['id']/('explicit-query-'+str(n))/'request.json')
                    self.assertEqual(dict(a,command_index=check['explicit_index']),b)
                    self.assertEqual(g['trace_length'],a['max_steps'])
                    self.assertEqual(1,a['min_steps'])
                    if case['origin']=='haskell': self.assertEqual(protocol.request(g,check['original_index']),a)

    def test_modifier_witnesses_check_identities_images_and_bag_counts(self):
        for inherited in (False,True):
            prefix = 'inherited' if inherited else 'direct'
            ref = 'this/Link/Link_ref' if inherited else 'this/head/head_ref'
            def projection(frame):
                heads = {t[-1] for t in frame['fields']['this/owner/r_head']}
                refs = {h:t for h,t in frame['fields'][ref] if h in heads}
                self.assertEqual(heads,set(refs))
                return heads,refs
            for scenario,mod in [('swap','target'),('change','ref'),('replace','both'),('replace','reverse'),('bag','both'),('bag','reverse')]:
                with self.subTest(inherited=inherited,scenario=scenario,modifier=mod):
                    frames = self.trace(prefix+'-'+scenario+'-'+mod)['frames']
                    a,ra = projection(frames[0]); b,rb = projection(frames[1])
                    if scenario=='swap':
                        self.assertEqual(a,b)
                        self.assertEqual(set(ra.values()),set(rb.values()))
                        self.assertTrue(all(ra[h]!=rb[h] for h in a))
                    else:
                        self.assertTrue(a.isdisjoint(b))
                        if scenario=='change': self.assertNotEqual(set(ra.values()),set(rb.values()))
                        else: self.assertEqual(set(ra.values()),set(rb.values()))
                        if scenario=='bag':
                            self.assertEqual(3,len(a)); self.assertEqual(3,len(b))
                            self.assertEqual(2,len(set(ra.values())))
                            self.assertNotEqual(Counter(ra.values()),Counter(rb.values()))

    def test_old_pattern_traces_are_the_distinguishing_valuations(self):
        def values(case,field):
            return [bool(f['fields']['this/root/r_c0_'+field]) for f in self.trace(case,'historical')['frames']]
        self.assertEqual([True,False,False,False],values('late-trigger','q'))
        self.assertEqual([False,True,False,False],values('late-trigger','p'))
        self.assertEqual([False,False,False,True],values('late-trigger','r'))
        self.assertFalse(any(values('late-trigger','s')))
        self.assertEqual([True,False,True,False],values('first-opener','q'))
        self.assertEqual([False,True,False,False],values('first-opener','p'))
        self.assertEqual([False,False,False,True],values('first-opener','s'))

    def test_names_empty_extent_and_meaningful_assertion_counterexample(self):
        g = self.generation('names')
        for name in ('sig','show','r_x','x_ref'): self.assertNotEqual(name,g['names'][name])
        for name in ('a_prime','a_prime__2','left__same','right__same'): self.assertIn(name,g['names'])
        inspected = pr113.read(self.output/'names/original/inspection.json')
        self.assertEqual(['this/'+g['names']['sig']], inspected['fields']['this/x/x_ref']['targets'])
        self.assertIn('this/'+g['names']['x_ref'], inspected['signatures'])
        trace = self.trace('names','original-query-2')
        self.assertTrue(all(not f['signatures']['this/Empty'] for f in trace['frames']))
        self.assertTrue(all(not f['fields']['this/root/r_'+g['names']['show']] for f in trace['frames']))
        self.assertEqual('sat',self.results['names']['checks'][2]['original_outcome'])

    def test_closed_modifier_arrays_and_mapping_mutations(self):
        g = self.generation('direct-swap-both')
        for key in ('_finalReferences','_refModifiers'):
            for bad in (None,'FinalRef',['Unknown'],[True],[{'tag':'FinalRef'}]):
                im = copy.deepcopy(g['post_analysis']); row = protocol.declarations(im)['head']
                obj = row['_modifiers'] if key=='_finalReferences' else row['_reference']
                obj[key] = bad
                with self.subTest(key=key,bad=bad),self.assertRaises(ValueError): protocol.declarations(im)
            for mode in ('missing','old','mixed'):
                im = copy.deepcopy(g['post_analysis']);row=protocol.declarations(im)['head']
                obj = row['_modifiers'] if key=='_finalReferences' else row['_reference']
                if mode!='mixed': del obj[key]
                if mode!='missing': obj['_finalReference' if key=='_finalReferences' else '_refModifier']='FinalRef'
                with self.subTest(mode=mode),self.assertRaises(ValueError): protocol.declarations(im)
        for mode in ('missing','extra','alias','renamed','dangling','duplicate_json'):
            bad = copy.deepcopy(g)
            if mode=='missing': del bad['names']['head']
            if mode=='extra': bad['names']['foreign']='foreign'
            if mode=='alias': bad['names']['head']=bad['names']['owner']
            if mode=='renamed': protocol.declarations(bad['backend_ir'])['head']['_parentUID']='root'
            if mode=='dangling': protocol.declarations(bad['post_analysis'])['head']['_parentUID']='foreign'
            if mode=='duplicate_json': bad['json']='{"iModule":null,'+bad['json'][1:]
            with self.subTest(mode=mode),self.assertRaises(ValueError): protocol.generation(bad)
        observed = pr113.read(self.output/'direct-swap-both/original/inspection.json')
        for mode in ('field','owner','endpoint','signature'):
            bad = copy.deepcopy(observed)
            if mode=='field': del bad['fields']['this/head/head_ref']
            if mode=='owner': bad['fields']['this/head/head_ref']['owner']='this/owner'
            if mode=='endpoint': bad['fields']['this/head/head_ref']['targets']=['this/owner']
            if mode=='signature': bad['signatures']['this/head']['parent']='this/Target'
            with self.subTest(mode=mode),self.assertRaises(ValueError): protocol.layout(g,bad)

    def test_fresh_replay_and_every_artifact_tamper(self):
        bundle = self.output/'direct-swap-target'
        result = pr113.replay(self.tools,bundle,self.output/'replayed')
        self.assertEqual('ok',result['status'])
        # Every indexed artifact is checked, including scopes, renamed IR and old discrepancy.
        for name in pr113.read(bundle/'evidence-index.json'):
            with self.subTest(artifact=name),tempfile.TemporaryDirectory() as scratch:
                target = Path(scratch)/'bundle';shutil.copytree(bundle,target)
                with (target/name).open('ab') as out: out.write(b' ')
                with self.assertRaisesRegex(ValueError,'Replay artifact changed'):
                    pr113.replay(self.tools,target,Path(scratch)/'replay')

    def test_unsupported_backends_have_no_solver_claim(self):
        for name in ('unsupported-real','unsupported-double'):
            g = self.generation(name)
            self.assertEqual('generated',g['outputs']['JSON']['status'])
            for mode in ('Alloy','Choco','Clafer'): self.assertEqual('unsupported',g['outputs'][mode]['status'])
            self.assertFalse((self.output/name/'original-query-0').exists())
