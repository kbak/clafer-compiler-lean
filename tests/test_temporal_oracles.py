"""Actual temporal Haskell/Alloy runs, independent witnesses and operational failures."""
import copy
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts/oracles'))
import oracle
import temporal
import temporal_build


def targets(frame,field):
    return {row[-1] for row in frame['fields'][field]}


# [utest->req~compiler-temporal-oracles~1]
class TemporalOracles(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path=os.environ.get('CLAFER_TEMPORAL_TOOLS')
        if not path:
            raise RuntimeError('Prepare temporal.py tools and set CLAFER_TEMPORAL_TOOLS; no skipped temporal gates')
        cls.tools_path=Path(path)
        cls.tools=temporal.load_tools(path)
        parent=oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output=Path(tempfile.mkdtemp(prefix='temporal-',dir=parent))
        print('Temporal oracle evidence: '+str(cls.output),flush=True)
        cls.cases=temporal.read(temporal.CORPUS)['cases']
        cls.results={c['id']:temporal.run_case(cls.tools,c,cls.output/c['id']) for c in cls.cases}

    def test_actual_corpus_and_matched_check_run_budgets(self):
        self.assertGreaterEqual(len(self.cases),27)
        for case in self.cases:
            with self.subTest(case=case['id']):
                result=self.results[case['id']]
                self.assertEqual('ok',result['status'],result)
                self.assertEqual(case['expected'],result['outcome'])
                bundle=self.output/case['id']
                generation=temporal.read(bundle/'generation.json')
                self.assertEqual('tmp.als',generation['backend'])
                self.assertIn('AlloyLtl',generation['effective_options'])
                self.assertEqual(generation['alloy'],(bundle/'model.als').read_text())
                self.assertEqual(generation['json'],(bundle/'model.json').read_text())
                self.assertEqual(case['request']['identities'].keys(),
                    {s['signature'] for s in result['command']['scopes']})
                if result['command']['check']:
                    budget=dict(case['request'],command_index=0)
                    runs=[c for c in self.cases if c['path']==case['path'] and c['request']==budget]
                    self.assertTrue(runs,'Assertion must have a model run with identical budgets')
                    self.assertEqual('sat',self.results[runs[0]['id']]['outcome'])
                if result['outcome']=='sat':
                    self.assertTrue((bundle/'witness.xml').stat().st_size>0)
                    temporal.validate_trace(result['trace'],case['request'])

    def test_independent_distinguishing_witnesses(self):
        # These checks use the source obligations, not a re-evaluation of Alloy's formula.
        frames=self.results['stable-event-run']['trace']['frames']
        self.assertTrue(frames[0]['fields']['this/c0_machine/r_c0_waiting'])
        self.assertTrue(frames[1]['fields']['this/c0_machine/r_c0_done'])
        self.assertEqual(targets(frames[0],'this/root/r_c0_machine'),
                         targets(frames[1],'this/root/r_c0_machine'))
        trace=self.results['identity-scope-2']['trace']
        live=[targets(f,'this/root/r_c0_item') for f in trace['frames']]
        self.assertTrue(all(len(s)==1 for s in live))
        self.assertTrue(live[0].isdisjoint(live[1]))
        self.assertEqual(2,len(set.union(*live)))
        self.assertEqual('bounded_unsat',self.results['identity-scope-1']['outcome'])
        for id in ('cancelled-signs','negated-run'):
            frames=self.results[id]['trace']['frames']
            self.assertEqual(1,len(targets(frames[0],'this/root/r_c0_machine')))
            self.assertFalse(targets(frames[1],'this/root/r_c0_machine'))
            self.assertTrue(all(not f['fields']['this/c0_ctx/r_c0_error'] for f in frames))
        trace=self.results['fixed-parent-run']['trace']
        frames=trace['frames']
        first=targets(frames[0],'this/c0_box/r_c0_item')
        self.assertTrue(first)
        self.assertTrue(first.isdisjoint(targets(frames[1],'this/c0_box/r_c0_item')))
        self.assertLessEqual(first,targets(frames[2],'this/c0_box/r_c0_item'))
        parent=frames[0]['fields']['this/c0_item/p_c0_item']
        self.assertTrue(all(f['fields']['this/c0_item/p_c0_item']==parent for f in frames))
        # The global assertion fails on an actual transition, including the lasso edge.
        trace=self.results['replaced-2-global-check']['trace']
        frames=trace['frames']
        counterexamples=[]
        for i,frame in enumerate(frames):
            nxt=frames[i+1 if i+1<len(frames) else trace['loop']]
            a=frame['fields']['this/c0_sm/r_c0_a']
            go=frame['fields']['this/root/r_c0_go']
            if a and go and not nxt['fields']['this/c0_sm/r_c0_b']:
                counterexamples.append((frame,nxt))
                self.assertNotEqual(targets(frame,'this/root/r_c0_sm'),targets(nxt,'this/root/r_c0_sm'))
        self.assertTrue(counterexamples)
        frames=self.results['inherited-swap-mutable']['trace']['frames']
        a=frames[0]['fields']['this/c0_Link/c0_Link_ref']
        b=frames[1]['fields']['this/c0_Link/c0_Link_ref']
        self.assertEqual([x[0] for x in a],[x[0] for x in b])
        self.assertNotEqual([x[1] for x in a],[x[1] for x in b])
        for mod in ('final','finalref','finaltarget'):
            self.assertEqual('bounded_unsat',self.results['inherited-swap-'+mod]['outcome'])

    def test_replay_invokes_fresh_compiler_and_preserves_query(self):
        output=self.output/'replayed'
        result=temporal.replay(self.tools,self.output/'identity-scope-2',output)
        self.assertEqual(('ok','sat'),(result['status'],result['outcome']))
        self.assertEqual(temporal.read(self.output/'identity-scope-2'/'request.json'),
                         temporal.read(output/'request.json'))
        self.assertTrue((output/'capture-command.json').is_file())

    def test_all_receipt_artifacts_detect_tampering(self):
        source=self.output/'identity-scope-2'
        for name in ('input.cfr','model.als','model.json','generation.json','build.json','request.json','result.json','witness.xml'):
            with self.subTest(artifact=name),tempfile.TemporaryDirectory() as scratch:
                target=Path(scratch)/'bundle'
                shutil.copytree(source,target)
                with (target/name).open('ab') as f: f.write(b' ')
                with self.assertRaisesRegex(ValueError,'Replay artifact changed'):
                    temporal.replay(self.tools,target,Path(scratch)/'replay')

    def test_missing_or_changed_exporter_cannot_be_reused(self):
        with tempfile.TemporaryDirectory() as scratch:
            path=Path(scratch)/'tools.json'
            record=temporal.read(self.tools_path)
            record['exporter']=str(Path(scratch)/'missing-exporter')
            oracle.write(path,record)
            with self.assertRaises((OSError,ValueError)): temporal.load_tools(path)
            record['exporter']=str(Path(scratch)/'changed-exporter')
            Path(record['exporter']).write_text('#!/bin/sh\nexit 0\n')
            Path(record['exporter']).chmod(0o755)
            oracle.write(path,record)
            with self.assertRaisesRegex(ValueError,'exporter/build changed'): temporal.load_tools(path)

    def test_invalid_bounds_and_missing_signature_do_not_mean_unsat(self):
        request=copy.deepcopy(self.cases[0]['request'])
        for key,value in [('min_steps',0),('bitwidth',True),('max_steps',-1),('extra',1)]:
            bad=dict(request,**{key:value})
            with self.subTest(key=key),self.assertRaises(ValueError): temporal.request_valid(bad)
        with tempfile.TemporaryDirectory() as scratch:
            directory=Path(scratch)
            shutil.copyfile(self.output/'stable-run'/'model.als',directory/'model.als')
            del request['identities']['this/c0_sm']
            result=temporal.solve(self.tools['runtime'],self.tools['api'],directory,request)
            self.assertEqual('malformed',result['status'])
            self.assertIsNone(result['outcome'])

    def test_real_process_timeout_failure_and_missing_result(self):
        # Controlled substitute JVMs test orchestration, not a claimed SAT4J timeout.
        request=self.cases[0]['request']
        for body,expected in [('import time; time.sleep(5)','timeout'),
                              ('raise SystemExit(7)','error'),('pass','error')]:
            with self.subTest(body=body),tempfile.TemporaryDirectory() as scratch:
                directory=Path(scratch)
                substitute=directory/'java'
                substitute.write_text('#!'+sys.executable+'\n'+body+'\n')
                substitute.chmod(0o755)
                runtime=dict(self.tools['runtime'],java=substitute)
                result=temporal.solve(runtime,self.tools['api'],directory,request,timeout=1)
                self.assertEqual(expected,result['status'])
                self.assertNotIn(result.get('outcome'),('sat','bounded_unsat'))

    def test_mutated_trace_identity_parent_and_loop_are_rejected(self):
        case=next(c for c in self.cases if c['id']=='fixed-parent-run')
        original=self.results[case['id']]['trace']
        for mutation in ('loop','parent','inventory','scope'):
            trace=copy.deepcopy(original)
            request=copy.deepcopy(case['request'])
            if mutation=='loop': trace['loop']=trace['length']
            if mutation=='parent': trace['frames'][1]['fields']['this/c0_item/p_c0_item']=[]
            if mutation=='inventory': trace['inventory'].append('foreign$0')
            if mutation=='scope': request['identities']['this/c0_item']['count']=0
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                temporal.validate_trace(trace,request)

    def test_missing_gmp_build_error_is_actionable(self):
        # A controlled failed compiler process exercises retained build diagnostics.
        with tempfile.TemporaryDirectory() as scratch:
            directory=Path(scratch)
            command=[sys.executable,'-c',"print('gmp.h: No such file'); raise SystemExit(1)"]
            with self.assertRaisesRegex(RuntimeError,'libgmp-dev.*no Haskell gate skipped'):
                temporal_build.run_build([command],directory,os.environ,directory/'build.log')
            self.assertIn('gmp.h: No such file',(directory/'build.log').read_text())

    def test_known_gaps_are_not_positive_source_truth(self):
        gaps=temporal.read(temporal.CORPUS)['known_comparison_gaps']
        self.assertEqual({'response-between','precedence-after','finaltarget-image','richer-structure-arithmetic'},
                         {g['id'] for g in gaps})
        self.assertIn('source rejects',gaps[0]['haskell'])
