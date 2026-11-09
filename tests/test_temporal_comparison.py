"""Exact first-slice candidates, mutation sensitivity and replay boundaries."""
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts/comparison'))
import temporal_compare as tc


def declaration(id,name,parent,*,local=(0,1),reference=None):
    return dict(id=id,name=name,origin='root' if parent is None else 'user',parent=parent,
        super=None,reference=reference or dict(kind='basic'),isAbstract=False,
        localBounds=dict(lower=local[0],upper=local[1]),groupBounds=dict(lower=0,upper='*'),source=None,authored=None)


def fixture(body=None,surface=None,*,owner=2,live=None,loop=0,extra_machine=False,reference=None):
    ds=[declaration(0,'root',None,local=(0,'*')),declaration(1,'machine',0),
        declaration(2,'ctx',1),declaration(3,'error',2)]
    structure=dict(version='clafer-ir/1',profile='m1-effective',root=0,declarations=ds,
                   parentRanks=[0,1,2,3],superRanks=[0]*4,unused=[False]*4)
    attachments=[] if body is None else [dict(id=40,owner=owner,kind='constraint',body=body,source=None)]
    document=dict(version='clafer-behavioral-ir/1',profile='behavioral-core/1',structure=structure,attachments=attachments)
    source='machine ?\n  ctx ?\n    error ?\n'
    if surface is not None:source+='  '*owner+'[ '+surface+' ]\n'
    ids=[dict(id=0,type=0,parent=None),dict(id=1,type=1,parent=0),dict(id=2,type=2,parent=1),dict(id=3,type=3,parent=2)]
    if extra_machine:ids += [dict(id=4,type=1,parent=0),dict(id=5,type=2,parent=4)]
    if reference:
        ds.append(declaration(4,'refs',2,local=(0,'*'),reference=dict(kind=reference,target=3)))
        structure['parentRanks'].append(3);structure['superRanks'].append(0);structure['unused'].append(False)
        source+='    refs '+('->>' if reference=='bag' else '->')+' error *\n'
        ids += [dict(id=6,type=4,parent=2),dict(id=7,type=4,parent=2)]
    live=live or [[0,1,2,3]]
    frames=[dict(live=row,references=([[4,6,3],[4,7,3]] if reference and 6 in row else [])) for row in live]
    c=dict(version='clafer-behavioral-trace/1',profile='behavioral-core/1',root=0,length=len(frames),loop=loop,
           identities=ids,frames=frames,integerObservations=[])
    counts={d['id']:sum(d['id']==r['type'] for r in ids) for d in ds}
    bounds=dict(version='clafer-behavioral-bounds/1',objects=len(ids),bitwidth=8,minSteps=len(frames),maxSteps=len(frames),
                declarations=[dict(id=d,size=n,exact=True) for d,n in counts.items()])
    return dict(version='clafer-temporal-case/1',document=document,bounds=bounds,source=source,
                uids={str(d['id']):'root' if d['id']==0 else 'c0_'+d['name'] for d in ds},candidate=c,seed=78)

ERROR=['atom',['inhabited',['thisStep',['child',3]]]]


# [utest->req~compiler-temporal-comparison~1]
# [utest->req~compiler-temporal-decode~1]
# [utest->req~compiler-behavioral-cli~1]
class TemporalComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent=tc.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output=Path(tempfile.mkdtemp(prefix='temporal-comparison-',dir=parent))
        tools=os.environ.get('CLAFER_TEMPORAL_TOOLS')
        if not tools:raise AssertionError('CLAFER_TEMPORAL_TOOLS required')
        cls.runtime=tc.Runtime(tools,cls.output/'runtime')
        print(f'Exact temporal evidence: {cls.output}',flush=True)

    def compare(self,name,case,expected=None,directions=None):
        result=self.runtime.compare(case,self.output/name)
        self.assertEqual(result['status'],'complete',result)
        self.assertEqual(result['directions'],directions or [],result)
        if expected:self.assertEqual(result['source'],expected,result)
        return result

    def test_exact_lifetime_witnesses(self):
        cases=[
            ('event-later',['eventually',ERROR],'F error',[[0,1,2],[0,1,2,3]],1,'satisfied'),
            ('event-never',['eventually',ERROR],'F error',[[0,1,2]],0,'violated'),
            ('cancel',['eventually',ERROR],'F error',[[0,1,2],[0]],1,'satisfied'),
            ('cancel-negated',['not',['eventually',ERROR]],'!(F error)',[[0,1,2],[0]],1,'satisfied'),
            ('context-death',['eventually',ERROR],'F error',[[0,1,2],[0,1]],1,'violated'),
            ('reappear',['eventually',ERROR],'F error',[[0,1,2],[0],[0,1,2,3]],2,'satisfied'),
            ('loop-event',['next',ERROR],'X error',[[0],[0,1,2],[0,1,2,3]],1,'violated'),
            ('initial',['initially',ERROR],'initially error',[[0],[0,1,2,3]],0,'satisfied'),
            ('final',['finally',ERROR],'finally error',[[0,1,2,3],[0]],0,'satisfied'),
            ('always',['always',ERROR],'G error',[[0,1,2,3],[0]],1,'satisfied'),
            ('until',['strongUntil',['truth'],ERROR],'(some error || no error) U error',[[0,1,2],[0,1,2,3]],1,'satisfied'),
            ('weak',['weakUntil',['truth'],ERROR],'(some error || no error) W error',[[0,1,2]],0,'satisfied'),
        ]
        for name,body,surface,live,loop,expected in cases:
            with self.subTest(name=name):self.compare(name,fixture(body,surface,live=live,loop=loop),expected)

    def test_generated_trace_walkthrough(self):
        case=tc.temporal.read(ROOT/'tests/fixtures/behavioral-cli/case.json')
        output=self.output/'walkthrough'
        result=tc.walkthrough(self.runtime,case,output)
        self.assertEqual(result['status'],'complete',result)
        self.assertEqual(result['generation'],dict(status='ok',outcome='sat',source='satisfied'))
        self.assertEqual(result['rejections'],dict(truncated='malformed',metadata='malformed',loop='malformed'))
        raw=tc.temporal.read(output/'generation/result.json')['trace']
        supplied=tc.temporal.read(output/'generation/generated-trace.json')
        self.assertEqual(raw,supplied,'checker must receive the actual Analyzer output')
        self.assertFalse((output/'generation/fixed-trace.json').exists())
        self.assertNotIn('tc_Clock',(output/'generation/model.als').read_text())
        decoded=tc.temporal.read(output/'generation/candidate.json')
        self.assertIsNotNone(tc.isomorphism(decoded,case['candidate']))
        for name,truth in [('event-later',True),('event-never',False),('loop-edge',True),('altered-loop',False)]:
            with self.subTest(name=name):
                r=result['cases'][name]
                self.assertEqual(r['source'],'satisfied' if truth else 'violated')
                self.assertEqual(r['directions'],[])
                self.assertEqual(r['targets'],{target:dict(status='ok',outcome='sat' if truth else 'bounded_unsat')
                                              for target in ('compiler','haskell')})
                self.assertEqual(tc.temporal.read(output/(name+'-replay')/'result.json'),r)
                checked=tc.temporal.read(output/name/'source-result.json')
                self.assertEqual(checked['structural'],'satisfied')
                self.assertEqual(checked['attachments'],[dict(id=40,satisfied=truth)])
        loop=tc.temporal.read(output/'loop-edge/case.json')
        broken=tc.temporal.read(output/'altered-loop/case.json')
        self.assertEqual(loop['candidate']['loop'],1)
        self.assertEqual(broken['candidate']['loop'],2)
        broken['candidate']['loop']=1
        self.assertEqual(loop,broken,'only the final successor changes')
        persistent={r['id'] for r in decoded['identities'] if r['type'] in (0,1,2)}
        self.assertTrue(all(persistent <= set(f['live']) for f in loop['candidate']['frames']))
        tc.validate_bundle(output)

    def test_walkthrough_operational_failure_is_not_unsat(self):
        case=tc.temporal.read(ROOT/'tests/fixtures/behavioral-cli/case.json')
        with patch.object(tc.temporal,'solve',return_value=dict(status='timeout')), \
                patch.object(self.runtime,'check') as check, patch.object(self.runtime,'compare') as compare:
            result=tc.walkthrough(self.runtime,case,self.output/'walkthrough-timeout')
        self.assertEqual(result['status'],'inconclusive')
        self.assertEqual(result['generation'],dict(status='timeout',outcome=None))
        self.assertEqual(result['cases'],{})
        check.assert_not_called();compare.assert_not_called()

    def test_reference_occurrences(self):
        for mode,expected in [('bag','satisfied'),('set','violated')]:
            with self.subTest(mode=mode):
                self.compare(mode,fixture(live=[[0,1,2,3,6,7],[0],[0,1,2,3,6,7]],loop=1,reference=mode),expected)

    def test_seeded_negative_candidates(self):
        rng=random.Random(78)
        for i in range(4):
            live=[[0]+([1] if rng.randrange(2) else []) for _ in range(2)]
            for row in live:
                if 1 in row and rng.randrange(2):row.append(2)
                if 2 in row and rng.randrange(2):row.append(3)
            case=fixture(['eventually',ERROR],'F error',live=live,loop=rng.randrange(2))
            self.compare('seed-'+str(i),case)

    def test_replacement_and_frozen_identity(self):
        # A new context under the same still-live parent cannot discharge the old
        # context's obligation, even when the new context has an error immediately.
        c=fixture(['eventually',ERROR],'F error',live=[[0,1,2],[0,1,4,5]],loop=1)
        c['candidate']['identities'] += [dict(id=4,type=2,parent=1),dict(id=5,type=3,parent=4)]
        c['bounds']['objects']=6
        for d in c['bounds']['declarations']:
            if d['id'] in (2,3):d['size']=2
        self.compare('replacement-context',c,'violated')
        body=['quant','all',['thisStep',['child',1]],['next',['atom',['subset',['var',0],['extent',1]]]]]
        for name,second,expected in [('replaced',4,'violated'),('same',1,'satisfied')]:
            c=fixture(body,'all s : machine | X (s in machine)',owner=0,
                      live=[[0,1],[0,second]],loop=1,extra_machine=True)
            self.compare('frozen-'+name,c,expected)

    def test_strict_actual_trace_decoder(self):
        c=fixture(live=[[0,1,2,3,6,7],[0],[0,1,2,3,6,7]],loop=1,reference='bag')
        self.compare('decode-base',c,'satisfied')
        d=self.output/'decode-base'
        actual=tc.temporal.read(d/'compiler/result.json')['trace']
        expected=tc.temporal.read(d/'compiler/fixed-trace.json')
        trace=tc.project_clock(actual,expected)
        checked=self.runtime.check(d,trace,'valid-decoder')
        self.assertEqual(checked['status'],'satisfied')
        self.assertEqual(len(checked['trace']['frames'][0]['references']),2)
        self.assertEqual(len({r[2] for r in checked['trace']['frames'][0]['references']}),1)
        def altered(name,change):
            bad=copy.deepcopy(trace);change(bad)
            r=self.runtime.check(d,bad,'bad-'+name)
            self.assertEqual(r['status'],'malformed',(name,r))
        altered('loop',lambda t:t.update(loop=t['length']))
        altered('truncated',lambda t:t['frames'].pop())
        altered('foreign',lambda t:t['frames'][0]['fields']['this/cc0/cc1'].append(['foreign','foreign']))
        altered('duplicate',lambda t:t['inventory'].append(t['inventory'][0]))
        altered('duplicate-tuple',lambda t:t['frames'][0]['signatures']['this/cc0'].append(t['frames'][0]['signatures']['this/cc0'][0]))
        altered('parent',lambda t:t['frames'][1]['fields']['this/cc0/cc1'].pop())
        error_sig=next(row['signature'] for row in tc.temporal.read(d/'compilation.json')['declarations']
                       if row['id']==3)
        altered('static-type',lambda t:t['frames'][1]['signatures'][error_sig].clear())
        altered('schema',lambda t:t['fields']['this/cc0/cc1'].update(mutable=True))
        altered('unknown-table',lambda t:t['frames'][0]['fields'].update(unknown=[]))
        altered('arity',lambda t:t['frames'][0]['fields']['this/cc0/cc1'][0].append(t['inventory'][0]))
        altered('unknown-inventory',lambda t:t['inventory'].append('unused'))
        bad=copy.deepcopy(checked['trace']);bad['frames'][0]['references'].pop()
        self.assertIsNone(tc.isomorphism(checked['trace'],bad),'bag heads collapsed')
        bad=copy.deepcopy(checked['trace']);bad['loop']=0
        self.assertIsNone(tc.isomorphism(checked['trace'],bad),'different loop accepted')
        # Tuple order is immaterial; all observations use the same global map.
        permuted=copy.deepcopy(trace)
        permuted['inventory'].reverse()
        for frame in permuted['frames']:
            for tables in frame.values():
                for rows in tables.values():rows.reverse()
        self.assertIsNotNone(tc.isomorphism(checked['trace'],self.runtime.check(d,permuted,'permuted')['trace']))

    def test_global_identity_not_per_frame_or_stuttering(self):
        a=fixture(live=[[0,1],[0,1]],loop=1,extra_machine=True)['candidate']
        b=copy.deepcopy(a);b['frames'][1]['live']=[0,4]
        self.assertIsNone(tc.isomorphism(a,b))
        b=copy.deepcopy(a);b['length']=3;b['frames'].append(copy.deepcopy(b['frames'][1]))
        self.assertIsNone(tc.isomorphism(a,b))
        b=copy.deepcopy(a)
        rename={i['id']:100+i['id'] for i in b['identities']}
        b['root']=rename[b['root']]
        for i in b['identities']:
            i['id']=rename[i['id']]
            if i['parent'] is not None:i['parent']=rename[i['parent']]
        for f in b['frames']:f['live']=[rename[x] for x in f['live']]
        self.assertIsNotNone(tc.isomorphism(a,b))

    def test_replay_and_both_discrepancy_directions(self):
        positive=fixture()
        r=self.runtime.compare(positive,self.output/'source-only',mutation='reject-all')
        self.assertEqual((r['status'],r['directions']),('complete',['compiler:source-only']),r)
        negative=fixture(['eventually',ERROR],'F error',live=[[0,1,2]])
        r=self.runtime.compare(negative,self.output/'target-only',mutation='drop-attachments')
        self.assertEqual((r['status'],r['directions']),('complete',['compiler:target-only']),r)
        self.assertEqual(tc.replay(self.runtime.tools_path,self.output/'target-only',self.output/'replayed'),r)
        minimized=tc.minimize(self.runtime,self.output/'source-only',self.output/'minimized')
        self.assertTrue(minimized.get('deletion_minimal'),minimized)
        tc.replay_case(self.runtime,self.output/'minimized/minimal',self.output/'minimal-replayed')
        (self.output/'target-only/extra.json').write_text('{}')
        with self.assertRaisesRegex(ValueError,'artifact inventory'):
            tc.replay_case(self.runtime,self.output/'target-only',self.output/'tampered-replay')
        with patch.object(self.runtime,'solve',return_value=dict(status='timeout')):
            r=self.runtime.compare(positive,self.output/'timeout')
        self.assertEqual(r['status'],'inconclusive',r)
        self.assertEqual(r['directions'],[])
        self.assertEqual(r['targets']['compiler'],dict(status='timeout',outcome=None))
        unsupported=copy.deepcopy(positive);unsupported['candidate']['integerObservations']=[0]
        self.assertEqual(self.runtime.compare(unsupported,self.output/'primitive')['status'],'unsupported')
        malformed=copy.deepcopy(positive);malformed['candidate']['loop']=1
        self.assertEqual(self.runtime.compare(malformed,self.output/'bad-candidate')['status'],'malformed')

    def test_cli_protocol_and_constructor_transport(self):
        c=fixture();d=self.output/'cli';d.mkdir()
        tc.oracle.write(d/'bounds.json',c['bounds'])
        command=[self.runtime.compiler,'compile-behavioral-ir','input.json','--bounds','bounds.json',
                 '--output','output.json','--format','json','--diagnostics','json']
        def call(doc,*,raw=None):
            (d/'input.json').write_text(json.dumps(doc) if raw is None else raw)
            return subprocess.run(command,cwd=d,capture_output=True,timeout=20)
        p=self.runtime.compile(d,c['document'],c['bounds'])
        for _ in range(2):
            r=call(c['document']);self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual(tc.temporal.read(d/'output.json'),p)
        e=['atom',['inhabited',['this']]]
        forms=[['truth'],*[[op,e] for op in ('not','next','eventually','always','initially','finally')],
            *[[op,e,e] for op in ('and','or','implies','iff','xor','strongUntil','weakUntil')],['ite',e,e,e],
            *[['quant',q,['extent',1],['atom',['inhabited',['var',0]]]] for q in ('all','some','no','one','lone')],
            ['letSet',['extent',1],['atom',['equal',['var',0],['var',0]]]]]
        sets=[['empty'],['this'],['root'],['extent',1],
              ['thisStep',['parent']],['thisStep',['child',3]],['step',['deref',3],['empty']],
              *[[op,['this'],['empty']] for op in ('union','inter','diff')]]
        forms += [['atom',[op,s,s]] for s in sets for op in ('equal','subset')]
        for form in forms:
            r=call(fixture(form)['document'])
            self.assertEqual(r.returncode,0,(form,r.stderr))
        last=(d/'output.json').read_bytes()
        bad=[]
        for body in (['truth',1],['atom',['inhabited',['var',0]]],['atom',['inhabited',['extent',999]]]):
            bad.append((fixture(body)['document'],2,None))
        for body in (['integer',0],['atom',['less',0,1]],['quant','many',['empty'],e]):
            bad.append((fixture(body)['document'],3,None))
        doc=copy.deepcopy(c['document']);doc['profile']='behavioral-full/1';bad.append((doc,3,None))
        bad.append((doc,2,'{"version":"clafer-behavioral-ir/1","version":"duplicate"}'))
        raw=json.dumps(c['document']).replace('"root": 0','"root": 0e0')
        bad.append((doc,2,raw))
        for doc,code,raw in bad:
            r=call(doc,raw=raw)
            self.assertEqual(r.returncode,code,r.stderr)
            self.assertEqual((d/'output.json').read_bytes(),last)
            self.assertIn(json.loads(r.stderr)['category'],('malformed','unsupported'))
        for change,code in [(dict(minSteps=0),2),(dict(minSteps=2,maxSteps=1),2),
                            (dict(bitwidth=17),3),(dict(declarations=[]),2)]:
            tc.oracle.write(d/'bounds.json',c['bounds']|change)
            r=call(c['document'])
            self.assertEqual(r.returncode,code,r.stderr)
            self.assertEqual((d/'output.json').read_bytes(),last)
