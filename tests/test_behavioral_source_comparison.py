"""Full-source exact observations, replay, decoder and sensitivity gates."""
from concurrent.futures import ThreadPoolExecutor
import copy
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts/comparison'))
import behavioral_source as bs
from behavioral_source_cases import absence_cases, case, features, patterns
from behavioral_initializer_cases import initializers
import behavioral_haskell as bh


def case_workers():
    """Bound independent source cases with the existing regression worker setting."""
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else (os.cpu_count() or 1)
    requested = int(os.environ.get('CLAFER_TEST_JOBS', '2'))
    if requested < 1 or requested > 4:
        raise ValueError('CLAFER_TEST_JOBS must be between 1 and 4')
    return max(1, min(requested, cpus))


# [utest->req~compiler-behavioral-qualification~1]
# [utest->req~compiler-behavioral-integration~1]
class BehavioralSourceComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workers=case_workers()
        parent=bs.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output=Path(tempfile.mkdtemp(prefix='behavioral-source-',dir=parent))
        tools=os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools: raise AssertionError('CLAFER_ORACLE_TOOLS required')
        cls.runtime=bs.Runtime(tools,cls.output/'runtime')
        print(f'Full source evidence: {cls.output}',flush=True)

    # [utest->req~compiler-behavioral-elaboration~1]
    # [utest->req~compiler-full-behavioral-correctness~1]
    def test_hard_initializers(self):
        def compare(row):
            name, expected, c = row
            return name, expected, self.runtime.compare(c, self.output / ('initializer-' + name))
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results = list(pool.map(compare, initializers()))
        for name, expected, result in results:
            with self.subTest(name=name):
                self.assertEqual(result, dict(status='complete', source=expected,
                    target='sat' if expected == 'satisfied' else 'bounded_unsat', directions=[]))
        bs.oracle.write(self.output / 'initializer-results.json', results)

    # [utest->req~compiler-behavioral-partial-lowering~1]
    # [utest->req~compiler-full-behavioral-correctness~1]
    # [utest->req~compiler-trace-representation~1]
    def test_absent_reference_observations(self):
        fixtures=list(absence_cases())
        self.assertEqual(len({name for name,_,_ in fixtures}),len(fixtures))
        def compare(row):
            name,expected,c=row
            result=self.runtime.compare(c,self.output/('absence-'+name))
            return name,expected,result
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results=list(pool.map(compare,fixtures))
        for name,expected,result in results:
            with self.subTest(name=name):
                self.assertEqual(result,dict(status='complete',source=expected,
                    target='sat' if expected=='satisfied' else 'bounded_unsat',directions=[]))
        bs.oracle.write(self.output/'absence-results.json',results)
        # Exact comparison includes every stored scalar, even when unobservable.
        # Replaying a passing cancellation witness retains both frames and loop.
        name='absence-parent-cancel-True-inherited-True'
        answer=next(r for n,_,r in results if 'absence-'+n==name)
        self.assertEqual(bs.replay(self.runtime,self.output/name,self.output/'absence-replay'),answer)

    # [utest->req~compiler-behavioral-partial-lowering~1]
    def test_absent_divisor_admission(self):
        # Cancellation and a supplied disappearing trace do not relax the
        # existing conservative range admission of a possibly zero divisor.
        for negative in (False,True):
            body='!(1 / this = 1)' if negative else '1 / this = 1'
            c=case('P ?\n  c -> int ?\n    [X ('+body+')]\n',3,
                [(1,1,0),(2,2,1)],[[1,2],[]],values=[{2:1},{}],interval=(0,4))
            output=self.output/('absence-divisor-'+str(negative));output.mkdir()
            with self.assertRaises(subprocess.CalledProcessError):
                self.runtime.compile(output,c)
            self.assertIn('behavioral.possible-zero-divisor',
                (output/'compile-stderr.log').read_text())

    # [utest->req~compiler-behavioral-encoding~1]
    # [utest->req~compiler-full-behavioral-correctness~1]
    def test_generated_absence_obligations(self):
        # These are unconstrained solver witnesses, not fixed candidate queries.
        # Root persistence and initial presence make the negative model genuinely
        # contradictory throughout the selected bounds, rather than just ruling
        # out one supplied disappearing trace.
        for value_obligation in (False,True):
            source='c -> int ?\n  [X (no this)]\n'
            if value_obligation: source+='  [X (this = 3)]\n'
            source+='[initially some c]\n'
            c=case(source,2,[(1,1,0)],[[1],[]],interval=(0,4))
            output=self.output/('absence-generated-'+str(value_obligation));output.mkdir()
            p=self.runtime.compile(output,c)
            (output/'model.als').write_text(p['alloy'])
            request=dict(command_index=0,overall=1,bitwidth=p['bitwidth'],
                min_steps=p['minSteps'],max_steps=p['maxSteps'],identities=p['scopes'])
            answer=bs.temporal.solve(self.runtime.runtime,self.runtime.api,output,request,
                timeout=120,integer_fields=[bs.SCALAR])
            bs.oracle.write(output/'result.json',answer)
            self.assertEqual(answer['status'],'ok',answer)
            self.assertEqual(answer['outcome'],'bounded_unsat' if value_obligation else 'sat',answer)
            if not value_obligation:
                decoded=self.runtime.decode(output,answer['trace'],'generated-witness')
                self.assertEqual(bs.Observation(p,decoded).check()['status'],'satisfied')
                head=next(i['id'] for i in decoded['identities'] if i['type']==1)
                self.assertIn(head,decoded['frames'][0]['live'])
                self.assertNotIn(head,decoded['frames'][1]['live'])
                self.assertTrue(all(not f['references'] for f in decoded['frames']))
                self.assertTrue(all(len(f['values'])==len(decoded['identities']) for f in decoded['frames']))

    def test_full_feature_observations(self):
        fixtures=list(features())+list(patterns())
        self.assertEqual(len({name for name,_,_,_ in fixtures}),len(fixtures))
        def compare(row):
            name,rows,expected,c=row
            result=self.runtime.compare(c,self.output/name)
            return name,rows,expected,result
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results=list(pool.map(compare,fixtures))
        for name,rows,expected,result in results:
            with self.subTest(name=name):
                self.assertEqual(result['status'],'complete',result)
                self.assertEqual(result['directions'],[],result)
                self.assertEqual(result['source'],expected,result)
        bs.oracle.write(self.output/'coverage.json',[dict(name=name,rows=rows,expected=expected,result=result)
                                                    for name,rows,expected,result in results])

    def test_revision_qualified_haskell_observations(self):
        path=os.environ.get('CLAFER_058_TOOLS')
        self.assertTrue(path,'CLAFER_058_TOOLS required')
        tools=bh.pr113.load_tools(path)
        selected=[]
        for name,rows,expected,c in features():
            if name.startswith(('inherited-bag','inherited-set','group-','modifier-False-',
                                'equation-','property-check','controller-','identity-budget-')) or (
                    name.startswith('root-') and c['query']['kind'] != 'scenario'):
                selected.append((name,c))
            if name.startswith('modifier-True-'):
                # Reference inherited from an abstract; both modifiers authored
                # on the concrete occurrence, matching accepted PR113 witnesses.
                c=copy.deepcopy(c)
                first=c['source'].splitlines()[0]
                mods=first[len('abstract '):].split(' R ')[0]
                c['source']='abstract R ->> int\n'+mods+' r : R *\n'
                selected.append((name,c))
        def compare(row):
            name,c=row
            return name,bh.compare(self.runtime,tools,c,self.output/('haskell-'+name))
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results=list(pool.map(compare,selected))
        for name,answer in results:
            with self.subTest(name=name):
                # Accepted Structural.Keys requires inherited set uniqueness.
                # This pinned Haskell generator omits the concrete-fiber key.
                expected=['target-only'] if name=='inherited-set' else []
                self.assertEqual(answer['directions'],expected,answer)
                if name=='inherited-set':
                    self.assertEqual((answer['source'],answer['target']),('violated','sat'))
                if name=='equation-True':
                    self.assertEqual(bh.replay(self.runtime,tools,self.output/('haskell-'+name),
                        self.output/'haskell-replay'),answer)

    # [utest->req~compiler-behavioral-frontend~1]
    # [utest->req~compiler-temporal-oracles~1]
    def test_058_let_capture_and_reference_exclusions(self):
        tools=bh.pr113.load_tools(os.environ['CLAFER_058_TOOLS'])
        fixtures=bs.oracle.UPSTREAM/'tests/fixtures/temporal-let'
        for name in ('baseline','target','same-state','head','changing-set','rebirth',
                     'shadow','rename','rename-control'):
            source=(fixtures/(name+'.cfr')).read_text()
            if name in ('rename','rename-control'):
                c=case(source,3,[(1,1,0),(2,2,0)],[[1,2]]*4,
                       values=[{0:1,1:1,2:2}]*4,interval=(1,2))
            else:
                live=([[1],[],[1],[1]] if name=='rebirth' else
                      [[1],[],[],[]] if name=='changing-set' else [[1]]*4)
                values=[{0:1,1:1},{0:1,1:2},{0:1,1:2},{0:1,1:2}]
                if name=='shadow': values=[{0:1,1:1}]*4
                c=case(source,2,[(1,1,0)],live,values=values,interval=(1,2))
            with self.subTest(name=name):
                answer=self.runtime.compare(c,self.output/('let-'+name))
                self.assertEqual(answer,dict(status='complete',source='satisfied',target='sat',directions=[]))
                reference=bh.compare(self.runtime,tools,c,self.output/('haskell-let-'+name))
                excluded=name in ('target','changing-set','rebirth')
                self.assertEqual(reference['source'],'satisfied',reference)
                self.assertEqual(reference['target'],'bounded_unsat' if excluded else 'sat',reference)
                self.assertEqual(reference['directions'],['source-only'] if excluded else [],reference)
        # A small signed domain keeps nested capture/aggregate expansion finite
        # enough for this exact strict-definedness witness (see issue #132).
        source=('v -> int ?\n[initially (some v && X no v)]\n'
                '[initially (let old = v in X (let unused = sum old in some root))]\n')
        c=case(source,2,[(1,1,0)],[[1],[]],interval=(0,0),width=2)
        answer=self.runtime.compare(c,self.output/'let-unused-partial')
        self.assertEqual(answer,dict(status='complete',source='undefined',target='bounded_unsat',directions=[]))
        reference=bh.compare(self.runtime,tools,c,self.output/'haskell-let-unused-partial')
        self.assertEqual((reference['source'],reference['target'],reference['directions']),
                         ('undefined','sat',['target-only']))
        # The accepted unused-division witness is rejected by conservative
        # source range admission. Resolved native tests separately exercise the
        # strict undefined let domain, without erasing the unused RHS.
        source=(fixtures/'unused.cfr').read_bytes()
        g=bh.pr113.capture(tools,{'unused.cfr':source},'unused.cfr',self.output/'haskell-let-unused')
        self.assertEqual(g['status'],'captured',g)
        self.assertNotIn(' / ',g['explicit'])
        reference=bh.pr113.query(tools,g,bh.protocol.request(g,0,steps=2),self.output/'haskell-let-unused-query')
        self.assertEqual((reference['status'],reference['outcome']),('ok','sat'))
        c=case((fixtures/'unused.cfr').read_text(),2,[(1,1,0)],[[1]],values=[{1:1}])
        output=self.output/'let-unused-divisor';output.mkdir()
        with self.assertRaises(subprocess.CalledProcessError): self.runtime.compile(output,c)
        self.assertIn('behavioral.possible-zero-divisor',(output/'compile-stderr.log').read_text())

    def test_replay_and_mutation_directions(self):
        for name,source,live,mutation,direction in (
            ('sound','A ?\n[no A]\n',[[1]],'drop-constraints','target-only'),
            ('complete','A ?\n[some A]\n',[[1]],'reject-all','source-only')):
            c=case(source,2,[(1,1,0)],live)
            output=self.output/name
            result=self.runtime.compare(c,output,mutation=mutation)
            self.assertEqual(result['status'],'complete',result)
            self.assertEqual(result['directions'],[direction],result)
            self.assertEqual(bs.replay(self.runtime,output,self.output/(name+'-replay')),result)
        copied=self.output/'tampered'
        import shutil
        shutil.copytree(self.output/'sound',copied)
        (copied/'candidate.json').write_text('{}')
        with self.assertRaisesRegex(ValueError,'changed replay inventory'):
            bs.replay(self.runtime,copied,self.output/'tampered-replay')

    # [utest->req~compiler-behavioral-elaboration~1]
    # [utest->req~compiler-diagnostics~1]
    def test_empty_navigation_and_self_expression_outcomes(self):
        tools = bh.pr113.load_tools(os.environ['CLAFER_058_TOOLS'])
        rows = [
            ('unknown', 'no noclafer.missing', True),
            ('nested', 'no (noclafer).(missing.parent.dref)', True),
            ('empty-false', 'some noclafer.missing', False),
            ('equal', 'A = (A)', True),
            ('not-equal', 'A != A', False),
            ('difference', 'no (A -- A)', True),
            ('intersection', 'some (A ** A)', True),
            ('safe-division', '(1 / 1) = (1 / 1)', True),
            ('temporal', 'X no noclafer.missing', True),
        ]
        def compare(row):
            name, expression, satisfied = row
            c = case('A ?\n[' + expression + ']\n', 2, [(1, 1, 0)], [[1]])
            result = self.runtime.compare(c, self.output / ('empty-self-' + name))
            reference = bh.compare(self.runtime, tools, c, self.output / ('haskell-empty-self-' + name))
            return name, satisfied, result, reference
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            results = list(pool.map(compare, rows))
        for name, satisfied, result, reference in results:
            with self.subTest(name=name):
                self.assertEqual(result, dict(status='complete',
                    source='satisfied' if satisfied else 'violated',
                    target='sat' if satisfied else 'bounded_unsat', directions=[]))
                self.assertEqual(reference['directions'], [], reference)
        c = case('P ?\n  field ?\nQ ?\n  field ?\n[no noclafer.field]\n', 5, [], [[]])
        result = self.runtime.compare(c, self.output / 'empty-ambiguous')
        self.assertEqual((result['source'], result['target'], result['directions']), ('satisfied', 'sat', []))

    def test_exact_populations_preserve_loose_bounds_and_empty_signatures(self):
        for present in (False,True):
            c=case('A ?\n[some A]\n',2,[(1,1,0)] if present else [],[[1]] if present else [[]])
            c['bounds']['objects']=3
            c['bounds']['declarations'][1].update(size=2,exact=False)
            output=self.output/('loose-bounds-'+str(present))
            result=self.runtime.compare(c,output)
            self.assertEqual(result,dict(status='complete',source='satisfied' if present else 'violated',
                target='sat' if present else 'bounded_unsat',directions=[]))
            product=bs.temporal.read(output/'compilation.json')
            request=bs.temporal.read(output/'compiler/request.json')
            trace=bs.temporal.read(output/'candidate.json')
            self.assertEqual(product['scopes']['this/cc0']['count'],3)
            for name,rows in trace['frames'][0]['signatures'].items():
                self.assertEqual(request['identities'][name],dict(count=len(rows),exact=True))

    def test_strict_scalar_decoder_and_global_identity(self):
        c=case('A ?\nr ->> int *\n',3,[(1,1,0),(2,2,0)],[[1,2],[],[1,2]],values=[{2:-1},{},{2:1}],interval=(-1,1),loop=1)
        work=self.output/'decode';work.mkdir();p=self.runtime.compile(work,c);trace=bs.target(c['candidate'],p)
        decoded=self.runtime.decode(work,trace,'valid')
        self.assertIsNotNone(bs.isomorphism(c['candidate'],decoded))
        changed=copy.deepcopy(decoded);changed['frames'][2]['values'][2][1]=0
        self.assertIsNone(bs.isomorphism(decoded,changed))
        changes={
            'missing':lambda t:t['frames'][0]['fields'][bs.SCALAR].pop(),
            'duplicate':lambda t:t['frames'][0]['fields'][bs.SCALAR].append(t['frames'][0]['fields'][bs.SCALAR][0]),
            'integer-number':lambda t:t['frames'][0]['fields'][bs.SCALAR][0].__setitem__(1,0),
            'integer-leading-zero':lambda t:t['frames'][0]['fields'][bs.SCALAR][0].__setitem__(1,'00'),
            'integer-foreign-head':lambda t:t['frames'][0]['fields'][bs.SCALAR][0].__setitem__(0,'0'),
            'integer-metadata':lambda t:t['fields'][bs.SCALAR].__setitem__('mutable',False),
            'loop':lambda t:t.__setitem__('loop',len(t['frames'])),
            'moved-parent':lambda t:t['frames'][2]['fields']['this/cc0/cc1'][0].__setitem__(1,'object_2'),
        }
        for name,change in changes.items():
            mutated=copy.deepcopy(trace);change(mutated)
            with self.subTest(name=name), self.assertRaisesRegex(ValueError,'native trace decode failed'):
                self.runtime.decode(work,mutated,name)
