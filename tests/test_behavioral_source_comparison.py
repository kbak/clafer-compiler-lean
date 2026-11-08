"""Full-source exact observations, replay, decoder and sensitivity gates."""
from concurrent.futures import ThreadPoolExecutor
import copy
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts/comparison'))
import behavioral_source as bs
from behavioral_source_cases import case, features, patterns
import behavioral_haskell as bh


# [utest->req~compiler-behavioral-qualification~1]
# [utest->req~compiler-behavioral-integration~1]
class BehavioralSourceComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent=bs.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output=Path(tempfile.mkdtemp(prefix='behavioral-source-',dir=parent))
        tools=os.environ.get('CLAFER_ORACLE_TOOLS')
        if not tools: raise AssertionError('CLAFER_ORACLE_TOOLS required')
        cls.runtime=bs.Runtime(tools,cls.output/'runtime')
        print(f'Full source evidence: {cls.output}',flush=True)

    def test_full_feature_observations(self):
        fixtures=list(features())+list(patterns())
        self.assertEqual(len({name for name,_,_,_ in fixtures}),len(fixtures))
        def compare(row):
            name,rows,expected,c=row
            result=self.runtime.compare(c,self.output/name)
            return name,rows,expected,result
        with ThreadPoolExecutor(max_workers=2) as pool:
            results=list(pool.map(compare,fixtures))
        for name,rows,expected,result in results:
            with self.subTest(name=name):
                self.assertEqual(result['status'],'complete',result)
                self.assertEqual(result['directions'],[],result)
                self.assertEqual(result['source'],expected,result)
        bs.oracle.write(self.output/'coverage.json',[dict(name=name,rows=rows,expected=expected,result=result)
                                                    for name,rows,expected,result in results])

    def test_revision_qualified_haskell_observations(self):
        path=os.environ.get('CLAFER_PR113_C7_TOOLS')
        self.assertTrue(path,'CLAFER_PR113_C7_TOOLS required')
        tools=bh.pr113.load_tools(path)
        selected=[]
        for name,rows,expected,c in features():
            if name.startswith(('inherited-bag','inherited-set','group-','modifier-False-',
                                'equation-','property-check','controller-','identity-budget-')):
                selected.append((name,c))
            if name.startswith('modifier-True-'):
                # Reference inherited from an abstract; both modifiers authored
                # on the concrete occurrence, matching accepted PR113 witnesses.
                c=copy.deepcopy(c)
                first=c['source'].splitlines()[0]
                mods=first[len('abstract '):].split(' R ')[0]
                c['source']='abstract R ->> int\n'+mods+' r : R *\n'
                selected.append((name,c))
        for name,c in selected:
            with self.subTest(name=name):
                answer=bh.compare(self.runtime,tools,c,self.output/('haskell-'+name))
                # Accepted Structural.Keys requires inherited set uniqueness.
                # This pinned Haskell generator omits the concrete-fiber key.
                expected=['target-only'] if name=='inherited-set' else []
                self.assertEqual(answer['directions'],expected,answer)
                if name=='inherited-set':
                    self.assertEqual((answer['source'],answer['target']),('violated','sat'))
                if name=='equation-True':
                    self.assertEqual(bh.replay(self.runtime,tools,self.output/('haskell-'+name),
                        self.output/'haskell-replay'),answer)

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
        tools = bh.pr113.load_tools(os.environ['CLAFER_PR113_C7_TOOLS'])
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
        for name, expression, satisfied in rows:
            c = case('A ?\n[' + expression + ']\n', 2, [(1, 1, 0)], [[1]])
            with self.subTest(name=name):
                result = self.runtime.compare(c, self.output / ('empty-self-' + name))
                self.assertEqual(result, dict(status='complete',
                    source='satisfied' if satisfied else 'violated',
                    target='sat' if satisfied else 'bounded_unsat', directions=[]))
                reference = bh.compare(self.runtime, tools, c, self.output / ('haskell-empty-self-' + name))
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
