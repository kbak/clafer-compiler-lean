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


def corpus_workers():
    """Reuse the runner's bounded worker budget during its exclusive phase."""
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else (os.cpu_count() or 1)
    requested = int(os.environ.get('CLAFER_TEST_JOBS', '2'))
    if requested < 1 or requested > 4:
        raise ValueError('CLAFER_TEST_JOBS must be between 1 and 4')
    return max(1, min(requested, cpus))


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
        with ThreadPoolExecutor(max_workers=corpus_workers()) as pool:
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
                    for form in ('original','explicit'):
                        query = self.output/case['id']/(form+'-query-'+str(n))
                        runtime = pr113.read(query/'runtime.json')
                        if n==0:
                            self.assertEqual(['AlloyPR113Inspect','--solve'],runtime['command'][-2:])
                            self.assertEqual(self.tools['tools']['inspector'],runtime['inspector'])
                            captured = self.output/case['id']/form
                            self.assertEqual(pr113.read(captured/'inspection.json'),pr113.read(query/'inspection.json'))
                            invocation = pr113.read(captured/'inspect-command.json')
                            self.assertEqual(runtime['command'],invocation['command'])
                            self.assertEqual(query,(captured/invocation['cwd']).resolve())
                        else:
                            self.assertEqual('AlloyTemporalBridge',runtime['command'][-1])
                            self.assertNotIn('inspector',runtime)

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


# [utest->req~compiler-temporal-oracles~1]
class PR113C7Oracles(PR113Oracles):
    """Same complete corpus and independent witnesses under the successor profile."""
    @classmethod
    def setUpClass(cls):
        for name in ('CLAFER_PR113_C7_TOOLS','CLAFER_PR113_TOOLS','CLAFER_TEMPORAL_TOOLS'):
            if not os.environ.get(name): raise RuntimeError('Prepare and set '+name+'; no skipped candidate gates')
        cls.tools = pr113.load_tools(os.environ['CLAFER_PR113_C7_TOOLS'])
        cls.previous = pr113.load_tools(os.environ['CLAFER_PR113_TOOLS'])
        cls.tools['old'] = temporal.load_tools(os.environ['CLAFER_TEMPORAL_TOOLS'])
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE',tempfile.gettempdir()))
        parent.mkdir(parents=True,exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='pr113-c7-',dir=parent))
        print('PR113 c7 oracle evidence: '+str(cls.output),flush=True)
        cls.cases = pr113.read(pr113.corpus(cls.tools))['cases']
        def run(case):
            return case['id'], pr113.run_case(cls.tools,case,cls.output/case['id'])
        with ThreadPoolExecutor(max_workers=corpus_workers()) as pool:
            cls.results = dict(pool.map(run,cls.cases))
        oracle.write(cls.output/'summary.json',cls.results)

    def test_complete_inventory_and_source_delta(self):
        source = self.tools['build'].parent/'compiler'
        upstream = {c['entry'] for c in self.cases if c['origin']=='haskell'}
        self.assertEqual({p.name for p in (source/'test/positive').glob('tmp_*.cfr')} |
                         {'explicit_dref_navigation.cfr'},upstream)
        self.assertEqual(66,len(upstream))
        old_cases = pr113.read(pr113.CORPUS)['cases']
        self.assertTrue({c['id'] for c in old_cases} <= {c['id'] for c in self.cases})
        delta = pr113.read(pr113.CORPUS.parent/'c7-delta.json')
        self.assertEqual(4,len(delta['commits']))
        self.assertEqual(delta['base'],self.previous['tools']['profile']['haskell_commit'])
        self.assertEqual(delta['candidate'],self.tools['tools']['profile']['haskell_commit'])
        self.assertEqual(240,len(delta['reviewed_sources'])+len(delta['generated_regressions']))
        for entry in delta['reviewed_sources']+delta['generated_regressions']:
            for which,tree in [('base',self.previous['build'].parent/'compiler'),('candidate',source)]:
                path = tree/entry['path']
                with self.subTest(path=entry['path'],revision=which):
                    if entry[which] is None: self.assertFalse(path.exists())
                    else: self.assertEqual(entry[which],oracle.digest(path))

    def test_fresh_corpus_fixed_points_and_bounded_queries(self):
        warnings = {}
        for case in self.cases:
            name = case['id']
            with self.subTest(case=name):
                result = self.results[name]
                self.assertEqual(case.get('expected_status','ok'),result['status'],result)
                if result['status'] not in ('ok','discrepancy'):
                    self.assertFalse(result['checks'])
                    continue
                self.assertTrue(result['fixed_point'])
                self.assertEqual(result['status']=='ok',result['agreement'])
                if 'expected' in case: self.assertTrue(result['expected_match'])
                if 'old_expected' in case: self.assertEqual(case['old_expected'],result['historical']['outcome'])
                if len(result['checks'])>1: self.assertTrue(result['assertions_nonvacuous'])
                g = self.generation(name)
                for n,check in enumerate(result['checks']):
                    a = pr113.read(self.output/name/('original-query-'+str(n))/'request.json')
                    b = pr113.read(self.output/name/('explicit-query-'+str(n))/'request.json')
                    self.assertEqual(dict(a,command_index=check['explicit_index']),b)
                    self.assertEqual(protocol.request(g,check['original_index'],
                        scopes=case.get('scopes'),steps=case.get('steps')),a)
                    for form in ('original','explicit'):
                        query = self.output/name/(form+'-query-'+str(n))
                        messages = pr113.read(query/'warnings.json')['warnings']
                        warnings[str(query.relative_to(self.output))] = messages
                        self.assertFalse(self.unused_root_warnings(self.generation(name,form)['alloy'],messages),messages)
                        expected = '--solve-static-c7' if g['backend']=='als' else '--solve-c7'
                        self.assertEqual(['AlloyPR113Inspect',expected],pr113.read(query/'runtime.json')['command'][-2:])
        oracle.write(self.output/'warning-summary.json',warnings)

    def test_union_endpoints_type_products_and_ownership_mutations(self):
        for name,field,targets in [('tmp_final_inherited_reference','this/motor7/motor7_ref',
                                    ['this/spare','this/gas']),
                                  ('explicit_dref_navigation','this/u/u_ref',['this/p','this/fast'])]:
            g = self.generation(name)
            observed = pr113.read(self.output/name/'original/inspection.json')
            self.assertEqual(targets,observed['fields'][field]['targets'])
            for mutation in ('remove','add','substitute','navigation','owner','product','product_remove','arity'):
                bad = copy.deepcopy(observed); f = bad['fields'][field]
                if mutation=='remove': f['targets'].pop()
                if mutation=='add': f['targets'].append('this/root')
                if mutation=='substitute': f['targets'][0]=f['owner']
                if mutation=='navigation': f['targets'][0]='this/garage.r_spare'
                if mutation=='owner': f['owner']=targets[0]
                if mutation=='product': f['columns']=[[f['owner'],f['owner']]]
                if mutation=='product_remove': f['columns']=[[f['owner'],targets[-1]]]
                if mutation=='arity': f['arity']=1
                with self.subTest(case=name,mutation=mutation),self.assertRaises(ValueError):
                    protocol.layout(g,bad)
        g = self.generation('union-live-good')
        ref = protocol.declarations(g['post_analysis'])['link']['_reference']['_ref']
        for mutation in ('operator','binding','navigation_owner','signature'):
            bad=copy.deepcopy(ref)
            if mutation=='operator': bad['_exp']['_op']='--'
            elif mutation=='binding': bad['_exp']['_exps'][1]['_exp']['_binding']['tag']='LocalBind'
            elif mutation=='navigation_owner':
                bad['_exp']['_exps'][0]['_exp']['_exps'][0] = copy.deepcopy(bad['_exp']['_exps'][1])
            else: bad['_exp']['_exps'][1]['_exp']['_sident']='r_other'
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                protocol.reference_targets(bad,protocol.declarations(g['post_analysis']),g['names'])

    def test_exact_navigation_bytes_and_target_restrictions(self):
        compact,spaced = self.generation('navigation-compact'),self.generation('navigation-spaced')
        self.assertNotEqual(compact['files'],spaced['files'])
        self.assertEqual(compact['explicit'],spaced['explicit'])
        self.assertIn('owner.link.dref',compact['explicit'])
        self.assertNotIn(' . ',compact['explicit'])
        # The restriction is independently retained in the explicit source, not inferred from field syntax.
        for name in ('tmp_final_inherited_reference','explicit_dref_navigation','union-live-good'):
            explicit=self.generation(name)['explicit']
            self.assertIn('++',explicit);self.assertIn(' in ',explicit)
        self.assertEqual(['sat'],[c['original_outcome'] for c in self.results['union-live-good']['checks']])
        dead=self.results['union-dead-target']
        self.assertEqual('discrepancy',dead['status'])
        self.assertEqual(('sat','bounded_unsat'),(dead['checks'][0]['original_outcome'],
                                               dead['checks'][0]['explicit_outcome']))
        frames=self.trace('union-dead-target')['frames']
        self.assertGreaterEqual(len(frames),2)
        target=frames[0]['fields']['this/box/r_nested'][0][1]
        self.assertTrue(all(not f['fields']['this/box/r_nested'] for f in frames[1:]))
        self.assertTrue(all([t for _,t in f['fields']['this/link/link_ref']]==[target] for f in frames))
        self.assertTrue(all(f['fields']['this/owner/r_link'] for f in frames))
        self.assertEqual('malformed',self.results['union-wrong-target']['status'])
        self.assertIn("Function '=' cannot be performed",self.results['union-wrong-target']['detail'])
        self.assertFalse((self.output/'union-wrong-target/original-query-0').exists())

    def test_root_binding_nested_guards_and_source_maps(self):
        import re
        g=self.generation('root-binding'); text=g['alloy']
        self.assertNotIn('all self_ : root',text)
        self.assertIn('always (root = root)',text)
        self.assertIn('always (no root)',text)
        self.assertIn('always (lone root.@r_thisThing)',text)
        self.assertIn('all self_ : owner | always (self_ in alive_owner implies',text)
        self.assertIn('self_.@r_child',text)
        self.assertIn('alive_thisThing',text)
        self.assertNotIn('rootThing',text)
        self.assertEqual(g['source_map'],g['backend_map'])
        # Retained physical Alloy spans must still select their attributed expression after bindTo.
        entries=re.findall(r'Span \(Pos (\d+) (\d+)\) \(Pos (\d+) (\d+)\),IrPExp \{pUid = "([^"]+)"\}',g['source_map'])
        self.assertTrue(entries)
        pids={}
        def visit(value):
            if isinstance(value,list):
                for x in value: visit(x)
            elif isinstance(value,dict):
                if value.get('_pid'): pids[value['_pid']]=value
                for x in value.values(): visit(x)
        visit(g['post_analysis'])
        selected=[];lines=text.splitlines()
        for line,col,end_line,end_col,pid in entries:
            self.assertIn(pid,pids)
            line,col,end_line,end_col=map(int,(line,col,end_line,end_col))
            self.assertTrue(1<=line<=end_line<=len(lines))
            if line==end_line: selected.append(lines[line-1][col-1:end_col-1])
        self.assertIn('root = root',selected)
        self.assertTrue(any('self_.@r_child' in x for x in selected))

    @staticmethod
    def unused_root_warnings(text,messages):
        lines=text.splitlines()
        return [w for w in messages if 'unused' in w['message'].lower()
                and lines[w['line']-1][w['column']-1:w['end_column']]=='self_'
                and 'all self_ : root' in lines[w['line']-1]]

    def test_old_root_binders_warning_control_and_matched_queries(self):
        for name in ('root-binding','root-recurrence','root-initially','root-recurring'):
            case=next(c for c in self.cases if c['id']==name)
            directory=self.output/('previous-'+name)
            g=pr113.capture(self.previous,pr113.inputs(case,self.tools),case['entry'],directory)
            self.assertIn('all self_ : root',g['alloy'])
            original=self.generation(name)
            for n,check in enumerate(self.results[name]['checks']):
                request=protocol.request(original,check['original_index'])
                result=pr113.query(self.tools,g,request,directory/('query-'+str(n)),inspection=True)
                self.assertEqual('ok',result['status'],result)
                self.assertEqual(check['original_outcome'],result['outcome'])
                warnings=pr113.read(directory/('query-'+str(n))/'warnings.json')['warnings']
                self.assertTrue(self.unused_root_warnings(g['alloy'],warnings),warnings)
        # Removing outer always admits the one-time event trace, contrary to root recurrence.
        g=copy.deepcopy(self.generation('root-recurrence'))
        request=protocol.request(g,0)
        needle='fact { always (eventually (some alive_event)) }'
        self.assertEqual(1,g['alloy'].count(needle))
        g['alloy']=g['alloy'].replace(needle,'fact { eventually (some alive_event) }')
        directory=self.output/'missing-root-always';directory.mkdir()
        (directory/'model.als').write_text(g['alloy'])
        result=temporal.solve(self.tools['runtime'],self.tools['api'],directory,request,inspection=True)
        oracle.write(directory/'result.json',result)
        self.assertEqual(('ok','sat'),(result['status'],result.get('outcome')))
        frames=result['trace']['frames']
        self.assertTrue(frames[0]['fields']['this/root/r_event'])
        self.assertTrue(all(not f['fields']['this/root/r_event'] for f in frames[1:]))

    def test_retained_root_navigation_failure_has_no_solver_claim(self):
        result=pr113.read(self.output/'root-navigation-unsupported/original-query-0/result.json')
        self.assertEqual(('error','parse',None),(result['status'],result['stage'],result['outcome']))
        self.assertIn('legal relational join',result['detail'])
        self.assertEqual('error',pr113.replay(self.tools,self.output/'root-navigation-unsupported',
                         self.output/'root-navigation-replay')['status'])

    def test_analyzer_union_syntax_is_closed_and_integer_columns_are_bounded(self):
        import subprocess
        runtime=self.tools['runtime']
        for index,(expression,accepted) in enumerate((('A',True),('A + B',True),
                ('A + (B + C)',True),('A & B',False),('A - B',False),('A.r',False))):
            directory=self.output/('endpoint-syntax-'+str(index));directory.mkdir()
            (directory/'model.als').write_text('sig A { r: set B }\nsig B {}\nsig C {}\n'
                +'sig R { ref: set '+expression+' }\nrun {} for 3\n')
            command=[str(runtime['java']),'-cp',os.pathsep.join(map(str,(runtime['classes'],runtime['jar']))),
                     'AlloyPR113Inspect','--inspect-c7']
            with (directory/'stdout.log').open('wb') as out,(directory/'stderr.log').open('wb') as err:
                result=subprocess.run(command,cwd=directory,stdout=out,stderr=err,timeout=30)
            oracle.write(directory/'execution.json',dict(command=command,returncode=result.returncode))
            with self.subTest(expression=expression): self.assertEqual(accepted,result.returncode==0)
        bundle=self.output/'explicit_dref_navigation/original-query-0'
        result=pr113.read(bundle/'result.json');request=pr113.read(bundle/'request.json')
        inspected=pr113.read(bundle/'inspection.json')
        fields={k for k,f in inspected['fields'].items() if f['targets']==['Int']}
        self.assertTrue(fields)
        for atom in ('foreign','128','-129','01'):
            trace=copy.deepcopy(result['trace']);field=next(iter(fields))
            trace['frames'][0]['fields'][field][0][1]=atom
            with self.subTest(atom=atom),self.assertRaises(ValueError):
                temporal.validate_trace(trace,request,integer_fields=fields)

    def test_historical_explicit_bytes_and_new_union_replay(self):
        case=next(c for c in self.cases if c['id']=='navigation-compact')
        g=pr113.capture(self.previous,pr113.inputs(case,self.tools),case['entry'],self.output/'historical-navigation')
        current=self.generation(case['id'])
        self.assertIn(' . ',g['explicit'])
        self.assertNotEqual(g['explicit'],current['explicit'])
        # Preserve and execute both historical bytes and new bytes without normalizing the comparison.
        again=pr113.capture(self.previous,{'explicit.cfr':g['explicit'].encode()},'explicit.cfr',self.output/'historical-navigation-explicit')
        self.assertEqual(g['explicit'],again['explicit'])
        self.assertEqual('ok',pr113.replay(self.tools,self.output/'union-live-good',self.output/'union-replay')['status'])
        self.assertEqual('discrepancy',pr113.replay(self.tools,self.output/'union-dead-target',self.output/'union-discrepancy-replay')['status'])


# [utest->req~compiler-temporal-oracles~1]
class Clafer058Oracles(PR113C7Oracles):
    """Fresh current-profile corpus; original PR113 classes retain their pins."""
    @classmethod
    def setUpClass(cls):
        for name in ('CLAFER_058_TOOLS', 'CLAFER_PR113_TOOLS', 'CLAFER_TEMPORAL_TOOLS'):
            if not os.environ.get(name): raise RuntimeError('Prepare and set ' + name)
        cls.tools = pr113.load_tools(os.environ['CLAFER_058_TOOLS'])
        cls.previous = pr113.load_tools(os.environ['CLAFER_PR113_TOOLS'])
        cls.tools['old'] = temporal.load_tools(os.environ['CLAFER_TEMPORAL_TOOLS'])
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='clafer-058-', dir=parent))
        print('0.5.8 oracle evidence: ' + str(cls.output), flush=True)
        cls.cases = pr113.read(pr113.corpus(cls.tools))['cases']
        def run(case):
            return case['id'], pr113.run_case(cls.tools, case, cls.output / case['id'])
        with ThreadPoolExecutor(max_workers=corpus_workers()) as pool:
            cls.results = dict(pool.map(run, cls.cases))
        oracle.write(cls.output / 'summary.json', cls.results)

    def test_complete_inventory_and_source_delta(self):
        source = self.tools['build'].parent / 'compiler'
        inventory = pr113.read(pr113.corpus(self.tools))
        self.assertEqual(inventory['haskell_commit'], self.tools['tools']['profile']['haskell_commit'])
        self.assertEqual(inventory['profile'], 'behavioral-0.5.8/v1')
        upstream = {c['entry'] for c in self.cases if c['origin'] == 'haskell'}
        self.assertEqual({p.name for p in (source / 'test/positive').glob('tmp_*.cfr')} |
                         {'explicit_dref_navigation.cfr'}, upstream)
        self.assertTrue({c['id'] for c in pr113.read(pr113.CORPUS.parent / 'c7-inventory.json')['cases']}
                        <= {c['id'] for c in self.cases})
        self.assertEqual(self.tools['tools']['profile']['ghc'], '9.12.4')
        self.assertEqual(self.tools['tools']['profile']['resolver'], 'nightly-2026-11-11')
