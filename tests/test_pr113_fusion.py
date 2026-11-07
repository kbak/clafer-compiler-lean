"""Inspection sharing preserves query supervision and complete paired coverage."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts/oracles'))
import oracle
import pr113
import temporal


# [utest->req~compiler-temporal-oracles~1]
class PR113FusionTests(unittest.TestCase):
    request = dict(command_index=0, overall=1, bitwidth=8, min_steps=1, max_steps=2,
                   identities={'this/root': dict(count=1, exact=False)})

    def substitute(self, directory, body):
        java = directory/'java'
        java.write_text('#!'+sys.executable+'\n'+body+'\n')
        java.chmod(0o755)
        runtime = dict(java=java, classes=directory, jar=directory/'unused.jar',
                       identity={}, temporal_bridge={'source':'bridge','binary':'class'},
                       inspector={'source':'inspector','binary':'inspector-class'})
        class Environment:
            @staticmethod
            def java_env(): return os.environ.copy()
        return runtime, {'alloy_runtime': Environment}

    def test_missing_or_malformed_shared_inspection_cannot_claim_an_outcome(self):
        # Substitute JVMs exercise retained protocol validation, not Alloy truth.
        answer = dict(schema='clafer-temporal-solver/1', status='ok', outcome='bounded_unsat',
                      options=dict(temporal.temporal_build.profile()['options'], solver='sat4j'))
        valid = dict(schema='clafer-pr113-inspection/1', signatures={}, fields={}, commands=[])
        for inspected in (None, '{', json.dumps(dict(valid, schema='wrong')), json.dumps(valid)):
            with self.subTest(inspection=inspected), tempfile.TemporaryDirectory() as scratch:
                directory = Path(scratch)
                body = 'from pathlib import Path\n'
                body += 'Path("solver.json").write_text('+repr(json.dumps(answer))+')\n'
                if inspected is not None:
                    body += 'Path("inspection.json").write_text('+repr(inspected)+')\n'
                runtime, api = self.substitute(directory, body)
                result = temporal.solve(runtime, api, directory, self.request, inspection=True)
                self.assertEqual('ok' if inspected==json.dumps(valid) else 'error', result['status'])
                if result['status']=='error': self.assertIsNone(result['outcome'])
                record = temporal.read(directory/'runtime.json')
                self.assertEqual(['AlloyPR113Inspect','--solve'], record['command'][-2:])
                self.assertEqual(runtime['inspector'], record['inspector'])
                self.assertEqual((30,512,2560), (record['timeout_seconds'],record['heap_mb'],record['address_space_mb']))
                self.assertEqual(['-Xmx512m','-Xss1m','-XX:ActiveProcessorCount=1','-XX:+UseSerialGC',
                    '-XX:ReservedCodeCacheSize=64m','-XX:CompressedClassSpaceSize=64m'], record['jvm_options'])

    def test_shared_inspection_has_the_query_deadline_and_retains_timeout(self):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            runtime, api = self.substitute(directory, 'import time; time.sleep(5)')
            result = temporal.solve(runtime, api, directory, self.request, timeout=1, inspection=True)
            self.assertEqual('timeout', result['status'])
            self.assertNotIn(result.get('outcome'), ('sat','bounded_unsat'))
            oracle.write(directory/'result.json', result)
            capture = directory/'capture'; capture.mkdir()
            with self.assertRaises(pr113.subprocess.TimeoutExpired):
                pr113.inspect({}, {}, capture, directory)
            invocation = temporal.read(capture/'inspect-command.json')
            self.assertEqual('..', invocation['cwd'])
            self.assertEqual(['AlloyPR113Inspect','--solve'], invocation['command'][-2:])

    def test_bad_layout_or_command_inventory_clears_successful_solver_outcome(self):
        valid = [{'label':'run','check':False}, {'label':'a','check':True}]
        for bad in ('layout','run','assertion','duplicate',None):
            with self.subTest(bad=bad), tempfile.TemporaryDirectory() as scratch:
                commands = [dict(c) for c in valid]
                if bad=='run': commands[0]['check']=True
                if bad=='assertion': commands[1]['label']='foreign'
                if bad=='duplicate': commands.append(dict(commands[1]))
                def solve(runtime, api, directory, request, **kwargs):
                    oracle.write(directory/'inspection.json', {'commands':commands})
                    return dict(status='ok',outcome='bounded_unsat')
                with patch.object(temporal,'solve',side_effect=solve), \
                        patch.object(pr113.protocol,'layout',side_effect=ValueError('layout') if bad=='layout' else None), \
                        patch.object(pr113,'assertions',return_value=['a']):
                    result = pr113.query({'runtime':{},'api':{}}, {'alloy':'model'}, self.request,
                                         Path(scratch)/'query', inspection=True)
                self.assertEqual('ok' if bad is None else 'error', result['status'])
                if bad is not None: self.assertIsNone(result['outcome'])

    def test_first_runs_are_used_once_and_all_assertions_keep_fresh_queries(self):
        for first_status in ('ok','timeout'):
            with self.subTest(first_status=first_status), tempfile.TemporaryDirectory() as scratch:
                directory = Path(scratch)
                build = directory/'build.json'; build.write_text('{}')
                generation = dict(status='captured',explicit='fixed',names={'x':'x'},trace_length=2)
                inspection = {'commands':[{'label':'run','check':False},{'label':'a','check':True}]}
                calls = []
                def query(tools, generation, request, output, *, inspection=False):
                    calls.append((output.name,dict(request),inspection))
                    if len(calls)==1 and first_status=='timeout': return {'status':'timeout'}
                    return dict(status='ok',outcome='sat')
                def request(g, index, **kwargs): return dict(self.request,command_index=index)
                with patch.object(pr113,'inputs',return_value={}), \
                        patch.object(pr113,'capture',return_value=generation), \
                        patch.object(pr113,'inspect',return_value=inspection), \
                        patch.object(pr113,'assertions',return_value=['a']), \
                        patch.object(pr113.protocol,'request',side_effect=request), \
                        patch.object(pr113,'query',side_effect=query):
                    result = pr113.run_case({'build':build}, {'entry':'fixture.cfr'}, directory/'evidence')
                self.assertEqual('ok' if first_status=='ok' else 'query_failure', result['status'])
                self.assertEqual(2,len(result['checks']))
                self.assertEqual(first_status,result['checks'][0]['original_status'])
                self.assertEqual([('original-query-0',0,True),('explicit-query-0',0,True),
                                  ('original-query-1',1,False),('explicit-query-1',1,False)],
                                 [(name,r['command_index'],inspected) for name,r,inspected in calls])
                self.assertEqual(calls[0][1],calls[1][1])
                self.assertEqual(calls[2][1],calls[3][1])

    def test_new_profile_requires_real_well_formed_warning_receipts(self):
        for warnings in (None, {}, {'schema':'clafer-alloy-warnings/1','warnings':[]},
                         {'schema':'clafer-alloy-warnings/1','warnings':[{'message':'incomplete'}]}):
            with self.subTest(warnings=warnings),tempfile.TemporaryDirectory() as scratch:
                def solve(runtime, api, directory, request, **kwargs):
                    oracle.write(directory/'inspection.json', {})
                    if warnings is not None: oracle.write(directory/'warnings.json',warnings)
                    return dict(status='ok',outcome='bounded_unsat')
                with patch.object(temporal,'solve',side_effect=solve), \
                        patch.object(pr113,'validate_inspection'):
                    result=pr113.query(dict(candidate='c7a2fb7',runtime={},api={}),
                        dict(alloy='model',backend='tmp.als'),self.request,Path(scratch)/'query')
                accepted=warnings=={'schema':'clafer-alloy-warnings/1','warnings':[]}
                self.assertEqual('ok' if accepted else 'error',result['status'])
                if not accepted: self.assertIsNone(result['outcome'])

    def test_explicit_fixed_point_rejects_whitespace_only_difference(self):
        with tempfile.TemporaryDirectory() as scratch:
            directory=Path(scratch);build=directory/'build.json';build.write_text('{}')
            original=dict(status='captured',explicit='[a.b]\n',names={},trace_length=4)
            changed=dict(original,explicit='[a . b]\n')
            with patch.object(pr113,'inputs',return_value={}), \
                    patch.object(pr113,'capture',side_effect=[original,changed]), \
                    patch.object(pr113,'query') as query:
                result=pr113.run_case({'build':build},{'entry':'input.cfr'},directory/'evidence')
            self.assertEqual('error',result['status'])
            self.assertFalse(result['fixed_point'])
            self.assertIn('Explicit corpus fixed point failed',result['detail'])
            query.assert_not_called()


if __name__=='__main__': unittest.main()
