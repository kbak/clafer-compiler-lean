"""Qualification adapters reject stale evidence and preserve real measurements."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import qualification as q


# [utest->req~compiler-qualification~1]
# [utest->req~compiler-performance~1]
class QualificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='clafer-qualification-test-')
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)

    def test_measurement_failure_timeout_and_per_process_memory(self):
        good = q.measure([sys.executable, '-c', 'print("measured")'], self.work, 'good', timeout=5)
        self.assertEqual((good['status'], good['exit_code']), ('completed', 0))
        self.assertGreater(good['elapsed_ns'], 0)
        self.assertGreater(good['max_rss_kib'], 0)
        self.assertEqual((self.work/'good.stdout').read_text(), 'measured\n')
        for name, program, timeout, status in [
            ('bad', 'raise SystemExit(7)', 5, 'completed'),
            ('slow', 'import time; time.sleep(10)', 0.1, 'timeout')]:
            with self.assertRaises(RuntimeError):
                q.measure([sys.executable, '-c', program], self.work, name, timeout=timeout)
            observation = json.loads((self.work/(name+'.result.json')).read_text())
            self.assertEqual(observation['status'], status)
            self.assertNotEqual(observation['exit_code'], 0)
            self.assertTrue((self.work/(name+'.command.json')).is_file())

    def test_evidence_requires_passed_source_match_and_unchanged_logs(self):
        log = self.work/'tests.log'
        log.write_text('fixture log')
        evidence = self.work/'evidence.json'
        p = {'status': 'review_required', 'tests': {'status': 'passed', 'source_status': 'matched'},
             'artifacts': {'tests.log': q.sha(log)['sha256']}}
        q.write(evidence, {'predicate': p})
        self.assertEqual(q.evidence_check(evidence)['status'], 'review_required')
        for key, value in [('status', 'failed'), ('source_status', 'changed')]:
            modified = json.loads(json.dumps(p))
            modified['tests'][key] = value
            q.write(evidence, {'predicate': modified})
            with self.assertRaises(ValueError):
                q.evidence_check(evidence)
        q.write(evidence, {'predicate': p})
        log.write_text('changed log')
        with self.assertRaisesRegex(ValueError, 'Changed evidence'):
            q.evidence_check(evidence)

    def test_corpus_scopes_and_no_implicit_comparison(self):
        cases = q.corpus(self.work)
        self.assertEqual([name for name, _, common in cases if common], ['tiny', 'representative', 'larger'])
        for name, directory, common in cases:
            bounds = json.loads((directory/'bounds.json').read_text())
            self.assertEqual(bounds['version'], 'clafer-bounds/2')
            if common:
                hb = json.loads((directory/'haskell-bounds.json').read_text())
                self.assertEqual(hb['bitwidth'], bounds['bitwidth'])
                self.assertEqual(len(hb['declarations'])+1, len(bounds['declarations']))
                self.assertEqual(sum(hb['declarations'].values())+1, bounds['objects'])
                self.assertEqual([d['exact'] for d in bounds['declarations']],
                                 [True]+[False]*len(hb['declarations']))
            else:
                self.assertFalse((directory/'haskell-bounds.json').exists())
        self.assertEqual(q.summary([{'x': 5}, {'x': 1}, {'x': 3}]),
                         {'x': {'min': 1, 'median': 3, 'max': 5}})
        with self.assertRaises(ValueError):
            q.generated(49)
        with self.assertRaises(ValueError):
            q.new_output(ROOT/'forbidden-evidence')

    def test_native_stage_output_is_the_production_output(self):
        parent = q.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='qualification-', dir=parent))
        print(f'Qualification probe evidence: {output}', flush=True)
        probe = q.build_probe(output)
        for name, source, bounds in [
            ('structural', *q.generated(1)[:2]),
            ('integer', (ROOT/'tests/fixtures/pipeline/two-values.cfr').read_text(),
             json.loads((ROOT/'tests/fixtures/pipeline/two-values.bounds.json').read_text()))]:
            directory = output/name
            directory.mkdir()
            (directory/'input.cfr').write_text(source)
            q.write(directory/'bounds.json', bounds)
            q.measure([probe, 'input.cfr', 'bounds.json', 'stages.als'], directory, 'probe', cwd=directory)
            q.measure([ROOT/'.lake/build/bin/clafer-compiler', 'compile-source', 'input.cfr',
                '--bounds', 'bounds.json', '--output', 'native.als'], directory, 'native', cwd=directory)
            self.assertEqual((directory/'stages.als').read_bytes(), (directory/'native.als').read_bytes())
            metrics = json.loads((directory/'probe.stdout').read_text())
            self.assertEqual(metrics['output_bytes'], (directory/'native.als').stat().st_size)
            for stage in ['parse', 'resolve', 'constraints', 'bounds', 'backend', 'render']:
                self.assertGreater(metrics[stage+'_ns'], 0)
        failed = subprocess.run([probe, 'missing'], capture_output=True, timeout=5)
        self.assertNotEqual(failed.returncode, 0)
        self.assertEqual(failed.stdout, b'')


if __name__ == '__main__':
    unittest.main()
