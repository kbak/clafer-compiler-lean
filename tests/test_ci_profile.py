"""Exercise dependency selection, explicit evidence profiles and the required gate."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from ci_profile import compiler_only, profile_scope, select


# [utest->req~intentbond-workflow~1]
class CIProfileTests(unittest.TestCase):
    def test_only_known_independent_inputs_avoid_reference_runs(self):
        for path in ['ClaferCompiler/Frontend/X.lean', 'ClaferCompiler.lean', 'Main.lean',
                     'tests/NewNative.lean', 'tests/test_new_compiler.py', 'docs/parser.md']:
            self.assertTrue(compiler_only(path), path)
        for path in ['scripts/oracles/temporal.py', 'scripts/ci_profile.py',
                     'tests/test_pr113_oracles.py', 'tests/test_temporal_oracles.py',
                     'tests/helpers.py', 'tests/fixtures/pr113/a.cfr', 'new-tool.py',
                     'lake-manifest.json', 'lean-toolchain', 'scope.json',
                     '.github/workflows/ci.yml', 'requirements/intentbond.txt',
                     'docs/oracles.md', 'docs/sources.md', 'docs/spec.md']:
            self.assertFalse(compiler_only(path), path)

    def test_actual_git_changes_and_missing_baseline(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-c', 'user.name=Fixture',
                    '-c', 'user.email=fixture@example.invalid', *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()
            git('init', '-q')
            (root/'base').write_text('fixture')
            git('add', '.')
            git('commit', '-qm', 'baseline')
            base = git('rev-parse', 'HEAD')
            (root/'Main.lean').write_text('def main := 1')
            git('add', '.')
            git('commit', '-qm', 'compiler')
            args = (root, 'pull_request', 'behavioral', 'refs/pull/1/merge', 'synchronize')
            result = select(*args, base)
            self.assertEqual(result['profile'], 'compiler')
            self.assertFalse(result['reference'])
            # Full qualification must require both parallel jobs even for a
            # compiler-only diff. Exercise the actual workflow output contract.
            for event, ref, action in [('schedule', 'refs/heads/main', ''),
                    ('workflow_dispatch', 'refs/heads/behavioral', ''),
                    ('push', 'refs/heads/behavioral', ''),
                    ('pull_request', 'refs/pull/1/merge', 'ready_for_review')]:
                result = select(root, event, 'behavioral', ref, action, base)
                self.assertEqual(result['profile'], 'compiler')
                self.assertTrue(result['reference'], 'Both jobs are mandatory')
            output, record = root/'outputs', root/'selection.json'
            selected = subprocess.run([sys.executable, str(ROOT/'scripts/ci_profile.py'),
                'select', '--repo', str(root), '--event', 'pull_request',
                '--base-ref', 'behavioral', '--ref', 'refs/pull/1/merge',
                '--action', 'ready_for_review', '--baseline', base,
                '--output', str(output), '--record', str(record)],
                capture_output=True, text=True)
            self.assertEqual(selected.returncode, 0, selected.stderr)
            values = dict(line.split('=', 1) for line in output.read_text().splitlines())
            self.assertEqual(values, dict(candidate=git('rev-parse', 'HEAD'),
                baseline=base, profile='compiler', reference='true'))
            self.assertEqual(json.loads(record.read_text())['reference'], True)
            # Renaming an unknown dependency into a safe path must still rerun it.
            git('mv', 'base', 'ClaferCompiler.lean')
            git('commit', '-qm', 'rename')
            self.assertTrue(select(*args, base)['reference'])
            for missing in ('', 'f'*40):
                self.assertTrue(select(*args, missing)['reference'])
            self.assertEqual(select(root, 'pull_request', 'main', 'refs/pull/1/merge', '', base)['profile'], 'routine')
            for event in ('pull_request', 'unknown'):
                result = select(root, event, '', '', '', base)
                self.assertEqual(result['profile'], 'compiler')
                self.assertTrue(result['reference'], 'Unknown inputs require both jobs')

    def test_profiles_preserve_policy_and_identify_their_actual_commands(self):
        original = (ROOT/'scope.json').read_bytes()
        self.assertEqual(profile_scope(original, 'full'), original)
        policy = json.loads(original)
        for name, command in [('compiler', ['bash', 'scripts/check.sh', '--compiler-ci']),
                              ('reference', ['bash', 'scripts/check.sh', '--reference-ci'])]:
            expected = copy.deepcopy(policy)
            expected['name'] += '/'+name
            expected['tests']['command'] = command
            self.assertEqual(json.loads(profile_scope(original, name)), expected)
        with self.assertRaises(ValueError):
            profile_scope(original, 'skip')
        policy['tests']['command'] = ['true']
        with self.assertRaises(ValueError):
            profile_scope(json.dumps(policy).encode(), 'compiler')

    def test_required_gate_rejects_failed_cancelled_and_missing_jobs(self):
        workflow = (ROOT/'.github/workflows/ci.yml').read_text()
        script = textwrap.dedent(workflow.split('      - name: Require every selected job\n')[1]
                                 .split('        run: |\n')[1])
        for selection, compiler, reference, required, ok in [
                ('success', 'success', 'success', 'true', True),
                ('success', 'success', 'skipped', 'false', True),
                ('failure', 'success', 'skipped', 'false', False),
                ('success', 'failure', 'success', 'true', False),
                ('success', 'cancelled', 'skipped', 'false', False),
                ('success', 'skipped', 'skipped', 'false', False),
                ('success', 'success', 'skipped', 'true', False),
                ('success', 'success', 'failure', 'true', False),
                ('success', 'success', 'cancelled', 'true', False),
                ('success', 'success', 'success', 'false', False),
                ('success', 'success', 'skipped', '', False)]:
            result = subprocess.run(['bash', '-e', '-c', script], env=dict(os.environ,
                SELECTION=selection, COMPILER=compiler, REFERENCE=reference, REQUIRED=required))
            self.assertEqual(result.returncode == 0, ok, (selection, compiler, reference, required))

    def test_profiles_partition_only_reference_cases_and_discover_new_tests(self):
        good = 'import unittest\nclass T(unittest.TestCase):\n def test_ok(self): pass\n'
        bad = good.replace('pass', 'self.fail("fixture")')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'tests').mkdir()
            names = [p.name for p in (ROOT/'tests').glob('test_*.py')]
            for name in names:
                (root/'tests'/name).write_text(good)
            references = ['test_pr113_oracles.py', 'test_temporal_oracles.py']
            for name in references:
                (root/'tests'/name).write_text(bad)
            def run(*args):
                return subprocess.run([sys.executable, str(ROOT/'scripts/run_tests.py'), *args],
                    cwd=root, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                    capture_output=True, text=True, timeout=15)
            compiler = run('--compiler-ci')
            self.assertEqual(compiler.returncode, 0, compiler.stdout+compiler.stderr)
            self.assertEqual(compiler.stderr.count('test_ok ('), len(names)-2)
            self.assertNotEqual(run().returncode, 0)
            self.assertNotEqual(run('--reference-ci').returncode, 0)
            (root/'tests/test_future_feature.py').write_text(bad)
            self.assertNotEqual(run('--compiler-ci').returncode, 0)
            for name in references:
                (root/'tests'/name).write_text(good)
            reference = run('--reference-ci')
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(reference.stderr.count('test_ok ('), 2)
            (root/'tests/test_temporal_oracles.py').unlink()
            self.assertNotEqual(run('--reference-ci').returncode, 0)
