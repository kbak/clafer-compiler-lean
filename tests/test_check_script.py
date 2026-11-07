"""Check mandatory gate execution/failure propagation with isolated tool stubs."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


# [utest->req~compiler-build~1]
class CheckScriptTest(unittest.TestCase):
    def test_native_checker_dependency_preparation_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            shutil.copyfile(ROOT / 'scripts/prepare_dependencies.sh',
                            root / 'scripts/prepare_dependencies.sh')
            binary = root / 'bin'
            binary.mkdir()
            for name in ['bash', 'dirname']:
                (binary / name).symlink_to(shutil.which(name))
            stub = '''#!/usr/bin/env bash
echo "${0##*/} $*" >> "$CALLS"
if [[ "${0##*/}" == python3 && "$1" == - ]]; then
  echo Mathlib.Fixture
fi
if [[ "$*" == *linkInfoExport* && "$FAIL_NATIVE" == 1 ]]; then exit 23; fi
'''
            for name in ['python3', 'lake']:
                path = binary / name
                path.write_text(stub)
                path.chmod(0o755)
            native = ('lake query --json +Clafer.Verification.Admission:linkInfoExport '
                      '+Clafer.Semantics.RealizationCompatibility:linkInfoExport')
            for fail in ('0', '1'):
                with self.subTest(fail=fail):
                    calls_file = root / ('calls-' + fail)
                    result = subprocess.run(['bash', str(root / 'scripts/prepare_dependencies.sh')],
                        env=dict(os.environ, PATH=str(binary), CALLS=str(calls_file),
                                 FAIL_NATIVE=fail), capture_output=True, text=True, timeout=10)
                    calls = calls_file.read_text().splitlines()
                    self.assertIn(native, calls)
                    self.assertEqual(result.returncode, 23 if fail == '1' else 0,
                                     result.stdout + result.stderr)
                    self.assertEqual(calls[-1], native if fail == '1' else
                                     'python3 scripts/project_modules.py --dependencies')

    def run_check(self, fail='', missing_lake=False, args=(), artifact_cache='false'):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            for name in ['check.sh', 'prepare_dependencies.sh']:
                shutil.copyfile(ROOT / 'scripts' / name, root / 'scripts' / name)
            binary = root / 'bin'
            binary.mkdir()
            # Only the tools needed by the shell/stubs are on PATH, so a missing
            # lake cannot accidentally resolve to a developer's installation.
            for name in ['bash', 'mkdir', 'dirname', 'env', 'rm']:
                (binary / name).symlink_to(shutil.which(name))
            stub = '''#!/usr/bin/env bash
echo "${0##*/} $*" >> "$CALLS"
if [[ "$*" == 'build clafer-compiler' ]]; then
  echo "native link cache=$LAKE_ARTIFACT_CACHE" >> "$CALLS"
  mkdir -p .lake/build/bin
  echo 'fixture link inputs' > .lake/build/bin/clafer-compiler.rsp
fi
if [[ "$*" == *axiom_audit.lean* ]]; then
  echo 'audit completed' >> "$CALLS"
fi
if [[ "$*" == *leanchecker* ]]; then
  echo "kernel threads=$LEAN_NUM_THREADS" >> "$CALLS"
  echo "cache=$LAKE_ARTIFACT_CACHE restore=$LAKE_RESTORE_ARTIFACTS" >> "$CALLS"
  echo 'kernel completed' >> "$CALLS"
fi
if [[ "$*" == *scripts/run_tests.py* ]]; then : > "$CALLS.regression"; fi
if [[ "$1" == scripts/project_modules.py ]]; then
  mkdir -p .lake/validation
  printf 'ClaferCompiler\nClaferCompiler.IR.Hidden\nMain\ntests\n' > .lake/validation/modules.txt
fi
if [[ -n "$FAIL_STEP" && "$*" == *"$FAIL_STEP"* ]]; then exit 23; fi
'''
            for name in ['python3', *([] if missing_lake else ['lake'])]:
                path = binary / name
                path.write_text(stub)
                path.chmod(0o755)
            env = dict(os.environ, PATH=str(binary), CALLS=str(root / 'calls'),
                       FAIL_STEP=fail, CLAFER_COMPILER_PACKAGES='',
                       LAKE_ARTIFACT_CACHE=artifact_cache)
            result = subprocess.run(['bash', str(root / 'scripts/check.sh'), *args],
                                    env=env, capture_output=True, text=True, timeout=10)
            calls = root / 'calls'
            return result, calls.read_text().splitlines() if calls.exists() else []

    def test_all_gates_include_unimported_modules(self):
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('lake build +ClaferCompiler +ClaferCompiler.IR.Hidden +Main +tests', calls)
        self.assertIn('lake env lean -DwarningAsError=true .lake/validation/axiom_audit.lean', calls)
        self.assertIn('lake env python3 scripts/run_tests.py', calls)
        self.assertIn('lake env leanchecker --verbose ClaferCompiler Main tests', calls)
        self.assertIn('kernel threads=2', calls)
        self.assertLess(calls.index('lake env python3 scripts/run_tests.py'),
                        calls.index('kernel completed'))
        self.assertLess(calls.index('audit completed'),
                        calls.index('lake env python3 scripts/run_tests.py'))

    def test_artifact_cache_preserves_every_validation_gate(self):
        result, calls = self.run_check(artifact_cache='true')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('cache=true restore=true', calls)
        self.assertIn('native link cache=false', calls)
        self.assertIn('audit completed', calls)
        self.assertIn('kernel completed', calls)
        self.assertIn('lake env python3 scripts/run_tests.py', calls)
        self.assertIn('[check] Kernel replay: exit 0,', result.stdout)

    def test_compiler_profile_keeps_build_audit_kernel_and_compiler_regressions(self):
        result, calls = self.run_check(args=['--compiler-ci'])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('audit completed', calls)
        self.assertIn('kernel completed', calls)
        self.assertIn('lake env python3 scripts/run_tests.py --compiler-ci', calls)
        self.assertIn('reference and behavioral source suites run in separate required jobs', result.stdout)
        self.assertNotIn('All build', result.stdout)

    def test_reference_profile_prepares_dependencies_without_claiming_compiler_gates(self):
        result, calls = self.run_check(args=['--reference-ci'])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('python3 scripts/project_modules.py --dependencies', calls)
        self.assertIn('python3 scripts/run_tests.py --reference-ci', calls)
        self.assertNotIn('audit completed', calls)
        self.assertNotIn('kernel completed', calls)
        self.assertIn('compiler proof and runtime checks are separate', result.stdout)

    def test_source_profile_builds_native_code_and_propagates_suite_failure(self):
        for failure in ('', 'scripts/run_tests.py'):
            result, calls = self.run_check(args=['--source-ci'], fail=failure)
            self.assertEqual(result.returncode, 23 if failure else 0, result.stdout + result.stderr)
            self.assertIn('lake build', calls)
            self.assertIn('native link cache=false', calls)
            self.assertIn('lake env python3 scripts/run_tests.py --source-ci', calls)
            self.assertNotIn('audit completed', calls)
            self.assertNotIn('kernel completed', calls)
            self.assertEqual('Behavioral source qualification passed' in result.stdout, not failure)

    def test_required_failures_stop_the_check(self):
        for failure in ['scripts/check.py', 'scripts/project_modules.py', '--dependencies',
                        'build', 'build clafer-compiler', 'axiom_audit.lean', 'scripts/run_tests.py', 'leanchecker']:
            with self.subTest(failure=failure):
                result, calls = self.run_check(fail=failure)
                self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
                self.assertTrue(any(failure in call for call in calls), calls)
                self.assertNotIn('All build', result.stdout)
                if failure in ('axiom_audit.lean', 'scripts/run_tests.py', 'leanchecker'):
                    self.assertIn('kernel completed', calls)
                    self.assertIn('audit completed', calls)

    def test_missing_tool_and_skip_option_fail(self):
        result, calls = self.run_check(missing_lake=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(any(call.startswith('lake ') for call in calls))
        result, calls = self.run_check(args=['--skip-lean'])
        self.assertEqual(result.returncode, 2)
        self.assertEqual(calls, [])

    def test_test_runner_rejects_empty_skipped_failed_and_unimportable_suites(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tests').mkdir()
            for source, expected in [('', 1),
                ('import unittest\nclass T(unittest.TestCase):\n'
                 ' @unittest.skip("fixture")\n def test_skipped(self): pass\n', 1),
                ('import unittest\nclass T(unittest.TestCase):\n'
                 ' def test_failed(self): self.fail("fixture")\n', 1),
                ('raise RuntimeError("fixture")\n', 1),
                ('import unittest\nclass T(unittest.TestCase):\n'
                 ' def test_passed(self): self.assertEqual(2 + 2, 4)\n', 0)]:
                with self.subTest(source=source):
                    (root / 'tests/test_fixture.py').write_text(source)
                    result = subprocess.run([sys.executable, str(ROOT / 'scripts/run_tests.py')],
                                            cwd=root, capture_output=True, text=True, timeout=10,
                                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
                    self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

    def test_isolated_group_cannot_hide_failure_or_skips(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'tests').mkdir()
            good = 'import unittest\nclass T(unittest.TestCase):\n def test_ok(self): pass\n'
            (root/'tests/test_existing.py').write_text(good)
            (root/'tests/test_cli_external.py').write_text(good)
            (root/'tests/test_axiom_audit.py').write_text(good)
            (root/'tests/test_comparison.py').write_text(good)
            (root/'tests/test_source_cli.py').write_text(good)
            (root/'tests/test_source_pipeline.py').write_text(good)
            added = ('test_behavioral_source_cli', 'test_behavioral_source_comparison',
                     'test_pr113_oracles', 'test_alloy_temporal', 'test_constraints', 'test_parser', 'test_resolution', 'test_qualification',
                     'test_alloy_core', 'test_alloy_text', 'test_expression_encoding',
                     'test_expressions', 'test_inherited', 'test_integer_arithmetic',
                     'test_structural_alloy', 'test_structural_ir', 'test_structural_representation')
            for module in added:
                (root/'tests'/f'{module}.py').write_text(good)
            for source,expected in [(good,0),('',1),
                ('import unittest\nclass T(unittest.TestCase):\n'
                 ' @unittest.skip("fixture")\n def test_skipped(self): pass\n',1),
                (good.replace('pass','self.fail("fixture")'),1),
                ('raise RuntimeError("fixture")\n',1)]:
                with self.subTest(source=source):
                    (root/'tests/test_cli.py').write_text(source)
                    result = subprocess.run([sys.executable,str(ROOT/'scripts/run_tests.py')],
                        cwd=root,capture_output=True,text=True,
                        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
                    self.assertEqual(result.returncode,expected,result.stdout+result.stderr)
            # The newly scheduled exact-comparison suite remains mandatory too.
            (root/'tests/test_cli.py').write_text(good)
            for source in ['', good.replace('pass', 'self.fail("comparison")'),
                           'import unittest\nclass T(unittest.TestCase):\n'
                           ' @unittest.skip("comparison")\n def test_skip(self): pass\n']:
                (root/'tests/test_comparison.py').write_text(source)
                result = subprocess.run([sys.executable,str(ROOT/'scripts/run_tests.py')],
                    cwd=root,capture_output=True,text=True,
                    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
                self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)

            # The source group is independently mandatory and propagates failure/skips.
            (root/'tests/test_comparison.py').write_text(good)
            for module in ('test_source_cli', 'test_source_pipeline', *added):
                for source in ['', good.replace('pass', 'self.fail("source")'),
                               'import unittest\nclass T(unittest.TestCase):\n'
                               ' @unittest.skip("source")\n def test_skip(self): pass\n']:
                    (root/'tests'/f'{module}.py').write_text(source)
                    result = subprocess.run([sys.executable,str(ROOT/'scripts/run_tests.py')],
                        cwd=root,capture_output=True,text=True,
                        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
                    self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)
                    if module == 'test_pr113_oracles':
                        self.assertIn('[check] Regression remaining:', result.stdout)
                (root/'tests'/f'{module}.py').write_text(good)
            (root/'tests/test_qualification.py').unlink()
            result = subprocess.run([sys.executable, str(ROOT/'scripts/run_tests.py')],
                cwd=root, capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
            self.assertNotEqual(result.returncode, 0, 'Missing scheduled suite must fail')

            # A one-CPU schedule must retain every case without overlapping groups.
            locked = ('import fcntl, time, unittest\nclass T(unittest.TestCase):\n'
                      ' def test_serial(self):\n'
                      '  with open("active.lock", "w") as lock:\n'
                      '   fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)\n'
                      '   time.sleep(0.03)\n')
            (root/'tests/test_qualification.py').write_text(locked)
            fixtures = list((root/'tests').glob('test_*.py'))
            for fixture in fixtures:
                fixture.write_text(locked)
            result = subprocess.run([sys.executable, str(ROOT/'scripts/run_tests.py')],
                cwd=root, capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', CLAFER_TEST_JOBS='1'))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stderr.count('test_serial ('), len(fixtures))
            # PR113 must not overlap any other group, even with several workers.
            # Shared locks permit the ordinary groups to run concurrently.
            shared = locked.replace('fcntl.LOCK_EX', 'fcntl.LOCK_SH')
            for fixture in fixtures:
                fixture.write_text(locked.replace('time.sleep(0.03)', 'time.sleep(0.3)')
                                   if fixture.stem == 'test_pr113_oracles' else shared)
            result = subprocess.run([sys.executable, str(ROOT/'scripts/run_tests.py')],
                cwd=root, capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', CLAFER_TEST_JOBS='3'))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stderr.count('test_serial ('), len(fixtures))
            for fixture in fixtures:
                fixture.write_text(locked)
            for invalid in ('0', '5', 'invalid'):
                result = subprocess.run([sys.executable, str(ROOT/'scripts/run_tests.py')],
                    cwd=root, capture_output=True, text=True,
                    env=dict(os.environ, CLAFER_TEST_JOBS=invalid))
                self.assertNotEqual(result.returncode, 0, 'Invalid worker limit must fail')
            wrapper = ('import runpy, sys; from unittest.mock import patch; '
                       'script=sys.argv[1]; sys.argv=[script]\n'
                       'with patch("os.sched_getaffinity", return_value={0}):\n'
                       ' runpy.run_path(script, run_name="__main__")\n')
            result = subprocess.run([sys.executable, '-c', wrapper, str(ROOT/'scripts/run_tests.py')],
                cwd=root, capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stderr.count('test_serial ('), len(fixtures))
