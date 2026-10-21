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
    def run_check(self, fail='', missing_lake=False, args=()):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            for name in ['check.sh', 'prepare_dependencies.sh']:
                shutil.copyfile(ROOT / 'scripts' / name, root / 'scripts' / name)
            binary = root / 'bin'
            binary.mkdir()
            # Only the tools needed by the shell/stubs are on PATH, so a missing
            # lake cannot accidentally resolve to a developer's installation.
            for name in ['bash', 'mkdir', 'dirname', 'sleep']:
                (binary / name).symlink_to(shutil.which(name))
            stub = '''#!/usr/bin/env bash
echo "${0##*/} $*" >> "$CALLS"
if [[ "$*" == *leanchecker* ]]; then
  echo "kernel threads=$LEAN_NUM_THREADS" >> "$CALLS"
  while [[ ! -f "$CALLS.regression" ]]; do sleep 0.01; done
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
                       FAIL_STEP=fail, CLAFER_COMPILER_PACKAGES='')
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
        self.assertIn('kernel threads=1', calls)
        self.assertLess(calls.index('lake env python3 scripts/run_tests.py'),
                        calls.index('kernel completed'))

    def test_required_failures_stop_the_check(self):
        for failure in ['scripts/check.py', 'scripts/project_modules.py', '--dependencies',
                        'build', 'axiom_audit.lean', 'scripts/run_tests.py', 'leanchecker']:
            with self.subTest(failure=failure):
                result, calls = self.run_check(fail=failure)
                self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
                self.assertTrue(any(failure in call for call in calls), calls)
                self.assertNotIn('All build', result.stdout)
                if failure in ('scripts/run_tests.py', 'leanchecker'):
                    self.assertIn('kernel completed', calls)

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

    def test_parallel_cli_group_cannot_hide_failure_or_skips(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'tests').mkdir()
            good = 'import unittest\nclass T(unittest.TestCase):\n def test_ok(self): pass\n'
            (root/'tests/test_existing.py').write_text(good)
            (root/'tests/test_cli_external.py').write_text(good)
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
