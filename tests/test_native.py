"""Exercise the actual linked executable, independently of Lean's evaluator."""
from pathlib import Path
import subprocess
import unittest


# [utest->req~compiler-build~1]
class NativeTest(unittest.TestCase):
    def test_version_and_rejection_protocol(self):
        executable = Path('.lake/build/bin/clafer-compiler').resolve()
        for args, code in [(['--version'], 0), ([], 2), (['compile-ir'], 2),
                           (['--version', 'extra'], 2)]:
            with self.subTest(args=args):
                result = subprocess.run([str(executable), *args], capture_output=True,
                                        text=True, timeout=10)
                self.assertEqual(result.returncode, code)
                if code == 0:
                    self.assertEqual(result.stdout, 'clafer-compiler 0.1.0 (build bootstrap)\n')
                    self.assertEqual(result.stderr, '')
                else:
                    self.assertEqual(result.stdout, '')
                    self.assertIn('compilation is not implemented', result.stderr)
