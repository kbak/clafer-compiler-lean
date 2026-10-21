"""Exercise the actual linked executable, independently of Lean's evaluator."""
from pathlib import Path
import json
import subprocess
import tomllib
import unittest


# [utest->req~compiler-build~1]
# [utest->req~compiler-cli~1]
class NativeTest(unittest.TestCase):
    def test_version_and_rejection_protocol(self):
        executable = Path('.lake/build/bin/clafer-compiler').resolve()
        package = tomllib.loads(Path('lakefile.toml').read_text())
        profile = json.loads(Path('scripts/oracles/profile.json').read_text())
        for args, code in [(['--version'], 0), (['--help'], 0), ([], 2), (['compile-ir'], 2),
                           (['--version', 'extra'], 2), (['compile-source', 'x'], 3)]:
            with self.subTest(args=args):
                result = subprocess.run([str(executable), *args], capture_output=True,
                                        text=True, timeout=10)
                self.assertEqual(result.returncode, code)
                if code == 0:
                    self.assertEqual(result.stderr, '')
                    if args == ['--version']:
                        self.assertIn('clafer-compiler ' + package['version'] + '\n', result.stdout)
                        self.assertIn(package['require'][0]['rev'], result.stdout)
                        self.assertIn(profile['haskell_commit'], result.stdout)
                        self.assertIn('m1-effective', result.stdout)
                        self.assertIn('source-text: unsupported', result.stdout)
                    else:
                        self.assertIn('compile-ir INPUT --bounds BOUNDS --output OUTPUT', result.stdout)
                else:
                    self.assertEqual(result.stdout, '')
                    self.assertIn('cli.', result.stderr)
