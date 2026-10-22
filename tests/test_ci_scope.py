"""Reject unapproved CI policy changes while retaining the original baseline."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from ci_scope import digest, select_scope, ORIGINAL_SHA256, MIGRATED_SHA256


def encode(policy):
    return (json.dumps(policy, indent=2) + '\n').encode()


# [utest->req~intentbond-workflow~1]
class ScopeSelectionTest(unittest.TestCase):
    def setUp(self):
        self.approved = (ROOT / 'scope.json').read_bytes()
        policy = json.loads(self.approved)
        policy['tests']['timeout_seconds'] = 120
        self.original = encode(policy)

    def test_exact_approved_migration_and_unchanged_policies(self):
        self.assertEqual(digest(self.original), ORIGINAL_SHA256)
        self.assertEqual(digest(self.approved), MIGRATED_SHA256)
        self.assertEqual(select_scope(self.original, self.approved), self.approved)
        for policy in [self.original, self.approved]:
            self.assertEqual(select_scope(policy, policy), policy)

    def test_weakened_gates_and_unrelated_edits_are_rejected(self):
        changes = [
            ('tests', 'timeout_seconds', 601),
            ('tests', 'command', ['true']),
            ('tests', 'format', 'junit'),
            ('policy', 'allow_skipped_tests', True),
            ('required_coverage', 'req', []),
            (None, 'inputs', ['README.md']),
            (None, 'review_paths', []),
            (None, 'test_paths', []),
            (None, 'name', 'another-project'),
        ]
        for parent, field, value in changes:
            with self.subTest(parent=parent, field=field):
                policy = copy.deepcopy(json.loads(self.approved))
                target = policy[parent] if parent else policy
                target[field] = value
                with self.assertRaisesRegex(ValueError, 'unapproved scope change'):
                    select_scope(self.original, encode(policy))

    def test_unknown_reversed_and_reformatted_migrations_are_rejected(self):
        for baseline, candidate in [
            (self.approved, self.original),
            (self.original + b' ', self.approved),
            (self.original, self.approved + b' '),
        ]:
            with self.subTest(baseline=digest(baseline), candidate=digest(candidate)):
                with self.assertRaisesRegex(ValueError, 'unapproved scope change'):
                    select_scope(baseline, candidate)

    def test_cli_retains_policy_and_receipt_and_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline, candidate, output, receipt = [root / name for name in
                                                     ['base', 'candidate', 'selected', 'receipt']]
            baseline.write_bytes(self.original)
            candidate.write_bytes(self.approved)
            command = [sys.executable, str(ROOT / 'scripts/ci_scope.py'),
                       '--baseline', str(baseline), '--candidate', str(candidate),
                       '--output', str(output), '--record', str(receipt)]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), self.approved)
            self.assertEqual(baseline.read_bytes(), self.original)
            record = json.loads(receipt.read_text())
            self.assertEqual(record['baseline_scope_sha256'], ORIGINAL_SHA256)
            self.assertEqual(record['selected_scope_sha256'], MIGRATED_SHA256)
            self.assertEqual(record['changed_fields'], ['tests.timeout_seconds'])
            output.unlink()
            receipt.unlink()
            candidate.write_bytes(b'{}')
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())
            self.assertFalse(receipt.exists())
