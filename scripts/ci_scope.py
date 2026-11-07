#!/usr/bin/env python3
"""Select baseline policy, allowing only explicitly reviewed deadline migrations.

Adapted from pinned Clafer Semantics scripts/ci_scope.py (MIT).
Copyright (c) 2026 Kacper Bak; see LICENSE.
Candidate policy is compared, never used to construct trusted policy.
"""

import argparse
import hashlib
import json
from pathlib import Path


ORIGINAL_SHA256 = "7209c4746455221aca57b7a884e133e4c38460dd180550323fe50b2c49c12449"
MIGRATED_SHA256 = "796e137352b837af1042ca51f875749f1bf0152ac6439d3ce8678f475f26ba77"

EXTENDED_SHA256 = "ad905b4cf0e2e275f60cc7aae01d09c7359732b80f8ae16e816392850838f7a5"


def digest(data):
    return hashlib.sha256(data).hexdigest()


# [impl->req~intentbond-workflow~1]
def select_scope(baseline, candidate):
    if candidate == baseline:
        return baseline
    migrations = {ORIGINAL_SHA256: (600, MIGRATED_SHA256),
                  MIGRATED_SHA256: (1200, EXTENDED_SHA256)}
    if digest(baseline) not in migrations:
        raise ValueError("unapproved scope change: baseline is not the approved migration source")
    deadline, expected = migrations[digest(baseline)]
    policy = json.loads(baseline)
    policy["tests"]["timeout_seconds"] = deadline
    migrated = (json.dumps(policy, indent=2) + "\n").encode()
    if digest(migrated) != expected or candidate != migrated:
        raise ValueError("unapproved scope change: only the exact reviewed deadline is permitted")
    return migrated


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--record", type=Path, required=True)
    args = parser.parse_args()
    baseline, candidate = args.baseline.read_bytes(), args.candidate.read_bytes()
    selected = select_scope(baseline, candidate)
    record = {
        "migration": f"check-deadline-{json.loads(selected)['tests']['timeout_seconds']}" if selected != baseline else None,
        "baseline_scope_sha256": digest(baseline),
        "candidate_scope_sha256": digest(candidate),
        "selected_scope_sha256": digest(selected),
        "changed_fields": ["tests.timeout_seconds"] if selected != baseline else [],
    }
    args.output.write_bytes(selected)
    args.record.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, sort_keys=True))


if __name__ == "__main__":
    main()
