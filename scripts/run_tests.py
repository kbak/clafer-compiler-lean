#!/usr/bin/env python3
"""Run every Python regression, failing on empty, skipped or failed suites.

CLI, source-pipeline comparison and audit fixtures run alongside other regressions.
All groups are mandatory; process isolation keeps module state and mocks separate.
"""
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
import sys
import unittest


ISOLATED_GROUPS = {
    '--isolated-worker': {'test_cli', 'test_cli_external', 'test_axiom_audit', 'test_comparison'},
    '--source-worker': {'test_source_cli', 'test_source_pipeline'},
    '--frontend-worker': {'test_constraints', 'test_parser', 'test_resolution', 'test_qualification'},
    '--target-worker': {'test_alloy_core', 'test_alloy_text', 'test_expression_encoding',
        'test_expressions', 'test_inherited', 'test_integer_arithmetic',
        'test_structural_alloy', 'test_structural_ir', 'test_structural_representation'},
}
ISOLATED_MODULES = set.union(*ISOLATED_GROUPS.values())


def cases(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from cases(item)
        else:
            yield item


def run(suite):
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return result.wasSuccessful() and result.testsRun > 0 and not result.skipped


# [impl->req~compiler-build~1]
# [impl->req~compiler-cli~1]
if len(sys.argv) == 2 and sys.argv[1] in ISOLATED_GROUPS:
    groups = [unittest.defaultTestLoader.discover('tests', pattern=name+'.py')
              for name in sorted(ISOLATED_GROUPS[sys.argv[1]])]
    if any(group.countTestCases() == 0 for group in groups):
        raise SystemExit('Each isolated module must contain tests')
    suite = unittest.TestSuite(groups)
    raise SystemExit(0 if run(suite) else 1)
if sys.argv[1:]:
    raise SystemExit('Usage: run_tests.py (all groups are mandatory)')

suite = unittest.defaultTestLoader.discover('tests', pattern='test_*.py')
all_cases = list(cases(suite))
present = [Path('tests',name+'.py').is_file() for name in ISOLATED_MODULES]
if any(present) and not all(present):
    raise SystemExit('All isolated modules are required')
if all(present):
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else (os.cpu_count() or 1)
    worker_count = max(1, min(4, cpus))
    print(f'Regression groups: {len(ISOLATED_GROUPS) + 1}; workers: {worker_count}', flush=True)
    def isolated(flag):
        return subprocess.run([sys.executable, str(Path(__file__).resolve()), flag]).returncode == 0
    with ThreadPoolExecutor(max_workers=worker_count) as pool:
        futures = [pool.submit(isolated, flag) for flag in ISOLATED_GROUPS]
        remaining = unittest.TestSuite(t for t in all_cases
                                       if t.__class__.__module__ not in ISOLATED_MODULES)
        futures.append(pool.submit(run, remaining))
        results = [future.result() for future in futures]
    raise SystemExit(0 if all(results) else 1)
raise SystemExit(0 if run(unittest.TestSuite(all_cases)) else 1)
