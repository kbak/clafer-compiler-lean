#!/usr/bin/env python3
"""Run the existing Alloy instance checks in walkthrough order; retain evidence."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


# [impl->req~compiler-differential~1]
# [impl->req~compiler-telematics~1]
def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('output', type=Path, help='new directory outside the repository')
    cli.add_argument('--part', choices=('all', 'structural', 'source'), default='all')
    args = cli.parse_args()
    if not os.environ.get('CLAFER_ORACLE_TOOLS'):
        cli.error('CLAFER_ORACLE_TOOLS is required; see CONTRIBUTING.md')
    output = oracle.external(args.output)
    output.mkdir(parents=True, exist_ok=False)
    os.environ['CLAFER_ORACLE_EVIDENCE'] = str(output)
    oracle.write(output / 'command.json', [sys.executable, *sys.argv])
    oracle.write(output / 'runner.json', oracle.digest(__file__))
    stages = [
        ('structural', 'test_comparison.ComparisonTests.test_actual_decode_and_negative_mutations'),
        ('source', 'test_source_pipeline.SourcePipelineTests.test_exact_candidates_and_mutation_replays'),
    ]
    summary = dict(complete=False, stages=[], explicit='not_requested')
    for name, test in stages:
        if args.part not in ('all', name):
            continue
        print(f'Running {name} instance checks; evidence: {output}', flush=True)
        before = set(output.iterdir())
        with (output / f'{name}.log').open('w') as log:
            # unittest supplies failure/skip accounting; the original suites retain
            # commands, source snapshots, tables, tool identities and solver output.
            result = unittest.TextTestRunner(stream=log, verbosity=2).run(
                unittest.defaultTestLoader.loadTestsFromName(test))
        passed = result.wasSuccessful() and result.testsRun == 1 and not result.skipped
        artifacts = sorted(p.name for p in set(output.iterdir()) - before if p.is_dir())
        summary['stages'].append(dict(name=name, passed=passed, tests=result.testsRun,
                                     evidence=artifacts))
        oracle.write(output / 'summary.json', summary)
        if not passed:
            print((output / f'{name}.log').read_text(), file=sys.stderr)
            return 1
    explicit_tools = os.environ.get('CLAFER_PR113_C7_TOOLS')
    if args.part in ('all', 'source') and explicit_tools:
        import pr113
        tools = pr113.load_tools(explicit_tools)
        if tools['candidate'] != 'c7a2fb7':
            raise ValueError('Explicit supplement requires the registered c7a2fb7 profile')
        source = ROOT / 'tests/fixtures/constraints/telematics.cfr'
        generated = pr113.capture(tools, {'telematics.cfr': source.read_bytes()},
                                 'telematics.cfr', output / 'explicit-telematics', backend='als')
        oracle.write(output / 'explicit-telematics/tools.json', tools['tools'])
        oracle.write(output / 'explicit-telematics/source.json', pr113.identity())
        if generated['status'] != 'captured':
            raise ValueError('Explicit export failed: ' + json.dumps(generated))
        summary['explicit'] = 'captured_supplement_only'
    summary['complete'] = True
    oracle.write(output / 'summary.json', summary)
    oracle.write(output / 'evidence-index.json', {
        str(p.relative_to(output)): oracle.digest(p)
        for p in sorted(output.rglob('*')) if p.is_file()})
    print(f'Completed requested instance checks. Evidence: {output / "summary.json"}', flush=True)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f'Instance demonstration failed: {error}', file=sys.stderr)
        raise SystemExit(1)
