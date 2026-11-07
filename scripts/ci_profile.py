#!/usr/bin/env python3
"""Select reviewed CI profiles; unknown inputs require reference qualification."""
import argparse
import copy
import json
from pathlib import Path, PurePosixPath
import subprocess

from ci_scope import digest


REFERENCE_TESTS = {'test_pr113_oracles.py', 'test_temporal_oracles.py'}


def compiler_only(path):
    """Whitelist independent compiler inputs; all other paths invalidate references."""
    p = PurePosixPath(path)
    if p.parts[0] == 'ClaferCompiler' and p.suffix == '.lean':
        return True
    if path in ('ClaferCompiler.lean', 'Main.lean'):
        return True
    if p.parts[0] == 'tests' and p.suffix == '.lean':
        return True
    if len(p.parts) == 2 and p.parts[0] == 'tests' and p.name.startswith('test_') and p.suffix == '.py':
        return p.name not in REFERENCE_TESTS
    return (p.parts[0] == 'docs' and p.suffix == '.md'
            and path not in {'docs/oracles.md', 'docs/sources.md', 'docs/build.md', 'docs/spec.md'})


# [impl->req~intentbond-workflow~1]
def select(repo, event, base_ref, ref, action, baseline):
    candidate = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    result = dict(candidate=candidate, baseline=baseline, profile='routine', reference=False,
                  reason='static CI', reference_inputs=[])
    if event not in {'pull_request', 'push', 'schedule', 'workflow_dispatch'} or (event == 'pull_request' and not base_ref):
        return dict(result, profile='compiler', reference=True,
                    reason='event or target classification unavailable')
    if (event in ('schedule', 'workflow_dispatch') or ref == 'refs/heads/behavioral'
            or (base_ref == 'behavioral' and action == 'ready_for_review')):
        return dict(result, profile='compiler', reference=True,
                    reason='scheduled, manual, integration or acceptance qualification')
    if base_ref != 'behavioral':
        return result
    result['profile'] = 'compiler'
    try:
        if not baseline:
            raise ValueError('missing baseline')
        subprocess.run(['git', 'merge-base', '--is-ancestor', baseline, candidate],
                       cwd=repo, check=True, capture_output=True)
        changed = subprocess.check_output(['git', 'diff', '--name-only', '--no-renames', '-z',
                                           baseline, candidate, '--'], cwd=repo).decode().split('\0')
        affected = [p for p in changed if p and not compiler_only(p)]
        return dict(result, reference=bool(affected), reference_inputs=affected,
                    reason='reference or unclassified inputs changed' if affected else 'only compiler inputs changed')
    except (OSError, ValueError, subprocess.SubprocessError):
        return dict(result, reference=True, reason='baseline/dependency comparison unavailable')


# [impl->req~intentbond-workflow~1]
def profile_scope(data, profile):
    scope = json.loads(data)
    if scope['tests']['command'] != ['bash', 'scripts/check.sh']:
        raise ValueError('Expected the trusted full-check policy')
    if profile == 'full':
        return data
    commands = {'compiler': ['bash', 'scripts/check.sh', '--compiler-ci'],
                'reference': ['bash', 'scripts/check.sh', '--reference-ci'],
                'source': ['bash', 'scripts/check.sh', '--source-ci']}
    if profile not in commands:
        raise ValueError('Unknown qualification profile')
    scope = copy.deepcopy(scope)
    scope['name'] += '/' + profile
    scope['tests']['command'] = commands[profile]
    return (json.dumps(scope, indent=2) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    selection = commands.add_parser('select')
    selection.add_argument('--repo', type=Path, default=Path('.'))
    for name in ('event', 'base-ref', 'ref', 'action', 'baseline'):
        selection.add_argument('--'+name, default='')
    selection.add_argument('--output', type=Path, required=True)
    selection.add_argument('--record', type=Path, required=True)
    policy = commands.add_parser('scope')
    policy.add_argument('--input', type=Path, required=True)
    policy.add_argument('--profile', choices=('full', 'compiler', 'reference', 'source'), required=True)
    policy.add_argument('--output', type=Path, required=True)
    policy.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    if args.command == 'select':
        result = select(args.repo, args.event, args.base_ref, args.ref, args.action, args.baseline)
        with args.output.open('a') as out:
            for key in ('candidate', 'baseline', 'profile', 'reference'):
                out.write(f'{key}={str(result[key]).lower()}\n')
    else:
        original = args.input.read_bytes()
        selected = profile_scope(original, args.profile)
        args.output.write_bytes(selected)
        result = dict(profile=args.profile, full_scope_sha256=digest(original),
                      selected_scope_sha256=digest(selected),
                      reference_execution='required' if args.profile in ('full', 'reference') else 'not run',
                      behavioral_source_execution='required' if args.profile in ('full', 'source') else 'not run')
    args.record.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
