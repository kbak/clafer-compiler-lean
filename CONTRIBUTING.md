# Contributing

Start with [intent](docs/intent.md), [requirements](docs/spec.md), the
[architecture contract](docs/architecture.md) and [source register](docs/sources.md).
The repository is private. Structural Clafer-to-Alloy development is the selected
direction; contract review and explicit manual intake of each task precede
implementation. A Todo ticket or this documentation does not start compiler work.
The current checkout still has no Lean toolchain or compiler implementation.

## Issues and pull requests

Search existing issues first. Describe outcome, scope, acceptance criteria,
validation, affected requirement IDs, source references, and dependencies. Use the
[private board](https://github.com/users/kbak/projects/3) to track Todo, In Progress,
and Done. `python3 scripts/tickets.py --help` lists issue and board operations;
GitHub CLI authentication needs repository and Project access. Use `--no-project`
when Project access is unavailable and leave reconciliation to a maintainer.

Use a focused branch, link PRs with `Closes #N`, and describe the behavior and
validation evidence. Review scope changes explicitly. Mark tasks Done only after
their acceptance criteria are met. Planning issues are not implementation approval.
IntentMade uses manual intake and draft PRs. Only its credential-bearing coordinator
may run ticket operations; workers return proposed updates without credentials.

## Setup and validation

Python 3.11+, Git, Bash and Java 17+ are required for the complete check.
Install the pinned checker in an environment outside the source tree:

```sh
python3 -m venv ../clafer-compiler-tools
../clafer-compiler-tools/bin/pip install -r requirements/intentbond.txt
../clafer-compiler-tools/bin/ib install-oft
```

Before editing, capture `git rev-parse HEAD` as `BASE_COMMIT`. Read the
[development skill at the pinned revision](https://github.com/kbak/intentbond/blob/a430efa8d82e2a88ed2607bfe838066bb9d73f3c/intentbond/skills/intentbond/SKILL.md)
and applicable references. Maintain intent, requirements, implementation and links
together, then run:

```sh
bash scripts/check.sh
../clafer-compiler-tools/bin/ib check --repo "$PWD" --base "$BASE_COMMIT"   --candidate worktree --out /tmp/clafer-compiler-evidence-UNIQUE
```

Use a new evidence directory outside the repository each time. The normal check
uses scope from the baseline; initial scope adoption requires explicit review and
an explicitly supplied scope. Exit 4 means automated checks passed with semantic
review pending. It does not approve a change. Preserve the original baseline for
`ib verify` after committing; retain evidence and unresolved review items.

Current checks validate JSON, Python/shell syntax, local Markdown file links and
conflict markers. They do not run Lean. Add real build and proof checks alongside
the future toolchain decision, with a reviewed scope update.

## Documentation and conduct

Keep the README brief and current intent in `docs/intent.md`. Use lowercase,
hyphen-separated documentation names. Keep runtime state, credentials, transcripts
and execution evidence out of source. Cite exact upstream revisions and check
licenses before copying material. Be respectful, constructive, and specific in
reviews. Contact the maintainer privately about conduct or sensitive concerns.
