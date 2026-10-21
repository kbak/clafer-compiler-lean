# Contributing

Start with [intent](docs/intent.md), [requirements](docs/spec.md), the
[architecture contract](docs/architecture.md) and [source register](docs/sources.md).
The repository is private. Structural Clafer-to-Alloy development is the selected
direction; contract review and explicit manual intake of each task precede
implementation. A Todo ticket or this documentation does not start compiler work.
The current checkout has a pinned Lean/Lake build, native bootstrap, external
[oracle tools](docs/oracles.md), [structural IR admission](docs/ir.md) and an
[independent Alloy core](docs/alloy-core.md), an accepted
[structural backend](docs/structural-encoding.md), and accepted
[checked serialization](docs/alloy-text.md). Accepted #11 provides
[M1 soundness and bounded completeness](docs/structural-correctness.md) under
explicit finite scope and integer-range hypotheses. Selected #13 adds
[inherited structural realization](docs/inherited-realization.md), pending semantic
acceptance. CLI integration remains separate. Task #12 supplies
[exact three-way comparison](docs/comparison.md) and strict instance export.
Accepted [static parser #16](docs/parser.md) preserves authored syntax. Selected #17
adds [checked structural resolution/defaulting](docs/resolution.md); source
expression typing remains separate. Accepted #14 (PR #32) adds the
[typed expression API](docs/expressions.md) and independent semantic interpretation.
Selected #15 adds [bounded target arithmetic](docs/expression-encoding.md);
source constraint translation and attachment preservation remain unfinished.
See [build and proof checks](docs/build.md).

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

## Reuse before implementation

Check existing repository code, pinned upstream sources, standard libraries and
relevant maintained libraries/tools before implementing. Prefer a reusable solution
that meets the contract. Before writing custom infrastructure, record the candidates
checked and concrete gaps or tradeoffs in the affected design or task notes. Assess
semantic fit, proof and runtime boundaries, maintenance, dependency and license
costs. Independence from another component does not require implementing general
machinery from scratch. Keep unresolved choices explicit; see the
[Alloy parser assessment](docs/alloy-text.md#parser-reuse-assessment).

## Setup and validation

Python 3.11+, Git, Bash, Java 17+, Elan and a C toolchain are required.
`lean-toolchain` selects Lean 4.35.0. Prepare the manifest-pinned dependencies:

```sh
bash scripts/prepare_dependencies.sh
python3 scripts/oracles/oracle.py prepare /tmp/clafer-oracle-tools-UNIQUE
export CLAFER_ORACLE_TOOLS=/tmp/clafer-oracle-tools-UNIQUE/tools.json
```

This fetches source and an optional Mathlib cache, builds the upstream dependency,
then provisions the [comparison tools](docs/oracles.md), requiring GMP headers
(`libgmp-dev` on Ubuntu). Cache download failure falls back to source compilation. Missing
tools or failed builds are failures, never skipped gates.
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
export CLAFER_COMPILER_PACKAGES="$PWD/.lake/packages"
../clafer-compiler-tools/bin/ib check --repo "$PWD" --base "$BASE_COMMIT"   --candidate worktree --out /tmp/clafer-compiler-evidence-UNIQUE
```

Use a new evidence directory outside the repository each time. The normal check
uses scope from the baseline; initial scope adoption requires explicit review and
an explicitly supplied scope. Exit 4 means automated checks passed with semantic
review pending. It does not approve a change. Preserve the original baseline for
`ib verify` after committing; retain evidence and unresolved review items.

Set `CLAFER_ORACLE_EVIDENCE` to an external directory to retain oracle runs
(otherwise each run creates a fresh directory under the system temporary directory).
The shared check validates syntax/links, inventories all Lean modules, builds
libraries/tests/native code, exercises the real pinned comparison tools, audits project declarations and their transitive
axioms, runs all Python/native regressions, and replays the kernel. It rejects
missing prerequisites, empty/skipped tests and unowned modules.

IntentBond runs the command in a fresh source snapshot. To reuse only the prepared
dependency packages, export `CLAFER_COMPILER_PACKAGES="$PWD/.lake/packages"` before
`ib check`. The snapshot copies them and verifies their clean, pinned Git identities;
project outputs are rebuilt. No private paths or credentials belong in source.

The existing scope already selects all files and review paths. Its coverage floors,
check command and 120-second execution deadline are unchanged. Dependency preparation
is outside that deadline; CI allows 30 minutes for provisioning and the check.
During development, CI runs only on manual dispatch, not on pushes or pull requests.
Run the full local IntentBond check before handoff. Use GitHub Actions → CI → Run
workflow when a clean hosted run is needed; automatic CI is deferred until
development is complete.
The workflow refuses differing baseline/candidate scope bytes; any future amendment
needs explicit review before selecting it as trusted policy.

## Documentation and conduct

Keep the README brief and current intent in `docs/intent.md`. Use lowercase,
hyphen-separated documentation names. Keep runtime state, credentials, transcripts
and execution evidence out of source. Cite exact upstream revisions and check
licenses before copying material. Be respectful, constructive, and specific in
reviews. Contact the maintainer privately about conduct or sensitive concerns.
