# Contributing

Start with [intent](docs/intent.md), [requirements](docs/spec.md), the
[architecture contract](docs/architecture.md) and [source register](docs/sources.md).
Discuss proposed compiler features in an issue before implementing them so their
scope, semantic contract and dependencies can be reviewed. Bug reports,
documentation improvements and focused fixes are welcome.
See the [documentation map](docs/intent.md#documentation-map) for component contracts
and the [qualification inventory](docs/qualification.md#feature-and-evidence-inventory)
for supported features and their evidence.

## Issues and pull requests

Search [existing issues](https://github.com/kbak/clafer-compiler-lean/issues) first.
For bugs, include the compiler revision, input, expected result and actual result.
For proposed features, describe scope, acceptance criteria, validation, affected
requirements, source references and dependencies.

Fork the repository and open a pull request from a focused branch. Contributors
can use GitHub directly; access to the maintainer
[Project](https://github.com/users/kbak/projects/3) is not required.
`python3 scripts/tickets.py --help` lists optional issue and board operations; use
`--no-project` when Project access is unavailable.

Link pull requests to their issue with `Closes #N` and describe the behavior and
validation evidence. Review scope changes explicitly. Mark tasks Done only after
their acceptance criteria are met. New compiler features require maintainer
selection and accepted dependencies.

`main` requires pull requests, the full CI check and resolved review conversations.
Force pushes and branch deletion are blocked. Passing CI does not grant semantic
acceptance; changes to proof contracts require independent review.

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

Python 3.11+, Git, Bash, Java 17+, Elan, a C toolchain, `ldd`, GNU time and Bubblewrap
with working user namespaces are required for validation. The native runtime
check currently targets Linux/glibc; ordinary compilation needs only the
[documented native runtime](docs/cli.md#native-runtime).
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
export CLAFER_COMPILER_PACKAGES="$PWD/.lake/packages"
../clafer-compiler-tools/bin/ib check --repo "$PWD" --base "$BASE_COMMIT" \
  --candidate worktree --out /tmp/clafer-compiler-evidence-UNIQUE
```

IntentBond runs `bash scripts/check.sh`; running it separately is optional during
development. Use a new evidence directory outside the repository each time.
The normal check uses scope from the baseline; initial scope adoption requires explicit review and
an explicitly supplied scope. Exit 4 means automated checks passed with semantic
review pending. It does not approve a change. Preserve the original baseline for
`ib verify` after committing; retain evidence and unresolved review items.

Set `CLAFER_ORACLE_EVIDENCE` to an external directory to retain oracle runs
(otherwise each run creates a fresh directory under the system temporary directory).
The shared check validates syntax/links, inventories all Lean modules, builds
libraries/tests/native code, exercises the real pinned comparison tools, audits project declarations and their transitive
axioms, runs all Python/native regressions, and replays the kernel. M1 comparison,
CLI and audit regressions share one worker; source CLI and pipeline comparisons
share another, alongside the remaining tests. It rejects
missing prerequisites, empty/skipped tests and unowned modules.

IntentBond runs the command in a fresh source snapshot. To reuse only the prepared
dependency packages, export `CLAFER_COMPILER_PACKAGES="$PWD/.lake/packages"` before
`ib check`. The snapshot copies them and verifies their clean, pinned Git identities;
project outputs are rebuilt. No private paths or credentials belong in source.

The scope selects all files and review paths. Its reviewed execution deadline is
600 seconds; coverage floors, check command and all gates are unchanged.
Dependency preparation is outside that deadline; CI allows 45 minutes for
provisioning and the check.
CI runs on pull requests, pushes to `main` and manual dispatch. Run the full local
IntentBond check before handoff; use GitHub Actions → CI → Run workflow for an
additional hosted run. Preparation builds all imported upstream modules, including
telematics examples, and retains their cache before checking the project.
CI caches only pinned dependencies and external tools,
then checks their identities and rebuilds the project in the source snapshot.
The workflow permits only the exact reviewed `120` → `600` deadline migration;
it retains the original comparison baseline and records both policy hashes.
Every other scope amendment needs explicit review before selection as trusted policy.
When checking across this migration locally, supply the reviewed scope explicitly
with `--scope` to both `ib check` and `ib verify`.

## Documentation and conduct

Keep the README focused on capabilities, getting started and assurance limits.
`docs/intent.md` owns the documentation map; requirements live in `docs/spec.md`,
interfaces and proof boundaries in component contracts, and source identities in
`docs/sources.md`. Link to the authoritative page instead of repeating its content.
Record task history and before/after accounts in issues and PRs.

Write current behavior directly, using short paragraphs and descriptive headings.
Use backticks for identifiers, paths, filenames, commands, options, literal values
and traceability IDs; use fenced blocks with a language for examples. Keep prose
link labels descriptive: name the decision or contract instead of writing only an
issue or PR number. Link relevant reviews when readers need their rationale; keep
implementation timelines in those reviews. Preserve exact source revisions, theorem assumptions and
proof-versus-test distinctions. Use lowercase, hyphen-separated documentation names
and check local links and examples when editing.

Keep runtime state, credentials, transcripts and execution evidence out of source.
Check licenses before copying material. Be respectful, constructive and specific in
reviews. Use the [private reporting guidance](SECURITY.md) for conduct or sensitive
concerns. Disagreement about a model or proof should address the claim and evidence;
harassment and disclosure of another person's private information are unacceptable.
