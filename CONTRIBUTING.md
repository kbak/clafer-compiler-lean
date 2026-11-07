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

`main` requires pull requests, the Lean proofs and native CLI check, and resolved
review conversations.
Force pushes and branch deletion are blocked. Passing CI does not grant semantic
acceptance; changes to proof contracts require independent review.

### Ticket readiness

Use **Todo → Ready → In Progress → Done**. Todo covers queued work with unmet
prerequisites or unresolved scope. Ready is limited to actionable tickets whose
hard dependencies are completed and accepted, including dependencies in the other
repository. Roadmap containers stay out of Ready. Ready makes a task available
for selection; manual intake is still required. Mark In Progress when selected
work actually starts, and Done only after acceptance and required review.

```sh
python3 scripts/tickets.py track NUMBER --status ready
python3 scripts/tickets.py track NUMBER --status in-progress
```

After accepted closure, reopening, dependency edits or scope changes, manually
reconcile affected unstarted tickets in both repositories' Projects. Promote
eligible Todo tickets to Ready; return newly blocked Ready tickets to Todo.
Closed as not planned is not accepted completion. Native blocked-by links record
hard dependencies; parent/sub-issue membership groups scope. Coordinate changes
to active work with its owner. The helper sets the requested status; it neither
checks dependencies nor installs automatic readiness synchronization.

### Behavioral integration

Behavioral feature branches use `codex/behavioral-...` and PRs target `behavioral`.
The [behavioral contract](docs/behavioral.md) owns the full feature and assurance
matrix, explicit static-profile separation and final two-repository gates.
Keep `Closes #N` in feature PRs, then explicitly close the issue and mark Done
after the accepted merge: GitHub may not auto-close issues on a non-default base.
Keep the accepted commit, actual APIs/theorems/assumptions, fixtures and matching
evidence with the handoff. Update readiness after acceptance; publication and
passing automation alone do not complete an issue.

Pin accepted upstream semantics by immutable SHA, never a moving `behavioral`
branch or unaccepted PR head. S7 semantic qualification precedes C10 compiler
qualification; upstream S8 main integration requires both. Downstream C11 then
repins the actual merged upstream-main SHA and repeats full qualification before
its own reviewed main merge. Main merges and releases require concrete authorization.

Behavioral integration requires the same check/review controls: up-to-date required
`Lean proofs and native CLI`, PR review, resolved conversations, administrator
enforcement, and no force pushes or deletion. Review minimums may retain the
single-maintainer zero-minimum policy without waiving independent semantic review.
Inspect hosted protection/rulesets separately and retain readback outside source;
report missing controls rather than treating a workflow file as proof of protection.

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
python3 scripts/oracles/temporal.py prepare \
  --static-tools "$CLAFER_ORACLE_TOOLS" \
  --build-cache /tmp/clafer-temporal-build-UNIQUE /tmp/clafer-temporal-tools-UNIQUE
export CLAFER_TEMPORAL_TOOLS=/tmp/clafer-temporal-tools-UNIQUE/tools.json
python3 scripts/oracles/pr113.py prepare \
  --static-tools "$CLAFER_ORACLE_TOOLS" \
  --build-cache /tmp/clafer-pr113-build-UNIQUE /tmp/clafer-pr113-tools-UNIQUE
export CLAFER_PR113_TOOLS=/tmp/clafer-pr113-tools-UNIQUE/tools.json
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
[development skill at the pinned revision](https://github.com/kbak/intentbond/blob/f9b4f9e40722dc6a83067ac9e62480159322dd09/intentbond/skills/intentbond/SKILL.md)
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
share another. The PR113 corpus runs before the other groups so its bounded
solver queries do not compete with Lean compilation. It runs at most two
independent cases concurrently, capped by available CPUs. After that phase,
the remaining groups share a bounded executor. The runner rejects
missing prerequisites, empty/skipped tests and unowned modules.

IntentBond runs the command in a fresh source snapshot. To reuse only the prepared
dependency packages, export `CLAFER_COMPILER_PACKAGES="$PWD/.lake/packages"` before
`ib check`. The snapshot copies them and verifies their clean, pinned Git identities;
project outputs are rebuilt unless Lake's native artifact cache is explicitly
selected with `LAKE_ARTIFACT_CACHE=true` and an external `LAKE_CACHE_DIR`.
Lake checks source/options/import traces and restores artifacts locally for the
mandatory axiom audit and kernel replay. No proof/test result is reused.
No private paths or credentials belong in source.

The scope selects all files and review paths. Its reviewed execution deadline is
1200 seconds; this is a failure ceiling, not a runtime target. Coverage floors,
check command and all gates are unchanged.
Dependency preparation is outside that deadline; CI allows 45 minutes for
provisioning and validation.

PRs outside `behavioral` and pushes to `main` run the Lean build, axiom audit, kernel replay,
native source/IR CLI tests and scope-policy tests. Run the full local IntentBond
check before handoff. PRs targeting `behavioral`, pushes to `behavioral`, and
GitHub Actions → CI → Run workflow run the full suite,
including Haskell/Alloy comparisons and all regressions. A passing routine CI run
is not full qualification evidence.

CI separately caches pinned dependency packages, native Lake artifacts, Mathlib
downloads, verified static/temporal exporters, Alloy and OFT. A semantics repin does
not invalidate unchanged Haskell tools. Exporter recipes and binary/source receipts
are verified on reuse; cold exporters share the pinned Stack/GHC package store.
Full IntentBond runs use an isolated source snapshot and run every validation gate.
The axiom audit, regression suite and kernel replay run in sequence to avoid CPU
and memory contention. After the exclusive PR113 phase, regression groups default
to two workers; CI selects three. Set `CLAFER_TEST_JOBS=1..4`
to select a limit, still bounded by CPU availability.
CI summaries and retained logs report gate and regression-group durations.
Preparation builds all imported upstream modules, including telematics examples.
The workflow permits only the exact reviewed `120` → `600` and `600` → `1200` deadline migrations;
it retains the original comparison baseline and records both policy hashes.
Every other scope amendment needs explicit review before selection as trusted policy.
When checking across this migration locally, supply the reviewed scope explicitly
with `--scope` to both `ib check` and `ib verify`.

## Lean trace annotations

The pinned IntentBond imports OFT tags from Lean line, nested block and
documentation comments, retaining original `.lean` paths and physical lines.
Place `impl`, `proof` and `utest` tags immediately before the relevant definitions,
actual theorems and assertions or test entry points. Use ordinary `--` line comments,
including when one declaration supports several requirements. Put tags before an
existing declaration doc comment to preserve its attachment. Do not collect a
file's links in its module header. One tag can introduce a contiguous group for
the same requirement; repeat it for a separate group only when that gives a useful
source location. Helpers and pure import aggregators need no arbitrary tags.

Only link declarations that supply evidence for the contract. A Markdown artifact
may discuss several requirements and modules together, so its file list does not
justify copying all its links onto each file. Preserve those named artifacts as
explanations of source correspondence and assumptions.

Strings and escaped identifiers do not supply coverage. The source-import
regression checks a real module through the installed checker and fails if a
future pin silently drops Lean artifacts. OFT validates declared relationships;
the build/kernel checks establish theorem checking, and review assesses whether
the statements and assertions satisfy the linked requirements.

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
