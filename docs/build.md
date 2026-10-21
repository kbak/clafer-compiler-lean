# Build and assurance bootstrap

The build belongs to [issue #5](https://github.com/kbak/clafer-compiler-lean/issues/5).
The structural contract was adopted through [PR #22](https://github.com/kbak/clafer-compiler-lean/pull/22).
Build, oracle and IR tasks #5–#7 are accepted through PRs #23–#25. The
[structural IR and admission bridge](ir.md), accepted independent
[target core](alloy-core.md), [structural backend](structural-encoding.md), and
partial [representation proofs](structural-correctness.md) have separate boundaries.
No parser, serialized Alloy output or global preservation theorem is delivered.

## Package and module ownership

The [toolchain](../lean-toolchain), [Lake configuration](../lakefile.toml) and
[manifest](../lake-manifest.json) pin Lean 4.35.0, Clafer Semantics
`1454e3bd2ce9697923cdcef3863c816651ffc147` and its inherited Mathlib/dependency commits.
There is no path dependency, semantic fork or vendored semantic definition.
Haskell remains the syntax/comparison guide pinned in [sources](sources.md);
its [comparison profile](oracles.md) belongs to #6, and it is not a native dependency.

| Root | Role and owner | Allowed project dependencies |
| --- | --- | --- |
| `ClaferCompiler.Frontend` | Empty ownership root; #16–#18 | Runtime modules |
| `ClaferCompiler.IR` | Executable structural tables/admission; #7, expressions later #14 | Runtime modules |
| `ClaferCompiler.Backend.Alloy` | Independent static syntax, bounded semantics; #8, then #9/#10/#15 | Runtime modules |
| `ClaferCompiler.Driver` | Pure bootstrap response; #5, then #19/#20 | Runtime modules |
| `ClaferCompiler.SemanticsBridge` | Structural interpretation/admission proofs; #7, expressions later #14 | Runtime/proof modules and upstream |
| `ClaferCompiler.Correctness` | Bootstrap, local generation and finite representation proofs; #5/#10/#11, then #15/#20 | Runtime/proof modules and upstream |
| `ClaferCompiler` | Public aggregate for proof consumers | Owned library modules |
| `Main` | Native IO entrypoint; #5, then #19/#20 | Runtime modules only |
| `tests` | All Lean test modules | Library, entrypoint and upstream |

Runtime imports are transitively kept outside `SemanticsBridge`, `Correctness`,
the aggregate and all four upstream roots. Libraries cannot import `Main` or tests.
The upstream smoke module imports only the independent upstream public roots.
Cycles, missing local imports, symlinked sources and unknown roots fail. Within
`Backend`, only the `Alloy` responsibility is currently selected. Other backends
require their own scope decision. Upstream's pinned clean sources retain their
one-way `Clafer -> FormalCD -> DPGraph -> Mathlib` graph; downstream cannot add a
reverse upstream dependency without changing the audited pin/source identity.

## Validation and trust

Run the setup and check commands in [CONTRIBUTING](../CONTRIBUTING.md#setup-and-validation).
[Dependency preparation](../scripts/prepare_dependencies.sh) fetches the committed
manifest and builds the independent upstream package. The optional Mathlib binary
cache saves compilation; failure falls back to source builds. It supplies no new
compiler proof evidence. The toolchain, pinned dependencies and their build artifacts
are trusted inputs; this task does not re-audit all upstream declarations.

[The full check](../scripts/check.sh) discovers sources before building. Lake's
recursive globs and explicit targets cover every module and Lean test, including
unimported helpers. It then checks clean Git identities for every dependency,
generates an `import all` audit, exercises native/Python regressions and invokes
`leanchecker --verbose ClaferCompiler Main tests`. Kernel replay and axiom audit
run on every check even when Lake reuses unchanged compiled artifacts.

[The axiom audit](../scripts/axiom_audit.lean) selects declarations by originating
module, including private names and generated declarations. It rejects project
axioms and unsafe/partial definitions, and checks transitive axiom dependencies
against Lean's standard `propext`, `Classical.choice`, `Quot.sound` allowlist.
The inventory additionally rejects textual proof escapes even in an unreferenced
`example` with warnings disabled. Comments and strings are not declarations.
Audit fixtures check both this distinction and suppressed `sorry` warnings.

The generated audit is tooling, not verified compiler code. Python, Bash, Git,
Lake, Lean's elaborator/kernel/checker, the audit metaprogram and IntentBond/OFT
are part of the assurance tool boundary. Native execution additionally trusts
Lean's code generator, C compiler/linker, runtime and operating system. `main` in `Main`
performs IO; the two pure equations below do not prove IO or machine-code behavior.
The native tests exercise stdout, stderr and exit status independently.

`scope.json` already includes all source and review paths and retains its original
coverage policy, command and 120-second check deadline. Provision dependencies
before checking. After the build and axiom audit, kernel replay and the isolated
regression suite run concurrently. Replay uses one worker to bound the number of
large imported environments resident at once; the check waits for both results
and fails if either fails. No module, test or kernel gate is skipped.
CI's overall 30-minute job budget includes dependency downloads
and compilation. It compares candidate scope bytes with the baseline and refuses
an unreviewed amendment. IntentBond exit 4 always leaves semantic review pending.
An external package cache may be copied into a fresh snapshot; its source commits
are verified and compiler outputs are not restored. No check has a skip mode.

The header parser, audit and audit-fixture runner adapt
`scripts/project_modules.py`, `tests/axiom_audit.lean` and `tests/test_axiom_audit.py`
from the pinned Clafer Semantics commit, copyright 2026 Kacper Bak, MIT.
The repository's [MIT notice](../LICENSE) preserves that attribution/license.
No Haskell source or fixture is redistributed.

## Build implementation

`impl~compiler-build-bootstrap~1`

[Driver](../ClaferCompiler/Driver.lean) defines `ClaferCompiler.Driver.version` and
`response`; [Main](../Main.lean) defines `main`. The package files above make these
a native executable. [Module discovery](../scripts/project_modules.py) implements
`inventory`, `validate`, `check_dependencies` and `audit_source`. The full check,
audit and [test runner](../scripts/run_tests.py) enforce the required gates.
[CI](../.github/workflows/ci.yml) runs the same check through pinned IntentBond on
manual dispatch. Push and pull-request triggers are deferred during development;
the full local check remains mandatory before handoff.

Covers:
- `req~compiler-build~1`
- `req~compiler-boundaries~1`

## Bootstrap response proofs

`proof~compiler-bootstrap-response~1`

[Correctness](../ClaferCompiler/Correctness.lean) declares
`ClaferCompiler.Correctness.version_response` and `empty_response`. Both have no
hypotheses and prove definitional equalities about the pure `Driver.response` by
`rfl`: `--version` returns the version string; empty arguments return `none`.
Their axiom dependencies are empty. These are build witnesses, not soundness,
completeness, frontend, upstream semantics or native execution theorems.

Covers:
- `req~compiler-build~1`

## Build and boundary tests

`utest~compiler-build-gates~1`

[Smoke](../tests/Smoke.lean) checks rejecting response equations and proof exports.
[Upstream](../tests/Upstream.lean) independently imports `DPGraph`, `FormalCD`,
`Clafer` and checks `DPGraph.Span.red_comp`, `FormalCD.Hom` and
`Clafer.Verification.check_correct` without re-stating their meanings.
[Native tests](../tests/test_native.py) execute the linked program.
[Inventory regressions](../tests/test_project_modules.py) exercise unimported
helpers, unknown roots, dependency boundaries, cycles, missing tests and escapes.
[Audit regressions](../tests/test_axiom_audit.py) compile isolated private/generated
declarations and test real audit rejection, including suppressed warnings.
[Gate regressions](../tests/test_check_script.py) exercise failed/missing tools,
propagation of each required gate's failure, and empty/skipped/failed test suites.

Covers:
- `req~compiler-build~1`
- `req~compiler-boundaries~1`
