<a id="build-and-assurance-bootstrap"></a>

# Build and validation

The build separates native runtime modules from proof dependencies, inventories
all owned modules, and checks the compiler against its pinned tools and semantics.
Component contracts state the [structural preservation](structural-correctness.md),
[expression](expressions.md), [source pipeline](pipeline.md) and
[serialization](alloy-text.md) proof boundaries. Native execution and external
Analyzer correspondence are tested separately.

## Package and module ownership

The [toolchain](../lean-toolchain), [Lake configuration](../lakefile.toml) and
[manifest](../lake-manifest.json) pin Lean 4.35.0, Clafer Semantics
`1454e3bd2ce9697923cdcef3863c816651ffc147` and its inherited Mathlib/dependency commits.
There is no path dependency, semantic fork or vendored semantic definition.
Haskell remains the syntax/comparison guide pinned in [sources](sources.md);
its [comparison profile](oracles.md) is external to the native runtime.

| Root | Role and owner | Allowed project dependencies |
| --- | --- | --- |
| `ClaferCompiler.Frontend` | Authored parser, checked declaration resolution and constraint elaboration | Runtime modules |
| `ClaferCompiler.IR` | Executable structural/inherited tables, admission and typed expressions | Runtime modules |
| `ClaferCompiler.Backend.Alloy` | Independent static syntax, bounded semantics, encoding and serialization | Runtime modules |
| `ClaferCompiler.Driver` | Native source/IR commands, strict JSON, bounds and diagnostics | Runtime modules |
| `ClaferCompiler.SemanticsBridge` | Structural/inherited interpretation, admission, expressions and source elaboration proofs | Runtime/proof modules and upstream |
| `ClaferCompiler.Correctness` | Response, generation, preservation, arithmetic and full source-model proofs | Runtime/proof modules and upstream |
| `ClaferCompiler` | Public aggregate for proof consumers | Owned library modules |
| `Main` | Native IO entrypoint | Runtime modules only |
| `tests` | All Lean test modules | Library, entrypoint and upstream |

Runtime imports are transitively kept outside `SemanticsBridge`, `Correctness`,
the aggregate and all four upstream roots. Libraries cannot import `Main` or tests.
The upstream smoke module imports only the independent upstream public roots.
The exact pinned-toolchain JSON imports `Lean.Data.Json.Parser`
and `Lean.Data.Json.FromToJson.Basic` are admitted for driver library reuse; arbitrary
`Lean`/elaborator imports remain rejected. Cycles, missing local imports, symlinked
sources and unknown roots fail. Within
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
are trusted inputs; the audit does not recheck all upstream declarations.

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

Runtime optimizations use Lean's standard `@[csimp]` mechanism with kernel-checked
function equalities: cached backend indices, shared rendering chunks and bounded
rank iteration that stops at a fixed point. The specification definitions remain
available to proofs. These equalities cover Lean-level results; they do not verify
the code generator or C toolchain. Native regressions and the
[measurement harness](qualification.md#measurements-and-replay) check that boundary.

`scope.json` includes all source and review paths, with a 600-second check deadline.
The reviewed deadline amendment changes no coverage policy, command or gate.
Provision dependencies before checking. After the build, the axiom audit, kernel replay and the isolated
regression suite run concurrently. Every process is awaited and every exit status
must succeed. Replay uses two workers to bound the number of
large imported environments resident at once. Failures in the audit, replay or
regressions fail the check. No module, test or kernel gate is skipped.
The regression runner partitions the discovered tests into isolated concurrent
groups; every group must execute without skips and pass. It retains every
discovered case and propagates each group's failure.
CI's overall 45-minute job budget includes dependency downloads
and compilation. It compares candidate scope bytes with the baseline and permits
only the exact reviewed deadline migration described below. IntentBond exit 4
always leaves semantic review pending.
An external package cache may be copied into a fresh snapshot; its source commits
are verified and compiler outputs are not restored. No check has a skip mode.

The header parser, audit and audit-fixture runner adapt
`scripts/project_modules.py`, `tests/axiom_audit.lean` and `tests/test_axiom_audit.py`
from the pinned Clafer Semantics commit, copyright 2026 Kacper Bak, MIT.
The repository's [MIT notice](../LICENSE) preserves that attribution/license.
No Haskell source or fixture is redistributed.

## Build implementation

`impl~compiler-build-bootstrap~1`

[Driver](../ClaferCompiler/Driver.lean) defines `ClaferCompiler.Driver.version`,
`response`, `compileText`, `compileSource` and `run`; [Main](../Main.lean) defines
`main`. See the [CLI contract](cli.md) for runtime-only verification. The
package files above make these a native executable.
[Module discovery](../scripts/project_modules.py) implements
`inventory`, `validate`, `check_dependencies` and `audit_source`. The full check,
audit and [test runner](../scripts/run_tests.py) enforce the required gates.
[CI](../.github/workflows/ci.yml) runs the same check through pinned IntentBond on
pull requests, pushes to `main` and manual dispatch. The full local check remains
mandatory before handoff. GitHub's cache action, already used by pinned Clafer
Semantics, reuses dependency packages and external comparison tools under keys
derived from the toolchain, dependency manifest, oracle profile and preparation
scripts. Preparation
and clean-pin/tool-identity checks still run after restoration; project build
outputs and successful proof/test results are not restored. There is no alternate
reduced CI suite or added runtime dependency.

Public CI artifacts retain check logs, source identities, notices, generated text,
solver witnesses and replay inputs for 30 days. The pinned `upload-artifact`
action's path exclusions omit compiled test executables, Java classes and the
downloaded Haskell source archive; no separate packaging tool or dependency is
needed. Binary hashes and build commands remain in the evidence so reviewers can
rebuild with the pinned tools. Tests still build and execute every native probe.
When adding a probe, keep its compiled output out of the public artifact paths.

The [scope selector](../scripts/ci_scope.py) adapts the pinned Clafer Semantics
`scripts/ci_scope.py` (MIT, copyright 2026 Kacper Bak). IntentBond already accepts
external trusted policy; plain `cmp` cannot distinguish an approved amendment from
an arbitrary edit. The selector constructs the approved `120` → `600` deadline
from the original baseline, pins both byte hashes and rejects every other change.
It never replaces the Git comparison baseline. CI retains the selected policy and
migration receipt. [Regression tests](../tests/test_ci_scope.py) check accepted
policy identities, weakened gates, altered coverage and unknown/reversed migrations.
This is unverified Python review tooling, with no added dependency or runtime code.

Dependency preparation reuses the module inventory and import parser to build all
upstream modules imported by project sources, including the telematics examples
outside the upstream root module. These are pinned dependency outputs; project
outputs are still rebuilt in the check. The regression runner reuses Python's
standard `ThreadPoolExecutor` (also used by the comparison harness) to bound
concurrent groups by CPU availability, with at most four groups. Every discovered
case and each group's exit status remain mandatory. CI uses the cache action's
separate restore/save steps to retain successfully prepared dependencies even if
later project verification fails. This adds no compiler dependency and removes or
relaxes no semantic assertion, input case, per-command limit or trusted check deadline.
Live log forwarding reuses the pinned upstream workflow's `tail --pid` pattern;
the full retained log and check exit status remain authoritative.

CI sets `LEAN_NUM_THREADS=2` for its two-CPU runner; kernel replay also uses two
workers. This bounds Lean's own parallelism as well as regression groups.
Ubuntu's [AppArmor namespace policy](https://documentation.ubuntu.com/security/security-features/privilege-restriction/apparmor/)
requires explicit permission for the runtime-isolation test. CI installs a
dedicated copy of the distribution's Bubblewrap executable and attaches the
[namespace profile](../.github/ci/bwrap.apparmor) to that path. It loads the profile
and probes namespace creation before validation; the real empty-root native test
remains mandatory. This is ephemeral runner provisioning, with no application
runtime dependency or global AppArmor disablement.

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

[Smoke](../tests/Smoke.lean) checks the pure informational-response equations and
proof exports; the full command dispatcher is exercised by the [CLI tests](cli.md#implementation-and-test-trace).
[Upstream](../tests/Upstream.lean) independently imports `DPGraph`, `FormalCD`,
`Clafer` and checks `DPGraph.Span.red_comp`, `FormalCD.Hom` and
`Clafer.Verification.check_correct` without re-stating their meanings.
[Native tests](../tests/test_native.py) execute the linked program.
The [native fixture helper](../tests/native.py) shares temporary entry-point
creation and Lake/C linking for the IR, inherited, representation and expression
tests. It uses Python's standard `subprocess`/`tempfile` with the existing explicit
module lists and 45-second command timeout; fixture selection and assertions stay
in each test. This adds no dependency or proof claim. Evidence-producing Analyzer
harnesses retain their separate source snapshots and command receipts.
[Inventory regressions](../tests/test_project_modules.py) exercise unimported
helpers, unknown roots, dependency boundaries, cycles, missing tests and escapes.
[Audit regressions](../tests/test_axiom_audit.py) compile isolated private/generated
declarations and test real audit rejection, including suppressed warnings.
[Gate regressions](../tests/test_check_script.py) exercise failed/missing tools,
propagation of each required gate's failure, and empty/skipped/failed test suites.

Covers:
- `req~compiler-build~1`
- `req~compiler-boundaries~1`
