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
`bbf81e44beca6eb6c4ff3f0e87516b15be59676e` and its inherited Mathlib/dependency commits.
There is no path dependency, semantic fork or vendored semantic definition.
Haskell remains the syntax/comparison guide pinned in [sources](sources.md);
its [comparison profile](oracles.md) is external to the native runtime.

| Root | Role and owner | Allowed project dependencies |
| --- | --- | --- |
| `ClaferCompiler.Frontend` | Authored parser, checked declaration resolution and constraint elaboration | Runtime modules |
| `ClaferCompiler.IR` | Executable structural/inherited tables, admission and typed expressions | Runtime modules |
| `ClaferCompiler.Backend.Alloy` | Independent static/temporal syntax, bounded semantics, encoding and serialization | Runtime modules |
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
manifest and builds the independent upstream package, including the native object
closure of `Clafer.Verification.Admission` and
`Clafer.Semantics.RealizationCompatibility` used by the source-candidate harness.
Lake's `linkInfoExport` facet provides that closure without a separate dependency
resolver. The optional Mathlib binary
cache saves compilation; failure falls back to source builds. It supplies no new
compiler proof evidence. The toolchain, pinned dependencies and their build artifacts
are trusted inputs; the audit does not recheck all upstream declarations.

[The full check](../scripts/check.sh) discovers sources before building. Lake's
recursive globs and explicit targets cover every module and Lean test, including
unimported helpers. It then checks clean Git identities for every dependency,
generates an `import all` audit, exercises native/Python regressions and invokes
`leanchecker --verbose ClaferCompiler Main tests`. Kernel replay and axiom audit
run on every full check and routine CI run, even when Lake reuses unchanged
compiled artifacts.

CI retains Lake's traced build artifacts even after a regression fails, so a
retry can reuse completed compilation. It caches no audit, test or kernel verdict;
the full check still runs every gate against the current source.

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

`scope.json` includes all source and review paths, with a 1200-second check deadline.
The reviewed deadline amendment changes no coverage policy, command or gate;
the deadline is a failure ceiling, not a runtime target.
Provision dependencies before checking. After the build, the axiom audit,
isolated regression suite and kernel replay run in sequence. This keeps expensive
replay environments out of each regression's CPU and memory budget. Every gate
runs even if another validation gate failed; every exit status must succeed.
Replay uses two workers to bound large imported environments resident at once. Failures in the audit, replay or
regressions fail the check. No module, test or kernel gate is skipped.
The regression runner runs both revision-specific PR113 corpora first, each with
its existing two case workers, then runs the remaining groups concurrently. The bounded solver queries
in that corpus therefore do not compete with Lean compilation in other suites.
Every group must execute without skips and pass, including after a failed PR113
phase. It retains every discovered case and propagates each group's failure.
The full temporal target suite uses its own early subprocess group, so the
other compiler regressions can overlap its solver work. This reuses the existing
group registry, bounded executor and subprocess isolation rather than adding a
test framework or persistent solver service. Separate processes preserve the
tests' environment and mock isolation; evidence directories remain per suite.
The outer worker cap, temporal suite's two fresh JVM workers, complete case
inventory and query deadlines remain unchanged. Runner fixtures check the new
group's missing, empty, skipped and failing cases as well as serial execution.
CI's overall 45-minute job budget includes dependency downloads
and compilation. It compares candidate scope bytes with the baseline and permits
only the exact reviewed deadline migrations described below. IntentBond exit 4
always leaves semantic review pending.
An external package cache may be copied into a fresh snapshot; its source commits
are verified. An opt-in native Lake artifact cache can also restore unchanged
compiler outputs using source/options/import traces; it never restores validation
results. Lake does not cache the native linker's response file. The check relinks
the executable from the restored objects with artifact reuse disabled for that
command, so an old local response file cannot stand in for current link inputs. Native probes and qualification retain the real
local link inputs. The default full check runs every gate; the explicitly named
CI profiles below retain separate execution evidence.

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
[CI](../.github/workflows/ci.yml) selects the following validation paths:

| Trigger | Checks |
| --- | --- |
| Ordinary PR outside `behavioral` or push to `main` | Repository syntax/links, dependency identities, every Lean module, axiom audit, kernel replay, native source/IR CLI regressions and scope-policy tests |
| PR targeting `behavioral` | Compiler and behavioral source IntentBond jobs: every Lean module, axiom audit, kernel replay and all compiler regressions, including native and Haskell/Alloy comparisons |
| Behavioral PR changing reference dependencies or unclassified paths | Additional independent reference job with both complete historical and PR113 corpora |
| Final `behavioral` → `main` PR (including drafts), behavioral PR marked ready for review, push to `behavioral`, scheduled or manual run | All three IntentBond jobs are mandatory: compiler/proofs, behavioral source and complete reference qualification |

Scheduled qualification checks `main`. Final integration is identified by the
PR head and base branches, independently of the changed paths.
The full local IntentBond check remains mandatory before handoff. Routine CI is
build/proof/CLI evidence, not full qualification evidence. All paths check scope
identity against the original baseline and retain logs. The full-check command,
coverage policy, test cases and per-command time limits are unchanged.

These paths reuse the existing module inventory, Lake build targets, axiom audit,
LeanChecker and Python `unittest` tests; no separate test framework or compiler
runtime dependency is added. The default `scripts/check.sh` runs every gate.
GitHub's cache action reuses pinned
dependency packages, native Lake artifacts and external comparison tools.
Preparation and clean-pin/tool identity checks still run for the tools each path
uses. Kernel replay and axiom inspection run on the restored local artifacts;
successful proof/test results are never restored.

### CI profiles

The [profile selector](../scripts/ci_profile.py) uses Git's complete, untruncated
path diff with rename detection disabled. Compiler Lean files, Lean test files,
independent `tests/test_*.py` modules, and component documentation do not affect
standalone reference qualification. The two reference test modules, all fixtures,
scripts/shared helpers, manifests, toolchains, CI configuration, requirements,
scope and source/oracle/build/specification contracts require it. Unknown paths,
missing baselines and unsuccessful ancestry/diff checks also require it.
No accepted input hash or successful result is inferred from a missing comparison.
Acceptance, integration, scheduled and manual runs always select all three jobs, even
when the diff contains only compiler inputs. Unknown event/target classification
also requires all three. This reuses the existing profile selector, reusable
workflow, test-group registry and required aggregate. The behavioral source suite
uses two solver workers; sharing a four-CPU runner with the temporal target suite's
two solver workers and other regressions creates CPU contention. A separate
required source job preserves their query budgets and complete case inventories.
The reference corpus likewise runs separately from compiler validation.
No new dependency, license obligation or compiler runtime/proof boundary is added.

`--compiler-ci` delegates exactly `test_pr113_oracles` and `test_temporal_oracles`
to `--reference-ci`, and `test_behavioral_source_cli` and
`test_behavioral_source_comparison` to `--source-ci`. It retains every other
discovered case, including new test modules, plus the normal build, audit and
kernel gates. The source profile builds the native compiler and runs both complete
source modules. Every profile rejects missing, empty, skipped or failed suites.
The default local check runs all modules together. Hosted full qualification
requires all three profiles against the same immutable candidate.

The [reusable validation workflow](../.github/workflows/validate.yml) derives each
explicit profile from the baseline-checked full scope. Only its name and test
command differ; coverage, skip policy and deadline remain identical. Each job
retains its actual scope, profile receipt, source SHA and fresh IntentBond evidence.
Each profile identifies the suites it executes and does not claim full qualification.
The reference job validates the pinned reference implementation, not the developing
compiler. All jobs check the same immutable candidate. The required
`Lean proofs and native CLI` aggregate rejects any failed, cancelled or unexpectedly
skipped job. Behavioral validation always requires the source job; the reference
job may be absent only when the retained dependency selection allows it.

GitHub `workflow_call`, job dependencies and the existing actions provide execution
and aggregation. Whole-workflow path filters can leave required checks pending and
do not express the conservative unknown-input rule, so a small standard-library
selector supplies that rule. No new dependency or license is introduced. The
selector is tooling within the existing Python/Git/CI trust boundary, not a compiler
proof. [Regression tests](../tests/test_ci_profile.py) exercise actual Git changes,
missing baselines, scope preservation, complete test partitioning and gate failures.
The daily schedule checks `main`. Manual dispatch runs full qualification on the
selected candidate branch.

Public CI artifacts retain check logs, source identities, notices, generated text,
solver witnesses and replay inputs for 30 days. The pinned `upload-artifact`
action's path exclusions omit compiled test executables, Java classes and the
downloaded Haskell source archive; no separate packaging tool or dependency is
needed. Binary hashes and build commands remain in the evidence so reviewers can
rebuild with the pinned tools. Full qualification still builds and executes every
native probe.
When adding a probe, keep its compiled output out of the public artifact paths.

The [scope selector](../scripts/ci_scope.py) adapts the pinned Clafer Semantics
`scripts/ci_scope.py` (MIT, copyright 2026 Kacper Bak). IntentBond already accepts
external trusted policy; plain `cmp` cannot distinguish an approved amendment from
an arbitrary edit. The selector constructs the approved `120` → `600` or `600` → `1200` deadline
from the original baseline, pins both byte hashes and rejects every other change.
It never replaces the Git comparison baseline. CI retains the selected policy and
migration receipt. [Regression tests](../tests/test_ci_scope.py) check accepted
policy identities, weakened gates, altered coverage and unknown/reversed migrations.
This is unverified Python review tooling, with no added dependency or runtime code.

Dependency preparation reuses the module inventory and import parser to build all
upstream modules imported by project sources, including the telematics examples
outside the upstream root module. These are pinned dependency outputs; Lake also
checks every project build target in the fresh check snapshot. The regression runner reuses Python's
standard `ThreadPoolExecutor` (also used by the comparison harness) to bound
concurrent groups by CPU availability after the exclusive PR113 phase. CPU-count
caps alone do not reserve execution time for a solver while other groups compile
Lean probes; phase separation supplies that isolation without changing query
budgets. The default is two workers, with an
explicit `CLAFER_TEST_JOBS` limit from one to four. Every discovered
case and each group's exit status remain mandatory. CI uses the cache action's
separate restore/save steps to retain successfully prepared dependencies even if
later project verification fails. The full check retains every semantic assertion,
input case, per-command limit and trusted check deadline.

Source-pipeline comparisons reuse `PipelineNative.run` in a generated Lean
harness compiled once through Lake's native dependency facets. Its binary accepts
batches of independent calls, sharing startup without interpreted imports. Each call compiles its
source, evaluates its own candidate and writes fresh artifacts; all mutation,
replay and solver assertions remain mandatory. The existing subprocess deadline
applies to the entire batch. This reuses Lean list recursion and Python's recorded
subprocess wrapper, with Lake supplying the native dependency closure. No
persistent service, custom dependency resolver or result cache is added. These test executions remain outside the kernel proof boundary.

Live log forwarding reuses the pinned upstream workflow's `tail --pid` pattern;
the full retained log and check exit status remain authoritative.

CI sets `LEAN_NUM_THREADS=2` and `CLAFER_TEST_JOBS=3`; kernel replay also uses two
workers, after all regression groups finish.
The cache layout reuses the pinned semantics repository's native Lake cache,
verified-exporter receipt checks, independent download caches and timing wrapper.
Lake 4.35's `enableArtifactCache` and `restoreAllArtifacts` provide source/options/
import invalidation and local artifacts for the audit; a custom build-result cache
would duplicate that machinery. Package sources remain checked against the exact
manifest. Separate exporter keys hash their builder/adapter sources rather than
the semantics manifest, and existing receipt validators reject changed binaries.
Temporal reuse additionally checks every archived source file. Static and temporal
cold builds share one pinned Stack/GHC store while retaining separate compiler
source trees. Compact exporter caches exclude GHC and Stack build directories;
there is no new dependency or license obligation. These caches are trusted build
inputs, not proof evidence. The Lean kernel, native code generator and C toolchain
boundaries described above are unchanged.

Preparation caches are saved before validation, so a later failed regression does
not discard working tools. The previous combined cache can seed the new layout;
subsequent runs restore the independent entries. All timing output uses Bash's
`SECONDS` and Python's monotonic clock, following the existing semantics workflow.
The workflow retains the exact check scope and all command time limits.

Ubuntu's [AppArmor namespace policy](https://documentation.ubuntu.com/security/security-features/privilege-restriction/apparmor/)
requires explicit permission for the runtime-isolation test. The manually
dispatched full CI run installs a dedicated copy of the distribution's Bubblewrap executable and attaches the
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
