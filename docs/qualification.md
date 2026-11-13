# Compiler qualification

<a id="private-compiler-qualification"></a>

Qualification links supported features to evidence, measures reproducible build
and compilation costs, and prepares candidate bundles for independent semantic
review. Bundles record their exact source revision, toolchain and review status.

The [static inventory](#feature-and-evidence-inventory) and complete
[behavioral source inventory](behavioral-source.md#feature-and-evidence-inventory)
link delivered profiles to implementations, proofs and runtime witnesses.
The [behavioral matrix](behavioral.md#complete-feature-and-evidence-matrix) retains
all B01–B32 obligations. Component inventories distinguish first-slice evidence
from the full frontend/encoder and source workflow. Every candidate still needs
source-matched full checks and independent review. The current
[0.5.8 profile](sources.md#clafer-058-source-and-replay) preserves the separate
historical corpora and temporal `let` exclusions. The shared
[initializer/absence qualification matrix](behavioral-source.md#initializer-and-absence-qualification)
retains exact source/compiler/reference outcomes, hidden-reference probes,
static Choco controls and explicit reference discrepancies. Its disposition
requires independent review; current tool and frontend checks do not imply acceptance.
The [instance-check walkthrough](instance-checks.md) runs small positive/negative
structural candidates and the complete static source model while retaining these
qualification and proof/execution boundaries.
The [Choco exercise](choco.md) checks actual generated structural instances,
supplied semantic violations, strict declaration/identity decoding and exact
candidate replay. Its Java/Haskell extraction boundary is tested, not proved;
bounded exhaustion is not a checker verdict or a completeness result.
The [temporal oracle corpus](oracles.md#temporal-fixture-and-witness-inventory)
provides separate bounded tool evidence for the 0.5.7 candidate. It executes fresh
Haskell/Alloy queries and retains complete traces; it does not qualify downstream
behavioral compilation, exact source-candidate replay or any new Lean theorem.

The [PR113 delta candidate](oracles.md#pr113-delta-qualification-candidate) adds
same-generation UID/Alloy correspondence, modifier-array validation, historical
pattern/reference discrepancies and fresh explicit-model bounded comparisons.
Its [tests](../tests/test_pr113_oracles.py) retain independent distinguishing
witnesses and replay evidence. It establishes no exact-lasso equivalence or new
Lean theorem; its historical receipts do not qualify a different producer pin.

The [behavioral IR inventory](behavioral-ir.md#proof-handoff) separately records
the delivered `behavioral-core/1` API, exact interpretation theorems and
[fixtures](behavioral-ir.md#fixtures-and-validation). It supplies no behavioral
source command, target encoding or full-profile qualification claim.

The [behavioral frontend inventory](behavioral-frontend.md) separately records
authored parsing, declaration/modifier/header binding, resolved reductions, partial
normalization, grouped binder plans/counting and source model/check/run requests.
The accepted expression surface has native integration tests, independent source
derivations, upstream interpretation/normalization proofs and complete range-check
obligations under explicit structural budgets. Grammar recognition and native
execution remain tested boundaries; scope-budget validity belongs to encoding.
The [hard initializer contract](behavioral-frontend.md#hard-declaration-initializers)
adds production classification, original-context RHS transport and structural
equation agreement. Its source cases distinguish empty-head inactivity, clocks,
rebirth, inheritance and temporal cancellation; finality retains explicit RHS
stability assumptions. Candidate changes require independent semantic review and
source-matched qualification.

The [temporal target](alloy-temporal.md) has separate admission, natural-time
meaning and checked serialization. Its kernel laws and
[Analyzer regressions](../tests/test_alloy_temporal.py) cover target constructs;
the first-slice source-to-target proofs are recorded separately below, and full
behavioral qualification retains its completion gate. This does not change the
static feature inventory below.

The [first-slice encoding](behavioral-encoding.md#kernel-boundaries) adds concrete
trace representation, signed formula transport and actual structural snapshot
correspondence. Its [35 Analyzer cases](behavioral-encoding.md#fixtures-and-validation)
exercise compiler-generated modules, counterexamples and native witness replay.
These are separate from the full-profile qualification gate and the static
inventory below.

The [full encoding](behavioral-encoding.md#full-profile-proof-components) adds
`Full.compile`, complete partial-expression lowering, disjoint direct-type
inventories, inherited structural facts and finite integer observations.
`Expressions.lowerAt_preserves` and `lower_preserves` follow the actual executable
pass. The [absence corollaries](behavioral-encoding.md#absent-reference-observations)
make the empty-reference boundary explicit while retaining total scalar decoder
data and the same representation and finite-integer assumptions.
`Full.compiled_sound` derives actual decoding and the existing upstream
model/query satisfaction from target satisfaction; `Full.compiled_complete`
proves the reverse for the concrete encoder under data-only source fitting
conditions. `compiled_complete_observed` includes arbitrary source carriers under
the concrete observation map. `frontend_sound` and `frontend_complete_observed` compose successful in-memory
source elaboration, while `SourceElaborated` records every authored/header
derivation. The full fixtures exercise scoped patterns, transition chains,
lifetime anchors, inherited groups/references and property commands. These
in-memory kernel results and bounded Analyzer witnesses retain the parser,
text/native and solver boundaries; they do not establish final behavioral
qualification or unrestricted infinite-trace representability.

The [resolved temporal runtime](temporal-runtime.md) supplies actual-output
decoding, verified finite source evaluation and exact three-way trace fixing.
Its corpus distinguishes cancellation and source negation, replacement under a
surviving parent, reappearance, frozen captures and loop edges. Decoder mutations,
injected discrepancies, replay tampering and runtime isolation test the external
boundaries. This is first-slice evidence with manually paired source/IR formulas;
it does not qualify the full source frontend or later Haskell profiles.

The [full source workflow](behavioral-source.md) records native commands, strict
scalar decoding, exact source/IR observations and per-case measurements. The
[suite](../tests/test_behavioral_source_comparison.py) retains complete lasso
queries and replay identities, while the static and reference-tool suites remain
mandatory. Its Python finite observer is tested, not kernel certified.

## Main integration

`impl~compiler-behavioral-main-integration~1`

The [Lake configuration](../lakefile.toml), [manifest](../lake-manifest.json),
[dependency checks](../scripts/project_modules.py), native version and oracle
profiles identify the [accepted semantics-main source](sources.md#accepted-semantics-main-dependency).
The [CI selector](../scripts/ci_profile.py) requires compiler/proof, behavioral
source and reference qualification for the final `behavioral` → `main` PR,
including drafts and synchronized updates. Routine main checks remain unchanged.
Scheduled full qualification uses `main`; solver suites keep separate jobs and
their existing concurrency and query deadlines.

The [final gate](https://github.com/kbak/clafer-compiler-lean/issues/80) retains
the frozen compiler baseline, source/API delta, full IntentBond evidence,
required hosted checks, review disposition and actual merged commit identities.
The [compiler](https://github.com/kbak/clafer-compiler-lean/issues/69) and
[semantics](https://github.com/kbak/clafer-semantics/issues/122) roadmap matrices
must account for every required feature and accepted dependency. Open work outside
the selected profile does not silently expand or narrow it. Publication of a PR,
passing automation and IntentBond exit 4 do not constitute merge acceptance.

Reuse the existing check, three CI jobs, profile selector and source/tool receipt
validation. No new runner, framework or dependency is needed. The full source
comparison reuses its validated target observation after checking original bounds,
avoiding a repeated table construction. Independent source observation and target
truth remain separate; this cleanup changes no proof premise or comparison rule.

Covers: `req~compiler-behavioral-main-integration~1`

## Reuse assessment

The existing mandatory check already inventories every Lean module, builds the
native compiler and proofs, audits transitive axioms, replays the kernel, runs
the supported/rejection corpus and retains exact Analyzer comparisons. Reuse
these gates and their evidence rather than introduce a second correctness suite.
The accepted parser, resolution, constraint, expression and pipeline tests supply
the feature witnesses. The guarded M1 comparison remains guarded; source
comparisons use the [pipeline's observation bridge](pipeline.md#composed-assurance).

Lean 4.35.0 supplies `IO.monoNanosNow`; its existing driver APIs and Lake linker
response file suffice for an external native stage probe. The probe is test code,
does not enter the production executable, and must emit the same bytes as the
ordinary source command. Python's `subprocess`, `statistics`, `hashlib`, `tarfile`
and `platform`, plus GNU time's per-process elapsed/CPU/maximum-RSS observations,
supply process measurement and packaging. Hyperfine would supply repeated
whole-process timing, but not the dependent in-process compiler stages, candidate
evidence binding or feature inventory; pyperf would add a Python dependency for
primarily non-Python measurements. Neither is needed for this descriptive harness.
No benchmark result is a semantic proof or a speedup requirement.

The pinned Haskell public `runClaferT`/`parse`/`desugar`/`compile`/`generate`
interface and existing hash-checked external build recipe supply the comparison
compiler. Its AST/IR have no `NFData` instances; forcing `show` would add unrelated
formatting to stage measurements. Instead measure its entire native compilation,
forcing the generated UTF-8 bytes through file IO before process exit. Use the
public static `Generator.Alloy.genModule` to supply explicit original-UID scopes;
`generate` with `scope_strategy = None` would otherwise supply no scopes.
Reuse the original compiler library without changing its semantics or source.
Haskell has a virtual root and
remaining abstractness/defaulting distinctions despite the adopted numeric policy; only identical explicit source/bounds in the common domain
support direct performance comparison. Complete telematics remains a separate
Lean qualification input where compatibility differs.

Candidate packaging reuses Git's immutable source export, IntentBond's source
verification, the existing isolated native smoke test and dependency manifest.
It must preserve failed measurements, external replay evidence, and pending
independent review; a generated manifest cannot grant acceptance. The package
contains the native compiler, source, documentation and applicable licenses, not
Haskell/Java/Alloy development tools. Lean's Apache-2.0 license and bundled
third-party notices accompany its linked runtime. The inspected Linux response
file links GMP and C++ runtime components statically; glibc is a shared runtime
requirement. Retain the response file and notice inventory. This is a local review
artifact, not redistribution clearance; the source/relink obligations for bundled
LGPL components must be addressed before distributing a binary. Keep all
measurements, binaries, machine details and receipts outside
source. No dependency pin, language scope or trusted coverage policy changes.

For each candidate, run the full check, commit and verify the source, measure
clean/warm builds and compiler runtime, then prepare a source-bound candidate bundle.
Retain unresolved limits for independent review.

## Feature and evidence inventory

This inventory accounts for the unchanged [adopted matrix](architecture.md#feature-matrix).
“Proved” refers to in-memory Lean declarations at their documented hypotheses.
Native, parser, text and solver witnesses are tests. The mandatory command discovers
every Lean module and Python test; links below identify the assertions for review,
not an assertion that a file link proves coverage. All rows remain subject to
candidate-specific check results and independent qualification review.

The [full validation command](build.md) runs every regression group, declaration
audit and kernel replay. Scheduling and resource limits are part of that build
contract; benchmark measurements retain their own configuration and source identity.

| Adopted capability | Implementation / promised proof boundary | Positive and negative evidence |
| --- | --- | --- |
| Resolved identities, ranks, containment, effective local/group intervals | [IR admission equivalence](ir.md), [structural preservation](structural-correctness.md) | [IR](../tests/test_structural_ir.py), [structural](../tests/Structural.lean), [global/local mutations](../tests/StructuralCorrectness.lean) |
| Parentless abstract local-bound normalization | [Resolved normal form, fixed points and structural satisfaction equivalence](ir.md#resolved-structural-normalization) | [Kernel witnesses](../tests/StructuralNormalization.lean), [native preservation and rejection](../tests/StructuralNormalizationNative.lean) |
| Root, abstract cover, declaration disjointness, ownership, set/bag occurrences, cyclic references | [M1 concrete representation, soundness/completeness](structural-correctness.md) | [Exact three-way comparison and mutations](../tests/test_comparison.py), [native reference-head checks](../tests/test_cli_external.py) |
| Actual Choco structural instances, source/explicit metadata and reference-head identity | [External adapter boundary](choco-adapter.md); existing guarded checker, no new proof | [Generated bag/set controls, semantic negatives, malformed exports and replay](../tests/test_choco_instances.py) |
| Ordinary inherited fields, explicit abstract families, group overrides and contextual views | [Selected realization and preservation](inherited-realization.md) | [Inherited fixtures](../tests/Inherited.lean), [native owner/group mutations](../tests/InheritedNative.lean), [full-source mutations](../tests/test_source_pipeline.py) |
| Authored names/IDs/spans, layout/braces, comments, Unicode, defaults, forward/lexical/global lookup | [Parser boundary](parser.md), [checked resolution and upstream-default agreement](resolution.md) | [Parser grammar/precedence and rejection corpus](../tests/test_parser.py), [defaults/ambiguity/cycles/identity](../tests/test_resolution.py) |
| Integer references and finite observations of mathematical integers | [Observation/range proofs](expressions.md), [full-model completion](pipeline.md) | [Distinct integers, zero observed carrier and primitive parent](../tests/test_source_cli.py), [carrier counterexample](../tests/PipelineLimits.lean) |
| Every typed static constructor, finite quantifiers and attachment occurrence | [Independent denotation](expressions.md), [constructor and attachment preservation](expression-encoding.md), [source elaboration rules](constraints.md) | [Constructor/undefinedness/role fixtures](../tests/ExpressionEncodingNative.lean), [actual Analyzer mutations](../tests/test_expression_encoding.py), [source shapes/owners/coercions](../tests/test_constraints.py) |
| Native IR/source commands, bounds, atomic output and diagnostics | [CLI](cli.md), [composed source soundness and bounded completeness](pipeline.md) | [IR protocol](../tests/test_cli.py), [source protocol](../tests/test_source_cli.py), [runtime isolation and actual Analyzer](../tests/test_cli_external.py) |
| Behavioral literal empty navigation and nonfatal self-expression warnings | [Independent source rules and reporting boundary](behavioral-frontend.md#literal-empty-navigation-and-successful-warnings), [CLI protocol](behavioral-source.md#successful-warning-protocol) | [Native term/partial-cursor assertions](../tests/BehavioralElaborationNative.lean), [kernel rule examples](../tests/BehavioralExpression.lean), [located warnings and zero-divisor rejection](../tests/test_behavioral_source_cli.py), [exact Haskell/Alloy outcomes](../tests/test_behavioral_source_comparison.py); static rejection tests retained |
| Complete Appendix 6, all twelve bodies and final selections | `Pipeline.source_sound`, `all_source_sound`, `source_complete`; [explicit carrier/Fits limits](pipeline.md#composed-assurance) | [Inventory equality](../tests/ConstraintsInventory.lean), [version/display/parent/omission/group replays](../tests/test_source_pipeline.py) |
| Static Alloy AST, finite scope and no-overflow target | [Independent target](alloy-core.md), [integer semantics](expression-encoding.md) | [Independent AST fixtures](../tests/AlloyCore.lean), [integer fixtures](../tests/IntegerArithmeticNative.lean), [external arithmetic](../tests/test_integer_arithmetic.py) |
| Deterministic hygienic text and metadata | [Successful-render reconstruction, not total renderability](alloy-text.md) | [Round trips and mutated names/grouping](../tests/AlloyText.lean), [real Alloy parsing](../tests/test_alloy_text.py), [CLI maps](../tests/Driver.lean) |

The constructor inventory is exhausted as follows; the source and target proofs
are structural over the admitted syntax, with explicit finite observation and
representation conditions discharged by the composed pipeline where applicable.

| Typed constructor(s) | Concrete witness family in `ExpressionEncodingNative` / source tests |
| --- | --- |
| `boolean`, `integer`, `and`, `not` | true/false, strict conjunction, negation and undefined implication |
| `this`, `extent`, `var` | owner under binder, global extent, lexical binding and shadowing |
| `map`, `image`, `join` | original head/dereference/parent roles, binary composition and identity relation |
| `equal`, `less` | object/relation/integer equality, operand-order Analyzer mutation |
| `arithmetic` add/subtract | positive/negative intermediates, rejected hidden overflow |
| `integerOf` | singleton, empty/multiple/off-domain values, zero primitive observation |
| `cardinality` | head versus target counts and distinct binary tuples |
| `setOp` union/difference/intersection | unary and binary forms, ordinary intersection |
| `subset` | inclusion and violating candidates |
| `widenObjects`, `widenRelation` | identity widening and source common-super coercion |
| `all` | nested lexical binding, empty domain, undefined nonempty body, primitive-value binder |

The [parser tests](../tests/test_parser.py) cover each retained precedence pair,
declaration/use/cardinality/group form and parentheses. The
[constraint tests](../tests/test_constraints.py) cover derived Boolean connectives,
comparisons, `in`/`not in`, arithmetic, unary minus, `#`, `some`/`no`/`not`/`one`/`lone`
collection tests, bare collections, single `all`/`some`/`no`/`not` binders and nested
paths. Original multiple bodies and inherited owner restrictions are retained.

| Explicit exclusion in the contract | Rejection evidence |
| --- | --- |
| Enums; runtime string/real/double/bool/boolean; noninteger literals | `ParserTests.test_rejections_do_not_erase_constructs` |
| Multiplication/division/remainder, sum/product/min/max | Same parser rejection corpus; source CLI rejects numeric multiplication |
| Conditional/let, domain/range restriction, deprecated intersection/comma, disjoint/multiple/one/lone binders | Same parser rejection corpus |
| Assertions, goals, initializers, behavior/temporal modifiers and transitions | Same parser rejection corpus; no erased unsupported source |
| Backend escapes, option directives, qualified names and non-direct target expressions | Same parser rejection corpus |
| Nested explicit abstracts, abstract references, reference inheritance, cycles, reserved names | `ResolutionTests.test_diagnostics_and_mutations`; [selected-domain rejection](../tests/Inherited.lean) |
| Ambiguity, invalid endpoints, type/coercion failures | `ConstraintTests` assertions in [source elaboration tests](../tests/test_constraints.py); malformed diagnostics are separate from unsupported |
| Whole primitive-extent observation, unsafe arithmetic/count budgets, unknown profiles/bounds fields | [Expression range tests](../tests/ExprRanges.lean), [source/IR CLI rejection suites](../tests/test_source_cli.py) |

No new proof of parser grammar recognition, arbitrary-carrier normalization,
total successful rendering, JSON/native correctness, Analyzer translation or SAT
solving is claimed. Completeness requires the concrete finite observation witness
and `Fits`; mathematical `Int` remains infinite. Bounded UNSAT is not unbounded
UNSAT. Remaining Haskell abstractness/group differences and width-16 Analyzer capacity failures
remain recorded in [sources](sources.md) and [expression encoding](expression-encoding.md).
Neither is silently reclassified as agreement. A newly discovered material defect
must block acceptance and receive an issue before any semantic correction.

## Measurements and replay

[The harness](../scripts/qualification.py) uses GNU time and monotonic nanoseconds.
Install the normal [build prerequisites](../CONTRIBUTING.md#setup-and-validation)
plus GNU time. Build the pinned Haskell library once outside the repository using
the existing upstream recipe (network access and GMP headers are required):

```sh
CLAFER_CAPTURE_CACHE=/tmp/qualification-haskell \
  python3 .lake/packages/clafer/scripts/verification/runtime.py true
```

Finish and commit the candidate before final measurements. Use new external
directories; measurement output is never checked into Git:

```sh
python3 scripts/qualification.py runtime --out /tmp/qualification-runtime \
  --haskell-work /tmp/qualification-haskell/f6ca5b887d7bacc09915c6fc0278064c8371beac \
  --warmup 1 --samples 5
python3 scripts/qualification.py builds --candidate HEAD --out /tmp/qualification-builds
```

`runtime` also requires the provisioned `CLAFER_ORACLE_TOOLS` manifest (or `--tools`).
After timing, the pinned Analyzer parses both common-domain outputs and checks
every actual signature scope and the Int width against the original bounds and
declaration maps, without solving. Audit startup time is kept outside compiler
samples. Tool/option identities and parsed command receipts are retained.

The common-domain generator creates 1, 8 and 48 owners, each with an optional
field and a set reference to that field. All cards are explicit `0..1`, all names
are unique, each user extent has upper scope 1, and width is 16. The Lean root
has exact scope 1; Haskell's root is virtual. The nonprimitive budget is one plus
the sum of all user upper scopes, so it adds no hidden restriction. Every source
byte and bound is retained. Haskell uses static generation with `keep_unused`,
no scope inference, no statistics and no solver. Its public generator receives
the original UID scopes after `withEmptyAbstracts` and the pinned Alloy-name
mapping, plus Int width. The receipt preserves source UIDs and backend symbols
separately; generation is not timed through the capture receipt audit.
The integer fixture and complete telematics model additionally exercise the Lean
stages; they are not mislabeled as common-domain Haskell comparisons.

Raw processes are interleaved with alternating tool order, one discarded warmup
and five retained samples by default. Whole-process wall/CPU time, peak RSS and
output bytes are distinct from the native probe's parsing, resolution/defaults,
constraint elaboration, bounds decoding, backend checking and checked-rendering
times. Stage time excludes file IO/startup; memory is the whole process high-water
mark, not per-stage allocation. All results depend on the recorded machine/load
and warm filesystem caches. No statistical significance or speedup claim follows
from these descriptive samples.

The build experiment exports the exact clean commit into fresh scratch storage,
copies only clean pinned dependency packages, measures a cold project build and
an incremental warm build, then separately measures first/repeated kernel replay
and the axiom audit. “Cold” excludes project outputs, not dependency artifacts or
OS caches. `lake build` includes proof elaboration; replay is not a second compiler
runtime measurement. Full correctness/solver evidence still comes from the
unchanged mandatory IntentBond command.

## Local candidate bundle

Run `ib check` and committed-source `ib verify` with the original baseline as in
[CONTRIBUTING](../CONTRIBUTING.md#setup-and-validation). Retain its full directory
and `CLAFER_ORACLE_EVIDENCE`. Prepare an external `review.json` with the exact
candidate and independent disposition, for example `status: pending`; never
substitute self-review or exit 4 for acceptance. Then:

```sh
python3 scripts/qualification.py package --candidate CANDIDATE --base BASE_COMMIT \
  --ib /path/to/pinned/bin/ib --evidence /tmp/check/evidence.json \
  --runtime /tmp/qualification-runtime --builds /tmp/qualification-builds \
  --oracles /tmp/oracle-evidence --review /tmp/review.json --out /tmp/compiler-candidate
```

The bundle binds the clean source, checked evidence, measurements and clean-built
native binary; it includes complete logs, fixture/output receipts, replay files,
tool pins, notices and explicit review status. Packaging rejects modified check
artifacts or measurements from a different source and invokes `ib verify` itself.
It tests the packaged executable in an empty Bubblewrap root with only its shared
libraries and inputs, and compares bytes with a host invocation. The tarball is
created locally; no release, tag, upload or visibility change occurs.

Use `bin/clafer-compiler --help` and the [source command examples](cli.md).
The current artifact targets Linux x86-64/glibc; it needs the recorded system shared
libraries, not Lean tooling, Haskell, Java or an Alloy installation. The package
contains original compiler source under MIT and Lean/third-party notices. It
excludes comparison-tool binaries and caches. Static runtime dependencies retain
their own licenses; the local bundle is not a general distribution clearance.

The [dependency upgrade policy](sources.md#discrepancies-and-reviewed-upgrades)
continues to require immutable pins, assumption/meaning/license review and all
applicable proofs/tests/comparisons. Preserve the independent SoSyM snapshot;
research tag creation is not a compiler gate. Each candidate requires independent
acceptance.

## Retaining and retrieving evidence

The [CI workflow](https://github.com/kbak/clafer-compiler-lean/actions/workflows/ci.yml)
retains check logs and comparison evidence for 30 days. Use the run associated
with the exact commit under review; a passing run for an earlier revision does
not qualify later changes. Public artifacts omit compiled probes and preserve
their build commands and hashes; see the [build contract](build.md#build-implementation).

For accepted candidates, retain the full evidence bundle beyond CI expiration,
including source identity, notices, raw measurements, comparison replays, runtime
smoke results and independent review disposition. Store a SHA-256 checksum with
each archive and keep a second backup. Verify the checksum when retrieving it.
Keep failed checks and their source identities alongside successful evidence.
Acceptance records belong in the linked issue or pull request and must identify
the candidate they accept.

Review evidence for credentials and private machine information before sharing it.
Binary distribution must also satisfy the linked runtime's license obligations
described above.

## Traceability

`impl~compiler-private-qualification~1`

The inventory above, [candidate adapter](../scripts/qualification.py),
[native probe](../tests/QualificationNative.lean) and
[pinned Haskell adapter](../scripts/qualification/HaskellBenchmark.hs) implement
the qualification and measurement contracts without changing production semantics.

Covers:
- `req~compiler-qualification~1`
- `req~compiler-performance~1`

`utest~compiler-private-qualification~1`

[Qualification regressions](../tests/test_qualification.py) exercise actual native
stage/production byte equality, corpus bounds, per-process measurements, retained
failure/timeout outcomes and rejection of modified or nonmatching check evidence.
Existing linked feature suites remain mandatory; the runtime/build experiments
are external candidate-specific evidence, not a substitute for those tests.

Covers:
- `req~compiler-qualification~1`
- `req~compiler-performance~1`
