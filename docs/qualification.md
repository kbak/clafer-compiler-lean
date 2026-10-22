# Private compiler qualification

Qualification links supported features to evidence, measures reproducible build
and compilation costs, and prepares private candidate bundles. The tooling was
accepted through [PR #45](https://github.com/kbak/clafer-compiler-lean/pull/45).
Each candidate still requires independent semantic review and redistribution
clearance; publication remains a separate decision.

## Reuse assessment

The existing mandatory check already inventories every Lean module, builds the
native compiler and proofs, audits transitive axioms, replays the kernel, runs
the supported/rejection corpus and retains exact Analyzer comparisons. Reuse
these gates and their evidence rather than introduce a second correctness suite.
The accepted parser, resolution, constraint, expression and pipeline tests supply
the feature witnesses. The guarded M1 comparison remains guarded; source
comparisons use #20's independently justified observation bridge.

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
different defaulting; only identical explicit source/bounds in the common domain
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
clean/warm builds and compiler runtime, then prepare a source-bound private bundle.
Retain unresolved limits for independent review.

## Feature and evidence inventory

This inventory accounts for the unchanged [adopted matrix](architecture.md#feature-matrix).
“Proved” refers to in-memory Lean declarations at their documented hypotheses.
Native, parser, text and solver witnesses are tests. The mandatory command discovers
every Lean module and Python test; links below identify the assertions for review,
not an assertion that a file link proves coverage. All rows remain subject to
candidate-specific check results and independent qualification review.

Qualification profiling found that the existing main regression process serialized
the frontend and target suites after the full project build, exceeding the adopted
deadline on this host. The [existing runner](../scripts/run_tests.py) now assigns
those independent suites to two additional bounded worker processes. Each worker
still fails on an empty, skipped, unimportable or failing suite; the parent waits
for every worker. [Runner regressions](../tests/test_check_script.py) inject these
outcomes into every newly scheduled module and test a missing module. No assertion,
case, kernel module, scope coverage rule or deadline was removed. There is no
compiler/runtime optimization in this scheduling change.

A further full run passed all 100 Python regressions but reached the deadline
during kernel replay (97 modules reported). The existing LeanChecker scheduler
now uses four workers, with the same complete module roots, instead of two.
This bounds concurrent import environments while completing replay alongside the
mandatory suites. The runner test checks this explicit worker count and still
requires replay/axiom failures to propagate. Build experiments retain a separately
recorded two-worker replay configuration so their timings are not conflated with
the parallel full gate.

| Adopted capability | Implementation / promised proof boundary | Positive and negative evidence |
| --- | --- | --- |
| Resolved identities, ranks, containment, effective local/group intervals | [IR admission equivalence](ir.md), [structural preservation](structural-correctness.md) | [IR](../tests/test_structural_ir.py), [structural](../tests/Structural.lean), [global/local mutations](../tests/StructuralCorrectness.lean) |
| Root, abstract cover, declaration disjointness, ownership, set/bag occurrences, cyclic references | [M1 concrete representation, soundness/completeness](structural-correctness.md) | [Exact three-way comparison and mutations](../tests/test_comparison.py), [native reference-head checks](../tests/test_cli_external.py) |
| Ordinary inherited fields, explicit abstract families, group overrides and contextual views | [Selected realization and preservation](inherited-realization.md) | [Inherited fixtures](../tests/Inherited.lean), [native owner/group mutations](../tests/InheritedNative.lean), [full-source mutations](../tests/test_source_pipeline.py) |
| Authored names/IDs/spans, layout/braces, comments, Unicode, defaults, forward/lexical/global lookup | [Parser boundary](parser.md), [checked resolution and upstream-default agreement](resolution.md) | [Parser grammar/precedence and rejection corpus](../tests/test_parser.py), [defaults/ambiguity/cycles/identity](../tests/test_resolution.py) |
| Integer references and finite observations of mathematical integers | [Observation/range proofs](expressions.md), [full-model completion](pipeline.md) | [Distinct integers, zero observed carrier and primitive parent](../tests/test_source_cli.py), [carrier counterexample](../tests/PipelineLimits.lean) |
| Every typed static constructor, finite quantifiers and attachment occurrence | [Independent denotation](expressions.md), [constructor and attachment preservation](expression-encoding.md), [source elaboration rules](constraints.md) | [Constructor/undefinedness/role fixtures](../tests/ExpressionEncodingNative.lean), [actual Analyzer mutations](../tests/test_expression_encoding.py), [source shapes/owners/coercions](../tests/test_constraints.py) |
| Native IR/source commands, bounds, atomic output and diagnostics | [CLI](cli.md), [composed source soundness and bounded completeness](pipeline.md) | [IR protocol](../tests/test_cli.py), [source protocol](../tests/test_source_cli.py), [runtime isolation and actual Analyzer](../tests/test_cli_external.py) |
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
UNSAT. Known Haskell default differences and width-16 Analyzer capacity failures
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
  --haskell-work /tmp/qualification-haskell/15adb2216909421bcb5022174d2d84ef2b42307c \
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
all original UID scopes and Int width; it is not timed through the receipt audit.
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
  --oracles /tmp/oracle-evidence --review /tmp/review.json --out /tmp/private-candidate
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
research tag creation is not a compiler gate. Each private candidate requires
independent acceptance; publication remains a separate decision in #3.

## Retaining and retrieving evidence

The accepted M0–M3 candidate has a
[private draft archive](https://github.com/kbak/clafer-compiler-lean/releases)
identified by `qualification-m0-m3-e816480`. It retains the original
`candidate-e816480.tar.gz`, the later `acceptance-2026-10-21.json`, and
`SHA256SUMS`. The candidate is `e8164804d1917d7b01f8111e1f269bd6c7ffdb4b`;
the archive's SHA-256 is
`42880b55068fd3cabdac775c7d532240d578ab11340ea8024dd2c9913e9821a0`.
Its original pending-review record is historical; the separate acceptance record
does not rewrite it. Neither record attests to later source revisions.
The additional `validation-history-20261022.tar.gz` asset retains earlier failed
qualification runs and the cleanup checks, including the standalone success and
snapshot timeouts. Its separate `.sha256` file verifies that archive.

Authenticated maintainers with access to drafts can retrieve and verify it:

```sh
gh release download qualification-m0-m3-e816480 --repo kbak/clafer-compiler-lean \
  --dir /tmp/qualification-retrieval
cd /tmp/qualification-retrieval
sha256sum --check SHA256SUMS
```

Draft assets avoid Actions artifact expiration. They can still be deleted, so
retain a second private backup. The uploaded archive was downloaded and its hashes
checked against the original; a second copy is retained outside temporary storage.
GitHub release assets and ordinary SHA-256 tools provide this storage without a
new service, package dependency or repository binary. The archive includes source,
notices, raw measurements, exact comparison replays, source-bound check evidence
and runtime smoke results.

Keep evidence drafts private and review their contents before any future visibility
change: logs can contain machine paths and internal context. A draft archive is
not binary redistribution clearance. CI's 30-day artifacts support current review;
accepted candidates need a separately retained archive. Preserve failed checks and
their source identities alongside successful evidence rather than replacing them.

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
