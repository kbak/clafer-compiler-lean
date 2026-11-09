# Compiler and repository requirements

These requirements cover the compiler, its assurance boundaries and the repository
workflow. The [architecture](architecture.md) defines the selected structural
fragment. Component contracts in the [documentation map](intent.md#documentation-map)
record exact delivered APIs, proof assumptions and testing limits; the
[roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) retains task dependencies
and acceptance history. The [behavioral contract](behavioral.md) specifies the
implemented temporal profile separately from the static contracts.

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent explain the selected static and behavioral Clafer-to-Alloy
profiles, their relationship to Clafer Semantics and the Haskell comparison compiler, and
their supported interfaces. Describe the implemented frontend, structural and
expression encodings, checked serialization and preservation proofs with their
explicit scope, numeric-range and representation assumptions. The
[constraint-preservation review](https://github.com/kbak/clafer-compiler-lean/pull/41)
records the finite-observation conditions; the
[source-pipeline review](https://github.com/kbak/clafer-compiler-lean/pull/44)
records their composition into full source-model assurance. The current theorem
contracts are in [constraint encoding](expression-encoding.md) and
[source pipeline assurance](pipeline.md#composed-assurance).
Grammar-to-parser correspondence and native/serialized execution remain tested,
unproved boundaries. Maintain a [readable list of key proved properties](lessons.md#key-proved-properties)
with each claim's significance, supported domain, essential assumptions, exact
declaration/source link and authoritative component contract. Distinguish upstream
semantic results, compiler proofs and execution/comparison evidence; link the
companion semantics list or its pending task. Distinguish delivered guarantees from future work. Contract
adoption precedes dependent manual intake; planning tickets do not start
implementation. Publish the compiler source under MIT and provide public issue
and pull-request workflows that do not require access to the maintainer Project.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Contribution and validation workflow

`req~intentbond-workflow~1`

Pin IntentBond to an immutable source revision. Keep intent, requirements and
artifact links together, including imported Lean comment tags with original
source paths and lines. Keep the source-import regression to detect a checker
that silently drops those tags. Run the repository check through IntentBond before
handoff. Retain evidence outside source. Exit 4 means automation passed with
semantic review pending, never approval. The full local check remains mandatory.
On PRs outside `behavioral` and pushes to `main`, hosted CI builds every Lean module, audits
axioms, replays the kernel, checks scope identity and tests the native source/IR
CLI. Every PR targeting `behavioral` additionally checks traceability and runs all compiler
regressions, including native execution and external source/target comparisons.
Only the standalone historical and PR113 reference qualification suites may run
conditionally: their complete corpora are mandatory when a reference pin,
adapter, fixture, test, shared helper, provisioning recipe, or execution policy
changes. Missing or ambiguous dependency information requires the full suites.
Run both complete reference suites on scheduled verification, manual dispatch,
behavioral integration pushes, ready-for-review behavioral PRs and the final
`behavioral` → `main` PR on every update, including drafts. Scheduled checks use
`main`; ordinary main PRs retain the routine profile. These hosted
runs require independent compiler/proof, source and reference jobs against the same
immutable candidate. Retain a full source-matched IntentBond check before
acceptance. The full local check before handoff remains mandatory. A deferred
reference suite must be reported as not run on this candidate; previously accepted reference evidence is
bound to its exact inputs and is never described as fresh compiler validation.
Keep compiler and reference jobs independent, with a required aggregate result
that fails on every failed or missing mandatory job. Retain evidence; routine CI
does not establish full qualification or semantic acceptance. Public CI artifacts
retain logs, notices, source identities and replay inputs without compiled test binaries.
Scope changes require explicit review.
CI checks scope identity against the baseline, permitting only exact reviewed
migrations without replacing the Git comparison baseline.

Before implementation, check repository code, pinned upstream sources, standard
libraries and relevant maintained libraries/tools for reusable solutions. Prefer
reuse when it meets the contract. Record candidates and concrete gaps or tradeoffs
before writing custom infrastructure, including proof/runtime boundaries and
dependency/license costs. Independence alone is not a reason to rebuild machinery.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Issue tracking and manual intake

`req~github-tracking~1`

Use public repository issues for contribution and acceptance records. Maintainers
track Todo, Ready, In Progress and Done in the Project; contributors do not need Project
access. Tasks describe scope, acceptance criteria, sources/requirements and dependencies.
Planning tickets do not trigger implementation. IntentMade registration uses manual
intake and draft PR publication; deployment configuration and credentials stay
outside this repository.
Ready is limited to actionable work with accepted hard dependencies across both
repositories and does not start implementation. Reconcile affected unstarted
statuses manually after accepted closure, reopening, dependency or scope changes;
not-planned closure is not acceptance. Parent/sub-issue membership groups scope,
not readiness. The helper accepts `track --status ready` and uses live Project
field/option IDs without claiming dependency automation. Behavioral feature PRs
target `main`; close their issues only after accepted integration
and refresh affected statuses. Preserve the main controls and report behavioral
protection gaps separately from CI results.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Feature and interface planning contract

`req~compiler-scope~1`

Maintain a reviewable three-column M1/M2/deferred feature matrix grounded in the
pinned upstream admission declarations and Haskell grammar. M1 is the exact
guarded effective core. M2 selects the upstream typed static core and inherited
realization, with every accepted constructor/surface form enumerated and owned by
an implementation/proof/test task. Explicitly classify primitives, arithmetic,
defaults, behavior and erased syntax. Specify resolved-IR before text input,
malformed/unsupported/semantic outcomes, spans, deterministic output, scopes,
bitwidth, definedness and finite quantifier domains. Retain narrow review decisions;
do not imply compatibility or implementation beyond the selected contract.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Architecture, assurance and source planning contract

`req~compiler-boundaries~1`

Document one-way compiler-to-semantics ownership and module handoffs.
Keep independently defined source/target satisfaction, concrete encode/decode
relations, soundness, bounded completeness, frontend elaboration and serialized
text/runtime trust boundaries explicit. Bounds/representation assumptions must
not assume the preservation conclusion. Pin semantic and Haskell
baselines, retain source locators/licenses and define reviewed upgrades. No
research tag is required. Adopt behavioral planning requirements with real contract
artifacts without inventing implementation/proof coverage; acceptance review precedes dependent
manual intake. The build enforces module ownership/import boundaries and exercises
independent upstream imports. Keep required theorem shapes distinct from actual
proved declarations and their explicit assumptions.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Behavioral profile planning contract

`req~compiler-behavioral-profile~1`

Maintain the complete versioned behavioral feature matrix against accepted upstream
source commits, paper §§5–6 and errata T1–T13. Map every feature and required
structural prerequisite to frontend, IR, encoding, proof, runtime and qualification
owners, with positive/negative fixtures and known compiler discrepancies. Distinguish
the first smaller slice from completion; omissions and broader exclusions require
explicit review. Preserve existing static modes, schema admission, source/oracle
pins and temporal-rejection checks outside explicit behavioral profile selection.
Document non-default integration, manual intake, immutable accepted-SHA repins,
source delta review and the ordered upstream-first final merge/revalidation gates.
Implementation and proof coverage are recorded in the component contracts; this
matrix alone does not establish their qualification or acceptance.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Behavioral structural handoff

`req~compiler-behavioral-structural-bridge~1`

Under explicit `behavioral-0.5.7-candidate/v1` selection, provide resolved structural
admission, authored identity/default correspondence and typed observation APIs
for the complete structural prerequisites in B01/B04–B08/B18–B19/B31–B32.
Use accepted S4 meaning for nested abstracts, refined parents, concrete supers,
ordinary inherited children, nearest inherited/refined references and effective
group unions. Keep names, IDs, head occurrences and targets distinct. Preserve
actual-parent navigation, one-step coercion, group/default provenance and strict
partial integer operations, with explicit finite observation and conservative
range conditions. Diagnose unsupported domains and `:=`; supply enum/finality and
constant-initializer sugar to the full frontend without enabling static temporal
syntax. Expose original source fixtures and proved APIs for dependent features.
Document exact successful-admission, source-coverage, role, observation and range
theorems and their premises, distinguishing them from native/parser tests and
future target composition. Preserve static behavior and comparison fixtures;
review an immutable accepted-SHA repin and retain its source delta and full checks.
The [component contract](behavioral-structure.md) records delivered APIs and C7/C8
handoff obligations; no required row is deferred out of full qualification.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral authored frontend

`req~compiler-behavioral-frontend~1`

Under explicit `behavioral-0.5.7-candidate/v1` selection, parse every accepted
behavioral modifier, temporal operator/alias, transition/guard/chain, lifetime
anchor, pattern/scope, assertion and scenario source form. Preserve layout,
precedence, original spans, syntactic polarity, lexical binders and attachment
ownership. Retain all repeated/combined reference modifiers in either order on
direct and inherited references. Keep model/scenario selection and assertions
distinct; reject unsupported objectives, escapes, domains and default initializers
explicitly. Preserve static-profile temporal rejection. Record an independent
grammar and distinguish tested recognition from proved elaboration. The
[frontend inventory](behavioral-frontend.md) states current APIs and their proof/testing
boundaries; parsing is not semantic admission.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Behavioral source elaboration

`req~compiler-behavioral-elaboration~1`

Resolve and elaborate the complete accepted behavioral source into the independent
upstream source rules. Preserve authored/effective metadata, context/parent lifetime
selection, time-spanning captures, strict definedness and attachment identity.
Implement initial/final/inherited-reference expansions, enum finality, constant
initializers, all thirty pattern cells and required transition chains. Preserve
response-between and first-opener precedence-after corrections and the distinct
finalref/finaltarget meanings. Compose whole-expression range obligations without
assuming constraint truth. Prove executable normalization and source elaboration
agreement, beyond well-formed output; distinguish universal assertions, classical
counterexample failure and existential scenarios. Grammar recognition, native
execution and reference-tool outcomes remain separately tested boundaries.
The [reduction inventory](behavioral-frontend.md#executable-reductions-and-proved-boundary)
records source derivations, composed interpretation/normalization and complete
range-check obligations, with explicit scope premises. Coverage does not replace
source-matched qualification or independent semantic acceptance.

Select behavioral `literal-empty-navigation/1`: a parsed literal `noclafer` root
with parenthesized or nested dot/name tails, including `parent`, `dref` and
unknown/ambiguous names, elaborates as unary empty without tail lookup. Exclude
primitive extents and arbitrary expression tails from the shortcut. Preserve
partial enclosing cursors and every ordinary check outside it. Keep the independent
source rule and successful elaboration certificate aligned. The
[exact syntax and warning policy](behavioral-frontend.md#literal-empty-navigation-and-successful-warnings)
does not change static lookup, temporal meanings or upstream profile pins.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Trace assurance planning contract

`req~compiler-trace-assurance~1`

Specify independently defined infinite source and Alloy temporal meanings, a
concrete shared identity correspondence over the whole trace, finite observation
and integer conditions, and separate lasso unfolding. State soundness, bounded
completeness, frontend and decode/encode theorem boundaries without assuming
source satisfaction in soundness or target truth in representation/Fits premises.
Preserve strict partial-domain obligations and signed parent-lifetime meaning.
Assertions use classical failure of the interpreted property, not source negation.
Separate identity budgets, trace-step/loop limits and integer bitwidth/ranges;
retain typed malformed/unsupported diagnostics and distinct SAT, bounded UNSAT,
unknown, timeout, violating and undefined outcomes. Require fixtures exposing
replacement, reappearance, loop-edge history, occurrences, signs and range failures.
Identify parser/text/native/solver trust separately. These are required theorem
shapes and review obligations, not claims of completed proofs.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Behavioral resolved IR

`req~compiler-behavioral-ir~1`

Provide explicit first-slice version/profile admission over the guarded structural
core, retaining resolved declaration IDs, authored/effective metadata, source
spans and unique attachment occurrences. Represent both source signs,
X/F/G/U/W, initial/final anchors, Boolean connectives, captured sets and lexical
quantifiers, including the raw `one`/`lone` counting barrier. Reject unsupported
profiles, requested constructors and attachment forms without changing static
admission. Retain one finite identity inventory, fixed direct types/parents,
changing presence and distinct reference heads. Check representation invariants
and separate identity, step and reference-observation bounds. Structural state
satisfaction remains an explicit upstream obligation, not a result of these
representation checks. See the [first-slice contract](behavioral-ir.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral interpretation

`req~compiler-behavioral-interpretation~1`

Interpret the executable first slice into accepted immutable upstream S2/S3
definitions. Prove structural admission, signed normalization and finite set/atom
evaluation agreement, including captures, current navigation and attachment
ownership. Define one identity correspondence for the entire trace independently
of satisfaction. Preserve first-parent-absence cancellation and reappearance,
with checked contrasting lifetime witnesses on an admitted source trace. Keep
classical target negation distinct from source negation. This slice does not
provide partial atoms, a finite temporal satisfaction evaluator, target
preservation or the complete behavioral profile. Its
[interpretation handoff](behavioral-ir.md#proof-handoff) states exact boundaries.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral first-slice encoding

`req~compiler-behavioral-encoding~1`

Compile admitted `behavioral-core/1` documents to the independent temporal target
with explicit object, declaration, step and integer bounds. Allocate one static
identity/type/actual-parent inventory and mutable live/reference relations.
Generate identity, lifetime and structural snapshot obligations, and preserve
attachment ownership, both source signs, X/F/G/U/W, frozen sets and quantifiers.
Retain the raw `one`/`lone` counting barrier. Return checked target syntax and
source maps; compilation alone makes no satisfiability claim. Keep the static
driver and its admission unchanged. The [encoding contract](behavioral-encoding.md)
records the first-slice API and capacity costs.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral trace representation

`req~compiler-trace-representation~1`

Provide executable finite trace encoding and checked decoding, preserving one
global identity bijection, root, fixed direct type and actual parent, each live
extent, reference-head occurrences, all frames and the loop index. Representation
contains data equations only. Distinct heads with equal referents remain distinct;
per-state renaming cannot disguise replacement. Prove concrete representation
and round-trip boundaries and derive decoding data from independent target facts.
Do not substitute assumed source validity or target truth for these equations.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral first-slice correctness

`req~compiler-behavioral-correctness~1`

Prove signed formula and definedness preservation over the concrete trace
representation. Derive source validity and attachments from the actual successful
compiler output. Prove bounded completeness for representable source lassos with
data-only identity, scope, step and integer-observation capacity assumptions.
Connect live snapshots to the existing structural backend's emitted declarations
and facts, reusing its soundness and completeness results. Distinguish these
in-memory kernel statements from tested text serialization, native execution,
Analyzer solving and witness replay. Retain distinguishing SAT/UNSAT fixtures for
all core temporal operators, lifetime cancellation, identity replacement, frozen
captures and missing invariants. Full-profile frontend/runtime qualification and
arbitrary infinite-trace finite representability remain separate obligations.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Partial behavioral lowering primitives

`req~compiler-behavioral-partial-lowering~1`

Retain source definedness separately from raw and signed target truth when
composing partial behavioral formulas. Boolean operands and both conditional
branches remain strict. Temporal domains follow the original source formula:
next checks the next active state, future operators check the entire remaining
parent lifetime, and inactive birth/death anchors impose no operand obligation.
Quantifiers require every admitted member's body to be defined; captures freeze
the same collection for truth and definedness. Keep raw counting barriers.
Classical assertion failure negates the complete attached property, including
definedness. Prove these composition laws and retain distinguishing counterexamples.
Concrete partial observations, full-profile representation and composed compiler
soundness/completeness remain required by the [complete encoding contract](behavioral.md#independent-trace-assurance).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Full behavioral preservation

`req~compiler-full-behavioral-correctness~1`

Compile the complete selected behavioral expression and structural profile at the
elaborated in-memory boundary. Prove preservation of original partial values,
raw truth and both source signs through the actual recursive lowering, including
frozen captures, whole-tuple counting and repeated aggregate occurrences.
Derive source structural validity and model/query satisfaction from successful
compilation and satisfaction of its actual target module. Prove the reverse for
represented source lassos under concrete data-only identity, declaration scope,
integer observation, count and step bounds. Keep the primitive source integer
carrier mathematical and infinite. Connect successful source elaboration to
these results, retaining parser, native execution, serialization and solver
boundaries explicitly. No assumed expression agreement, target truth in `Fits`,
per-state identity renaming or bounded solver result replaces a proof.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Behavioral property commands

`req~compiler-behavioral-property-commands~1`

Compile a run request as model-plus-scenario satisfaction and a check request as
classical failure of the complete asserted property. Assertions are separate
from model facts. Undefined asserted properties are counterexamples; source
negation retains the original strict domain and signed lifetime meaning.
Preserve implicit-always attachment and explicit lifetime anchors. Prove these
command meanings for the actual compiled module and retain distinguishing native
counterexamples, including undefined assertions and additional scenarios.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Serialized temporal traces

`req~compiler-temporal-decode~1`

Strictly decode the complete Analyzer frame/loop schema for `behavioral-core/1`.
Validate table metadata, closed fields, unique tuples and the global inventory;
reject unknown atoms, truncated states, invalid loops and changing static types
or parents. Preserve root, immutable identities and parent data, each mutable
live set and every reference-head occurrence under one global bijection. Keep
target sets separate from their occurrence heads. Primitive integer observations
are unsupported in this profile and must not be silently erased. Decoding tests
do not extend the in-memory representation proofs to JSON or native execution.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Exact temporal comparison and replay

`req~compiler-temporal-comparison~1`

Evaluate the same finite candidate with the pinned upstream verified evaluator,
the native compiler's Alloy and the pinned historical Haskell Alloy in the
documented common domain. Establish executable source-lowering correspondence
before using that evaluator. Fix every observed table, every stored state and the
loop under one global renaming. Accept neither per-state renaming nor stuttering
or different lasso presentations as equivalent. Retain satisfied and violated
candidates, both discrepancy directions, seeds, source/IR/Alloy and tool identities,
effective options and original scopes. Verify those artifacts before fresh replay.
Provide discrepancy-preserving live/reference-row minimization at the original
identity/step bounds, explicitly distinguishing deletion minimality from a global
minimum. Retain every attempt and report inconclusive minimization if any required
query fails. Malformed, unsupported, error, resource limit and timeout results
must not count as bounded UNSAT. Haskell expectations identify the exact profile
and revision; historical discrepancies do not qualify a newer generator. Paired
source/IR formula agreement is a reviewed fixture premise until full frontend
qualification. The [comparison contract](temporal-comparison.md) records this
boundary and the distinguishing lifetime/identity/loop tests.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Resolved behavioral command

`req~compiler-behavioral-cli~1`

Expose `compile-behavioral-ir` with explicit versioned `behavioral-core/1` IR,
identity/declaration scopes, step bounds and bitwidth. Strictly admit original
declaration IDs, lexical indices, constructor arities and attachment metadata.
Produce deterministic checked Alloy or the documented JSON compilation envelope,
reuse stable diagnostics and preserve existing output on failure. Compilation
runs with only the native executable and its library closure; it requires neither
Haskell nor Alloy and never invokes a solver. Keep the static command/profile
contracts unchanged. Compilation success says nothing about satisfiability;
bounded UNSAT is a separate external result. Document all input/output schemas,
first-slice exclusions and diagnostic codes in the
[resolved runtime contract](temporal-comparison.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Behavioral source integration

`req~compiler-behavioral-integration~1`

Expose the complete `behavioral-0.5.7-candidate/v1` source frontend and encoder
through a separate native command, with closed versioned bounds for nonprimitive
identity pools, declaration scopes, steps and observed integer values. Preserve
authored source locations, deterministic output and source maps. Select model
compilation, universal assertion counterexamples and additional existential
scenarios explicitly; preserve scenario ownership and source attribution.
Reuse checked in-memory requests and temporal serialization. Compilation needs
only the native runtime, invokes no solver and preserves output on failure.
Keep static and first-slice commands and schemas unchanged. Parser, JSON,
serialization and native execution remain tested boundaries beside the existing
full frontend preservation theorems. The [source workflow](behavioral-source.md)
records the concrete API, bounds, reuse and qualification limits.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Behavioral source qualification

`req~compiler-behavioral-qualification~1`

Retain full-profile source/IR pairing, exact lasso comparisons with one global
identity map and separate finite integer observations, positive and deliberate
negative feature/interaction witnesses, replayable source/tool identities and
explicit compilation/checking measurements. Distinguish executable reference
checks from kernel-checked correspondence and from revision-specific Haskell
comparisons. Unsupported requests and timeouts are inconclusive, never passes.
Independent review and source-matched full regression evidence remain required
for candidate acceptance; bounded agreement does not establish universal proof.

Covers: `intent~compiler-foundation~1`

Needs: impl, utest

## Behavioral main integration

`req~compiler-behavioral-main-integration~1`

Pin the accepted immutable semantics-main commit and deliberately regenerate the
dependency manifest. Review the delta from the qualified behavioral and static
baselines, preserving source meanings, tool identities and historical evidence.
Reconcile compiler main and retain full source-matched static and behavioral
IntentBond, kernel, native and Haskell/Alloy qualification. The final integration
PR requires all three existing validation jobs; ordinary main PRs retain routine
checks. Keep current documentation and the complete feature/assurance inventory.
Independent review and concrete authorization precede main merge. Record actual
merged commits and matching evidence before closing the gate; tags and binary
publication require separate selection. See [main integration](qualification.md#main-integration).

Covers: `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible build and assurance bootstrap

`req~compiler-build~1`

Pin the Lean toolchain and Clafer Lake dependency to the source register and retain
the upstream-compatible transitive manifest. Build every owned compiler and Lean
test module, including modules unreachable from the root import. Build and run
the native executable, including its version and argument rejection protocol.
Exercise the source and resolved-IR commands specified below.
Retain the pure version and empty-argument response equations; those equations
prove neither IO nor compiler correctness.

Every full check must replay the project/test kernel declarations and audit their
module origins, including private/generated declarations. Reject project axioms,
`sorry`/`admit`, unsafe/partial declarations, and transitive axioms other than
`propext`, `Classical.choice` and `Quot.sound`. Check the executable import closure
excludes upstream semantics and proof-only modules. Document native IO/tooling
trust. Fail on absent tools, failed gates, empty/skipped regressions and unknown
module ownership. Retain source-bound IntentBond evidence before handoff. Cached compiled artifacts
may be reused only through Lake's source/options/import validation, with local
restoration for fresh axiom inspection and kernel replay. Separate comparison-tool
caches must still pass their pinned source/recipe/binary identity checks. Never
reuse a previous proof/test result as current evidence. Report validation timings
and bound concurrent regressions without dropping cases or relaxing per-command
time limits. Amendments to the overall check deadline require explicit scope review.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Reproducible comparison oracles

`req~compiler-oracles~1`

Reuse the immutable upstream capture/import/comparison adapters with the pinned
Haskell 0.5.7 library, Stack/GHC/dependency profile, Lean semantics and Alloy 6.2.0 JAR.
Retain source and tool hashes, same-generation IR/Alloy receipts, actual Java
vendor/build, effective static SAT4J options, explicit per-UID scopes and signed
bitwidth. Run the actual tools on positive and negative candidates; preserve
reference occurrences. The initial profile uses Java 17 and upstream bitwidths
1–16 with independent range admission. Reject temporal source/backend dispatch.
Require the paired UID-to-Alloy map, strict modifier arrays and zero scopes for
unused abstracts. Reject stale generation/version/build receipts. Preserve old
0.5.4 evidence with its original compiler revision and tools; the current runtime
has one structural profile. Behavioral comparison profiles remain independent.

Run the finite checker only after its guarded constraint-free admission. Keep
inherited fields, primitive integer references and expressions unsupported;
leaf abstract inheritance remains admitted when its guards hold. Inventory
structural, set/bag, group, inheritance, reference-cycle, shadowing and numeric
fixtures with immutable provenance and licenses. Preserve bundled distribution
notices externally and preserve applicable licenses when packaging tools.

Missing tools, modified inputs/tools, unsupported domains, timeouts, resource
limits, malformed input and errors must remain distinct from agreement or bounded
UNSAT. Required checks fail rather than skip. Retain exact candidates, both
outputs, options and replay instructions outside source. Discrepancies require
minimized evidence, independent expected semantics and an issue before semantic
changes. Haskell is supplementary evidence. This base oracle establishes neither
compiler correctness nor a new proof; the [three-way comparison](comparison.md)
adds downstream compiler Alloy to the comparison.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible temporal comparison oracles

`req~compiler-temporal-oracles~1`

Select `behavioral-0.5.7-candidate/v1` explicitly for the pinned Haskell 0.5.7
candidate and Alloy 6.2.0. Build and execute the unchanged Haskell library;
retain paired source/JSON/Alloy/options, source-tree and exporter build hashes,
actual Java identity, JAR identity and every effective solver option. Reuse
existing provisioning without changing static oracle pins or temporal rejection.

Run the registered positive/negative corpus for stable and replaced machines,
both source signs under parent cancellation, persistent parents, identity scope
one versus two, fixed parents across lifetimes and inherited final references.
Pair assertion checks with satisfiable model runs at identical identity, integer
and step budgets. Retain complete lasso frames, one shared atom inventory and the
loop index; distinguish identity capacity, per-state population and trace length.
Keep SAT, bounded UNSAT, malformed/unsupported input, tool/resource failure and
timeout separate. Missing GMP/exporter prerequisites fail explicitly; no skipped
Haskell gates. Inventory fixture hashes/licenses before execution and preserve
hand-checked witnesses and known comparison gaps separately from source truth.

Replay verifies retained artifacts and reruns the same compiler and bounded query.
Exact source-candidate decoding/replay and semantic preservation remain C9's
obligations. These bounded tool tests establish no new kernel theorem or blanket
Haskell equivalence. Adoption of final 0.5.7 release bytes requires an immutable
delta review, repeated corpus execution and explicit acceptance; preserve the
candidate and static receipts.

Qualify later PR113 bytes under the separate `behavioral-pr113-9a0f16e/v1`
candidate profile. Retain the complete delta inventory, same-generation forward
UID/Alloy mapping and renamed backend IR; reject incomplete, ambiguous or
inconsistent mappings and mixed scalar/array modifier schemas. Exercise both
modifier orders on direct and inherited references, swaps, target-image changes,
head replacement, set-versus-bag multiplicity and corrected pattern witnesses.
Keep the old revision's discrepancies executable. Freshly generate and recompile
every registered temporal explicit model, including imported source closures,
and retain both scope files, effective options and trace length. Pair original
and explicit bounded runs/assertions using the original model's scopes and
identical solver budgets. Printer fixed points and bounded outcome agreement
are weaker than exact-lasso equivalence; they do not discharge C9 or the Lean
explicit-form preservation task. This qualification does not adopt a new primary
compiler pin; independent delta review remains required.

Qualify `c7a2fb7` separately as `behavioral-pr113-c7a2fb7/v1`, retaining both
historical profiles. Derive union field endpoints from captured resolved target
expressions and the forward UID map; check ownership, arity, hierarchy and actual
Analyzer type products. Admit only the selected direct, containment-navigation
and union forms, preserving the structural importer's expression-target rejection.
Include the static navigation fixture with explicit backend and integer handling.
Keep exact original/explicit bytes, fixed points, original scopes and matched
bounded queries. Record actual warning callbacks, including an old unused-root
binder positive control; warnings are neither counterexamples nor tool failures.
Check root cardinalities, constraints and assertions retain `always` and bind
`this` to the singleton permanent root; nested instances retain their live guards.
Retain source-map spans and identifier boundaries. Distinguish recurrence from
`initially` with positive/negative traces and a removed-`always` mutant. Document
unsupported captures and parse failures without changing independent semantics.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Executable structural IR and admission

`req~compiler-ir~1`

Provide finite executable M1 declaration tables with stable input IDs distinct from
names, resolved parent/super/reference edges, effective bounds, optional authored
metadata and original byte spans. Preserve declaration/reference-head identity;
never merge repeated names or targets. Resolve raw IDs deterministically, rejecting
duplicates, dangling edges, malformed metadata/certificate shape, invalid intervals
and cyclic parent/super graphs. Permit reference cycles. Use checked ranks and
unused-abstract certificates for exactly the upstream guarded effective domain.

Interpret all semantic fields into the pinned independent effective core. Prove
both directions of guard agreement, successful admission's actual upstream
well-formedness/support, preservation of the original typed table, and completeness
with suitable certificates. Prove finite lookup soundness/completeness under unique
IDs. Do not confuse admission with candidate satisfaction or bounded UNSAT.

Specify the closed versioned `clafer-ir/1` JSON interchange and deterministic
malformed/unsupported diagnostics, including strict types, duplicate-key rejection
and explicit effective-only provenance. Implement version/profile selection on
already decoded data; the [native driver](cli.md) supplies strict file/JSON
parsing and diagnostic serialization.
Reject unknown profiles and primitives; no static expression or inherited semantics
are admitted by extension placeholders. Retain tested raw resolution/native behavior
separately from the proved typed-core boundary and serialized execution.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Resolved structural normalization

`req~compiler-resolved-normalization~1`

Canonicalize the effective local bound of every parentless abstract declaration
in the existing resolved structural `Core` to `0..*`. Define normal form
independently by that field condition. Preserve declaration count/order, IDs,
names, origins, parent/super/reference edges, set/bag mode, abstractness, group
bounds, root and source/authored metadata exactly. Preserve all other local
bounds, including the concrete root's slot. Equality is full in-memory structural
equality, including metadata; this is not a canonical form of all equivalent
models or a source/text serialization contract.

Provide a total operation on validated M1 values retaining the exact certificate,
and a checked typed-core API that validates the original input before rewriting.
Preserve original admission failures, including invalid intervals, unsupported
zero-bound abstracts and invalid certificates. Prove output normal form,
fixation of every normal-form core, idempotence, M1 admission preservation,
successful checked normalization of admitted normal forms, and equivalence of
upstream structural satisfaction for the same configuration. Reuse the operation
in source-to-M1 conversion with a proof of equality to its existing projection.

Retain positive and negative kernel/native witnesses for nontrivial abstract
chains, stable identities/references/provenance, parented bounds, repeated names,
already-normal inputs and admission-before-normalization. Solver scopes remain
caller-owned and ID-keyed; this API neither consumes nor changes them. Source
parsing, UID generation, byte equality, behavioral normalization and Haskell
execution remain outside this contract. See the
[resolved normalization contract](ir.md#resolved-structural-normalization).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Independent static Alloy target

`req~compiler-alloy-core~1`

Provide resolved static unary/binary target syntax and an admission API that
rejects malformed references, bindings, arities and declaration hierarchies.
Define finite target instances and compositional relation, formula, declaration,
fact and run/check satisfaction independently of source semantics and compilation.
Preserve atom identity, parent inclusion, sibling/top-level disjointness, Alloy's
abstract-leaf behavior, owner-first field direction and fiber multiplicity.
Distinguish malformed candidates from well-formed violating candidates.
Document auxiliary/unused atom policy and the source invariants the
[structural encoder](structural-encoding.md) must generate.

Maintain the construct correspondence and retained source identity against the
official reference. Kernel-check constructor laws and independent truth tables,
and compare representative equivalent formulas through the pinned real Analyzer.
Keep formal target properties distinct from tested Analyzer correspondence and
serialization/source preservation proofs. See the [target contract](alloy-core.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Independent Alloy temporal target

`req~compiler-alloy-temporal-target~1`

Provide a separate checked Alloy 6 temporal target for the selected behavioral
profile. Define finite shared identity inventories, static and mutable declarations,
current `univ`/`iden`, captured environments, relational prime and ordinary
future/past truth independently of source truth and compilation. Facts begin at
time zero; invariants require explicit `always`. Include next, strong/weak until,
release and justified past-time birth guards. Type disjointness and identity scopes
apply across the whole trace. Define nonempty lassos, valid loop indices, explicit
step bounds including the closing edge, and representable signed integers.
Preserve initial history when unfolding repeated frames. Reject malformed syntax,
unsafe bounds and malformed lasso shape distinctly from candidate violation.
Document the admitted target subset and future encoder responsibilities without
reducing the behavioral source completion matrix. Kernel-check operator/lasso laws
and retain actual pinned Analyzer positive/negative witnesses and their bounds.
The [temporal target contract](alloy-temporal.md) states exact APIs and limits.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Checked temporal Alloy text

`req~compiler-alloy-temporal-text~1`

Serialize admitted temporal targets deterministically with explicit mutability,
operator grouping, step/identity/integer scopes and hygienic names/source maps.
Keep source labels out of executable text. Reuse the static identity namespace
and map guarantees without changing static output. Validate complete reconstruction
of emitted temporal text through an independent grammar before returning success;
retain typed metadata/correspondence errors and the conditional successful-render
proof boundary. Test actual Alloy parsing and bounded solving, distinguishing
native/parser/solver evidence from kernel proofs or source preservation.
See [temporal serialization](alloy-temporal.md#serialization-and-source-maps).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Explicit target bounds and checked cardinalities

`req~compiler-bounds~1`

Require complete explicit exact/upper scopes and the accepted signed bitwidth
profile. Reject incompatible signature-multiplicity scopes and unsafe literal
or count ranges before evaluating a candidate. Use conservative finite column
budgets, including binary endpoint products and union inventories, independently
of facts and successful satisfaction. Check every fact/command branch and binder
body. Count distinct tuples, retain runtime representability checks and propagate
undefined integer observations distinctly from false. Scope allocation numerals
and multiplicity predicates do not themselves introduce Alloy integer expressions.

Preserve valid scopes excluding every model as unsatisfiable constraints; source
compilation may express conflicting declaration multiplicity as a fact.
Do not infer scopes, encode infinity as an integer, silently wrap arithmetic or
add richer M2 integer operations. State the proof/test boundary of range analysis.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Hygienic deterministic Alloy text

`req~compiler-alloy-text~1`

Render every selected target constructor using legal identity-based names,
explicit precedence/grouping, multiplicities, declaration ownership, command
polarity and complete exact/upper scopes. Retain original source names and byte
spans in deterministic declaration maps, never executable syntax. Handle repeated,
shadowed, reserved, Unicode and internal names without capture or aliasing.

Prove name injectivity and print/parse reconstruction against an independent
parser for the emitted subset, or obtain explicit review for an alternative
assurance boundary. The [candidate boundary](alloy-text.md#proved-boundary-and-review-obligation)
proves reconstruction for successful rendering by translation validation;
unconditional successful renderability is not claimed and remains a review
consideration. Preserve whole target identity, reject malformed metadata and
failed correspondence, and keep native execution and actual Alloy parsing/solving
outside the kernel claim. Compare real pinned Analyzer ASTs and exact-candidate
meaning, including grouping/name mutations. Extend all constructor checks with M2.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Guarded structural encoding

`req~compiler-structural-encoding~1`

Translate the exact admitted M1 effective IR into the independent static target
with deterministic declaration/field allocation and complete explicit ID scopes,
total object budget and signed bitwidth. Preserve declaration and reference-head
identity, inherited membership, owner-first containment/dereference, set/bag keys,
local intervals and union-of-child-head group counts. Enforce root singleton and
freshness, typed endpoints, used-object coverage, abstract cover including empty
families, and global incomparable declaration disjointness. Reject non-M1 inputs
through existing admission; do not narrow the source domain or silently drop facts.

Return checked target syntax/bounds and a source-ID/name/span map with obligation
labels. Distinguish malformed manual bounds, unsafe range profiles and internal
generation errors from contradictions: well-formed scopes excluding all models
still compile. No inferred bounds or implicit solver calls. Prove local inventory,
identity, field-direction and generated-fact lemmas; test positive/negative cases
and omission mutations against independent source meaning. Keep finite tests and
local proofs distinct from global soundness, bounded completeness, executable
encode/decode and text/CLI assurance, which remain dependent tasks. The
[encoding contract](structural-encoding.md) specifies the exact layout and handoff.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Finite structural representation

`req~compiler-structural-representation~1`

Provide an executable finite shared-object presentation and in-memory encoder and
decoder for the accepted structural target layout. Preserve declaration extents,
containment tuples and distinct reference heads. Distinguish malformed/root decode
errors from retained semantic violations. State the concrete bijection, root,
extent and active-role tuple equations, including all target atom coverage and
unused-slot policy, independently of either satisfaction relation.

Kernel-prove the encode/decode data round trip under explicit table/root hygiene,
and derive decoder success and a concrete representation from satisfaction of an
actual successful compiler output, including live-atom coverage from target
constraints. Exercise nontrivial bag witnesses, semantic violations, renamed atoms
and malformed tables. Keep these representation results distinct from the global
source-soundness, bounded-completeness and compiled-bank composition obligations
specified in the [correctness contract](structural-correctness.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Structural soundness and bounded completeness

`req~compiler-structural-correctness~1`

For the exact admitted M1 effective domain and a successful compilation, prove
that every independently satisfying target instance decodes to a concretely
represented source configuration satisfying every upstream structural clause.
Derive root, carrier coverage, typed endpoints, inheritance, abstract cover,
declaration disjointness, ownership, references, keys, local bounds and group
unions from the emitted target declarations and facts. Do not assume source truth,
successful decoding or a supplied preservation equivalence.

Conversely, construct a target representation of every finite source configuration
satisfying that independent meaning and fitting the manual scopes and signed
integer observation ranges. State scope counts and numeric definedness separately
from source and target satisfaction. Preserve every source object and reference
occurrence, including repeated bag targets. Compose with the pinned local-bank,
constraint-free erasure and arbitrary-link normalization results while retaining
their actual global hypotheses. Keep native and serialized execution outside the
kernel theorem boundary; bounded absence does not establish unrestricted UNSAT.

Kernel-check nontrivial actual compilation witnesses and mutations distinguishing
omitted upper bounds, collapsed bag heads and missing global abstract cover.
Keep semantic acceptance and dependent task intake separate from automated checks.
The [correctness contract](structural-correctness.md) records exact APIs and assumptions.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Selected inherited structural realization

`req~compiler-inherited-realization~1`

Admit the selected inherited structural domain through a separate explicit API,
retaining authored abstractness and original declaration/occurrence identity.
Check the actual upstream selection, core and primitive-origin restrictions.
Distinguish ordinary fields made effectively abstract by containment from explicit
abstract families. Compile original inherited inventories, cover/disjointness,
ownership and union-based realized groups without creating contextual copies.

Prove soundness and finite bounded completeness against the pinned independent
`Realization.Satisfies`, with numeric scopes/count definedness and finite primitive
observation limits explicit. Preserve the original M1 domain and prove compatibility
of meanings on the overlap. Prove contextual object/link restriction, discharging
live-carrier premises for decoded satisfying targets. Supply actual compilation
witnesses, the complete Appendix 6 structural skeleton and negative ownership,
inherited-group and abstract-cover mutations. Keep scalar primitive interpretation,
constraint bodies and native/serialized correspondence outside these model proofs.
The [inherited contract](inherited-realization.md) records the exact API and limits.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Strict external instance decoding

`req~compiler-instance-decode~1`

Decode actual native-generated Alloy instances into the shared source candidate
protocol, preserving declaration identity, all objects, containment endpoints
and distinct reference heads even when owner/target pairs coincide. Reject
unknown/missing tables, duplicate identities/tuples, invalid arities/endpoints
and malformed roots. Keep well-formed semantic violations distinct from malformed
input. Prove exact row correspondence for the executable export from the existing
structural observation; identify JSON/Analyzer parsing and native execution as
unproved external boundaries. See the [comparison contract](comparison.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Exact three-way candidate comparison

`req~compiler-differential~1`

Within the common admitted capture domain, compare the identical candidate with
the upstream verified checker, same-generation Haskell Alloy and actual native
Lean compilation/serialization/Alloy. Retain equivalent explicit source scopes,
bitwidth and solver options, documenting the virtual versus explicit root layout.
Require exact decoded-candidate isomorphism for SAT, preserve negative candidates
and both discrepancy directions, and never treat raw text equality as the oracle.

Exercise complete tiny enumerations and reproducible seeded generation without
satisfaction filtering. Retain sources, IR, raw candidate/output, maps, tool/source
identities, commands, options, seeds and replay evidence outside source. Verify
replay identities; minimize completed discrepancies with retained attempts and
honest deletion-minimality bounds. Detect injected occurrence collapse, omitted
cardinality/group/disjointness enforcement and swapped endpoints. Keep malformed,
unsupported, timeout/resource and tool failure outcomes separate from completed
agreement. Finite comparisons do not replace the independent backend preservation proofs.
Include reserved/derived-name collisions, qualified names, apostrophe collisions,
renamed inherited references and unused abstracts on positive and violating
candidates. Preserve original source UIDs through the separate Haskell and native
symbol maps and exact decoding.

Provide a runnable [instance-check walkthrough](instance-checks.md) showing
repeated-target bag acceptance, rejection of the identical set candidate and a
passing distinct-target set control, within this same comparison domain.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Authored static source parsing

`req~compiler-parser~1`

Parse the adopted static surface whitelist into authored syntax independently of
name resolution, defaulting, typing and generation. Implement layout and explicit
braces, declarations/use shorthand, direct references and inheritance, keyword and
numeric groups/cardinalities, and every selected hard-constraint expression with
the pinned precedence/associativity. Preserve original source, spelling, UTF-8
spans, omitted versus authored values, group keyword provenance, set/bag arrows,
binders and constraint attachment occurrences. Match the pinned Latin-1 lexer
character class without normalization or silently narrowing it to ASCII.

Reject malformed layout/intervals and recognize excluded primitives, operators,
initializers, escapes, directives and all temporal forms without erasing them.
Describe the grammar independently in the [parser contract](parser.md). Exercise
native examples, malformed mutations, finite generated properties and live pinned
Haskell syntax comparisons, retaining differences and tool failures separately.
Reuse the pinned Lean parser primitives and existing oracle tooling. Keep the
unproved grammar/parser/native boundary explicit; successful parsing does not
establish resolution, type correctness, admission or satisfaction.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Source declaration resolution

`req~compiler-resolution~1`

Resolve the accepted authored declaration tree deterministically into finite
identity-based structural tables. Preserve every declaration, its source path and
span, repeated names in distinct contexts, parent/super/reference edges, set/bag
head identity, original constraints and their owner occurrences. Resolve forward
and cyclic references without following target edges recursively. Require unique
nearest lexical lookup or unique global lookup, with explicit parentless abstract
types for supers. Reject missing/ambiguous names, duplicate siblings, reserved
user names, inheritance cycles and excluded inheritance forms with stable source
diagnostics. Integer aliases refer to one explicitly classified canonical primitive.

Define independent source coverage, lookup and elaboration rules and kernel-prove
that successful elaboration satisfies them and yields the upstream well-formed
structural core and selected realization domain. Well-formed output alone is
insufficient. Retain ordinary inherited fields and explicit abstract families;
keep constraints available for [expression elaboration](constraints.md). The
explicit M1 conversion must reject richer features and constraints, and pass the existing exact M1 admission. Compare
resolved fields with the pinned importer on its common domain, retaining expected
identity/provenance differences. See the [resolution contract](resolution.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Authored and effective defaults

`req~compiler-defaults~1`

Retain omitted versus authored multiplicity, group keyword versus numeric
provenance, explicit abstractness and effective inherited abstractness. An omitted
group inherits the superclass's complete effective group, otherwise unrestricted.
An omitted parented local bound is `0..1` under a keyword group or a numeric
group other than exactly `0..*`; numeric `0..*` gives `1..1`. Authored bounds
override it. Preserve this distinction through inheritance, including `opt`
versus numeric `0..*`. Effective abstractness is the explicit flag or the parent's
effective flag. Kernel-prove agreement with pinned `Clafer.Defaults` and test
child-default agreement with Haskell 0.5.7 on the common domain, including
finite/unbounded numeric groups, the unrestricted exception and overrides.
This is the adopted language evolution from Appendix 3, not a paper correction.
Require actual source/native/Alloy witnesses in which a numeric `1..1` group
admits either of two unannotated children and rejects zero or both children.
Do not fabricate parent fibers for parentless abstracts. An explicit M1 projection
may normalize that unused local slot to unrestricted while retaining authored metadata; it must preserve every other declaration field.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Source frontend diagnostics

`req~compiler-diagnostics~1`

Return a deterministic version-1 source diagnostic with stable code, phase,
malformed/unsupported category, message, logical filename, primary zero-based
half-open UTF-8 byte span, one-based line/scalar column and related locations.
Retain original CRLF/Unicode byte offsets and use zero-width EOF locations.
Fail without a partial successful document. Distinguish recognized excluded
features from missing/malformed syntax. The resolver supplies name/default
diagnostics. The constraint elaborator supplies typed-expression diagnostics with
phase `type`; its source constraint contract specifies the accepted inference rules. Exact
English wording is not stable. The parser returns the first lexical error,
otherwise the first grammatical error.
The [native driver](cli.md) serializes source diagnostics and supplies IR-only
locations and process exits for both commands. No source coordinates are invented
for developer IR. The resolver prioritizes declaration/name checks, edge resolution, inheritance and
realization ranks, then independent source correspondence validation.

Behavioral successful-report APIs additionally return nonfatal warnings for literal
empty navigation and syntactically identical operands of `=`, `!=`, `--`, `**`.
Preserve ordinary operations, typing, range admission and strict definedness.
Use stable warning severity/codes/operators and authored source locations, with
one navigation warning per maximal skipped chain. The CLI emits separate
`clafer-warning/1` records on stderr under `--diagnostics json`, or located text,
while preserving exit `0`, compilation output schemas and existing error APIs.
Failures do not emit partial warnings. The
[warning protocol](behavioral-source.md#successful-warning-protocol) fixes ordering
and compatibility; the static profile retains its established behavior.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Native resolved-IR command

`req~compiler-cli~1`

Provide the standalone `compile-ir INPUT --bounds BOUNDS --output OUTPUT` command
for the exact guarded `clafer-ir/1` M1 profile. Decode strict UTF-8/JSON without
losing duplicate keys, numeric token forms, unknown semantic fields or identities;
compose existing admission, structural compilation and checked serialization.
Require complete declaration-ID scopes, a distinct-object budget and explicit
bitwidth, with documented overrides. Report the compiler version and exact
semantic/reference pins; source-text compilation remains explicitly unsupported.

Document deterministic input/output, diagnostics and exit behavior. Read stdin or
files and emit complete Alloy to stdout or replace a file only after successful
rendering. Malformed inputs exit 2, unsupported features/ranges exit 3, operational
failures exit 1, compilation exit 0. Preserve existing file output on failure before
rename. Never infer SAT/UNSAT or invoke a solver implicitly. Retain declaration
identity and generated source maps in the pure API for dependent integration.

Run the native binary with only its documented runtime libraries visible, without
a Lean development toolchain, Haskell, Java or Alloy. Exercise real Analyzer loading
and solving as external validation. Keep tested JSON/CLI/native behavior distinct
from existing in-memory proofs. The
[CLI contract](cli.md) supplies examples, platform limits and review boundaries.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Executable typed static expressions

`req~compiler-expressions~1`

Provide executable finite support and annotated syntax for every adopted M2 typed
core constructor, with checked sorts, lexical positions, fresh nested binders,
explicit identity/inclusion widening and original byte spans. Preserve `this`,
global extents, repeated map occurrences and operand order. Reject malformed
annotations and direct observations of the complete primitive integer extent.
Return the original tree with checked typing and observation evidence.
Include defined empty collections at both core arities, with no extent/map reads
and budget zero. Keep unary/binary, Boolean and scalar sorts distinct; primitive
empty collections are finite and singleton extraction from them is undefined.

Interpret successful typed trees into the pinned independent typed core, using
its existing partial denotation. Prove exact admission, footprint preservation
and admissible environment interpretation. Undefined remains distinct from false;
reference-head and target-set counts remain distinct. Permit map-free literals
through direct denotation without changing upstream Compile support. This API
neither extends M1 admission nor implements a parser, general finite evaluator,
Alloy constraint encoding or production CLI. See the [expression contract](expressions.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Static arithmetic and finite observation

`req~compiler-arithmetic~1`

Retain mathematical Int meaning with explicit width, finite observation budgets,
value intervals and separate definedness obligations. Conservatively check every
literal, integer extraction and arithmetic intermediate, including all Boolean
branches and binder bodies, for signed representability at widths 1–16. Reject
unsafe profiles as unsupported, without wrapping or asserting UNSAT. Check
candidate observations and external environments against their recorded budgets
and intervals independently of constraint truth.

Prove exact finite singleton extraction, interval transfer/representability,
and construction of full-integer bindings retaining nonprimitive objects and
original links under explicit independent model obligations. Prove admitted
expression denotation invariant across such extensions and finite meaning for
admitted collections, including integer navigation and quantifier domains.
Keep primitive/root structural composition explicit; do not claim whole-domain
finite equivalence. Prove the executable range analyzer sound against that
independent denotation: every defined number lies in its returned representable
interval and every collection's distinct cardinality meets its returned budget.
Derive finite recorded membership through navigation, widening and lexical binding
from checked observations. Include every numeric intermediate and actual quantified
body, without assuming final constraint truth or successful singleton extraction.
Compose the finite-observation bridge for arbitrary full-integer extensions and
show scalar compatibility with target bounded-integer admission. Source-to-target
expression/attachment preservation is specified below; structural source pipeline
composition is specified by the
[pipeline requirement](#integrated-source-pipeline-and-composed-correctness).
See [source range proofs](expression-encoding.md#source-range-analysis-proofs).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Source constraint elaboration

`req~compiler-constraint-elaboration~1`

Elaborate the accepted static source expressions over checked declaration tables.
Resolve lexical positions, this, parent, contextual/inherited fields, global
extents and explicit/implicit dereferencing with deterministic missing/ambiguous
name and type diagnostics. Bare names search own/inherited fields and enclosing
parent scopes before the original context's reference target, then use global
lookup. Target fallback retains finite reference chains from that context only;
explicit dotted navigation retains its separate traversal rules.
This adopts compiler precedence rather than Appendix 4's Targets-before-Ancestors
order within the [selected lookup boundary](constraints.md#api-and-lookup).
Preserve original declaration/map identities, attachment
owner, body position and UTF-8 spans. Use actual inclusion paths for common-type
widening; keep reference-head counts distinct from dereferenced target counts.

Expand exactly the adopted connectives, comparisons, presence/cardinality tests,
finite single-object quantifiers and integer operations. Quantifier domains use
the outer environment; fresh identities permit shadowing without capture.
Successful output carries an independently defined declarative elaboration
relation, checked typing and finite-observation admission. Interpret its typed
syntax through the pinned partial denotation, retaining undefined as distinct
from false. Type checking must not assert singleton extraction, numeric bounds,
source satisfaction, or backend preservation. Literal-only bodies need no maps.
Reserve `noclafer` as a unary empty literal with contextually instantiated bottom
element type; keep `none` available for user declarations and binders. Adapt
the literal before reference/scalar coercions, preserving collection
equality with numeric reference heads. Support standalone cardinality, presence,
empty quantifiers and uniquely resolved navigation from emptiness. Keep missing
or ambiguous names and scalar/arity mismatches diagnostic, with no invented class
or inclusion edge. Computed collections retain the resolved typing and strict
partiality described in the [empty literal contract](constraints.md#empty-collection-literal).

Enumerate every original body and prove source occurrence/order preservation;
retain empty bracket groups in the source document without inventing bodies.
Compare all Appendix 6 c01–c12 elaborations with the existing pinned manual
inventory, including parent/server paths, repeated names and display-head counts.
Exercise negative variants, ambiguity, invalid joins and generated nested scopes.
Keep native/parser tests distinct from kernel proofs and semantic acceptance.
See the [source constraint contract](constraints.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Bounded target arithmetic

`req~compiler-target-arithmetic~1`

Extend the independent Alloy target with ordered integer addition and subtraction
over literals, finite distinct-tuple cardinalities and nested integer expressions.
Use mathematical intermediate values with explicit signed representability at
widths 1–16; propagate undefined operands and overflow rather than wrapping or
converting them to false. Conservatively admit every intermediate using explicit
scope-derived count inventories, including branches under negation, implication
and quantifiers. Reject malformed integer stack programs and invalid relation
operands through target admission.

Prove constructor definedness/value equations and checked-interval agreement with
mathematical arithmetic under explicit leaf count-capacity premises. Those
premises must state actual tuple bounds, never final truth or preservation.
Retain the remaining general relation-inventory and source-denotation obligations.
Extend checked serialization and independent parsing for all integer constructors;
exercise the actual pinned Analyzer with independent ASTs, boundary cases and
operand, grouping and lexical-binding mutations. This target layer does not
claim source expression or attachment preservation. See [encoding work](expression-encoding.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Static constraint encoding and preservation

`req~compiler-expression-encoding~1`

Translate every admitted typed static expression constructor into the independent
Alloy target. Preserve lexical positions, owner `this`, original map roles,
ordered operands, explicit identity/inclusion widening and finite primitive
observations. Generate separate definedness and value/truth; undefined extraction
must remain distinguishable from false under negation and quantification.
Conservatively reject all unsafe numeric intermediates, including vacuous bodies.
Encode typed empty collections with true definedness and arity-correct target
emptiness, retaining the existing singleton-extraction failure behavior.

Represent observed integer objects with typed, total scalar fields and emit
interval and injectivity facts. Prove the corresponding enforcement from target
field admission and the generated facts. For checked observations within explicit
budgets/intervals and concrete object/map/scalar representation equations, prove
constructor definedness, value and truth correspondence to the independent pinned
source denotation. Derive numeric representability from source admission; do not
assume successful source extraction, final constraint truth or desired equality.
Retain the finite-observation bridge to arbitrary full mathematical integer extensions.

Compile every attached body in order, retaining original identity, owner and span,
including repeats and inherited owners. Prove exact occurrence preservation and
all-body satisfaction equivalence under the stated representation conditions;
derive source truth from satisfaction of the generated module. Keep full structural
source-pipeline composition and source CLI integration in the
[pipeline requirement](#integrated-source-pipeline-and-composed-correctness).

Extend checked serialization/reconstruction for the emitted scalar and identity
forms. Run native and actual pinned Analyzer checks covering all constructors,
empty/nonempty domains, scalar range/identity, inherited contexts, lexical capture,
ordered operands, parent/dereference confusion, undefinedness and overflow. Keep
these tests distinct from kernel proofs and semantic acceptance.
See the [encoding contract](expression-encoding.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Integrated source pipeline and composed correctness

`req~compiler-pipeline-correctness~1`

Compose the accepted parser, resolution/defaults, constraint elaboration, inherited
backend, expression translation and checked serializer in a native source command.
Retain original IDs, owner/body occurrences, spans and diagnostics; keep M1 IR
compilation available. Require explicit closed version-2 bounds, nonprimitive
object budgets, original declaration scopes, signed width and primitive intervals.
The standalone runtime must not require Lean tooling, Haskell or a solver.

Derive target-to-source representation and satisfaction from the actual successful
compilation and target instance. Construct one rooted selected source model with
all mathematical integers and every original constraint on its full owner domain.
Preserve primitive parent queries, reference occurrences, inherited groups,
undefinedness and all admitted source expression denotations. For full source
models with the concrete finite observation relation and data-only Fits, construct
the target and prove bounded completeness. Fits must not assume target truth,
finite source satisfaction or preservation. State the canonical carrier and
parser/native/text/solver boundaries explicitly; do not present candidate-level
conditional equivalence as composed soundness or completeness.

The implicit primitive uses unrestricted multiplicity and is also inserted for
constraint-bearing source without integer references. This supplies the full
carrier required by the pinned semantics; authored IDs remain stable. The
[full integer carrier](pipeline.md#full-integer-carrier) explains
why both conditions are necessary. Upstream meanings and public M1 guards remain
unchanged.
See the [pipeline proof and reuse inventory](pipeline.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Complete telematics integration

`req~compiler-telematics~1`

Compile the complete supported Appendix 6 source, including all twelve constraints
and final selections, with explicit bounds. Exercise distinct observed integer
values and exact candidate comparison against the pinned Analyzer. Justify the
extended inherited/source observation evaluator separately from the guarded M1
checker. Detect wrong version order, display count, parent navigation, omitted
constraint and missing inherited-group mutations; retain bounded minimized replay
witnesses and state their reduction order. Preserve complete source/candidate,
original maps, scalar rows, commands, tool/source identities and external outcomes.
These finite tests complement the composed proofs, not certify the external tools.

The [instance-check walkthrough](instance-checks.md) shall run a standalone version
`3 >= 2` success and `1 >= 2` rejection with all other obligations valid, then
the complete native source example. Identify final selections within the twelve
bodies, retain exact replay tables and explain the input contract for another
backend without widening the guarded Haskell comparison domain.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

<a id="private-candidate-qualification"></a>

## Candidate qualification

`req~compiler-qualification~1`

Prepare a local candidate with a closed accounting of the adopted feature
matrix: implementation, promised proofs, positive/negative tests and explicit
rejection of excluded forms. Preserve all existing scope and assurance boundaries;
material defects prevent acceptance. Retain the exact clean candidate commit,
source-matched passing IntentBond evidence, complete test/kernel logs, independent
review disposition, immutable tool identities, license attribution and replayable
discrepancies. Bind clean-built standalone artifacts and their isolated runtime
smoke results to that candidate. Reject stale or modified evidence and mismatched
measurements. A pending review remains pending in the package manifest.

Document reproducible usage, supported platforms, trust boundaries and the existing
dependency-upgrade policy. Preserve the upstream SoSyM snapshot independently;
neither a semantics branch nor a research tag gates compiler qualification.
See [qualification](qualification.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible compiler measurements

`req~compiler-performance~1`

Measure parsing, declaration/default resolution, constraint elaboration, backend
encoding, checked rendering, process memory and output size independently of Alloy
solving. Retain raw samples, warmup policy, commands, inputs, explicit bounds,
machine/tool identities and failure outcomes. Use tiny, representative and larger
generated inputs plus the complete supported telematics source. Compare the pinned
Haskell compiler on identical common-domain input bytes and equivalent explicit
scopes/bitwidth/options, accounting for its virtual root and different pipelines.
Force lazy output before stopping whole-process measurement. Do not compare
instrumented stage times as equivalent work or claim blanket Haskell compatibility.

Measure clean-project and warm Lean build/proof elaboration separately from native
compiler runtime and kernel replay; state reused dependency/cache boundaries.
Check the measurement probe against production output. Preserve timeouts/errors as
failures, never silently omit required cases. No speedup threshold or optimization
is promised; any subsequent optimization needs profiling and semantic preservation.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Documentation and workflow artifacts

`impl~scaffold-boundary~1`

[README](../README.md), [intent](intent.md), the
[key proved properties](lessons.md#key-proved-properties), [security policy](../SECURITY.md), and
[license](../LICENSE) describe the current boundary. GitHub visibility is an
external setting: verify it separately before reporting repository publication.

Covers:
- `req~scaffold-boundary~1`

`impl~intentbond-workflow~1`

[Contribution guidance](../CONTRIBUTING.md), [agent instructions](../AGENTS.md),
[pin](../requirements/intentbond.txt), [scope](../scope.json),
[check entrypoint](../scripts/check.sh), and [CI](../.github/workflows/ci.yml)
provide the validation workflow, including real Lean/kernel/native gates. These
checks do not establish compiler correctness.

Covers:
- `req~intentbond-workflow~1`

`impl~github-tracking~1`

[Project configuration](../.github/project.json), [ticket helper](../scripts/tickets.py),
[task template](../.github/ISSUE_TEMPLATE/task.yml), and contribution guidance
support issue tracking. IntentMade's private deployment owns registration and
manual intake settings; repository checks cannot attest to their live state.

Covers:
- `req~github-tracking~1`

`impl~compiler-scope-contract~1`

The [feature matrix and constructor/surface inventories](architecture.md#feature-matrix),
[API contract](architecture.md#resolved-ir-api-and-cli-sequence),
[arithmetic policy](architecture.md#arithmetic-definedness-and-finite-observation),
and [intent](intent.md) are the planning deliverables. Their task ownership and
explicit deferred forms are review targets, not compiler test evidence.

Covers:
- `req~compiler-scope~1`

`impl~compiler-boundaries-contract~1`

The [ownership map](architecture.md#ownership-and-dependencies),
[assurance contract](architecture.md#independent-meanings-and-theorem-obligations),
[review handoff](architecture.md#review-handoff), [source register](sources.md)
and requirement reservation policy below implement the documentation obligation.
No Lean declaration or compiler theorem is claimed by these Markdown artifacts.

Covers:
- `req~compiler-boundaries~1`

## Reserved implementation requirements

`compiler-qualification` and `compiler-performance` are active requirements above.
The behavioral profile/trace planning IDs are active contract requirements above;
behavioral implementation requirements above retain their component boundaries.
New scope needs its own reviewed requirements and manual intake; this does not imply acceptance
of the qualification candidate.

The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) owns scheduling.
Upstream requirement IDs retain their upstream repository namespace; citing a
theorem or ticket does not import its coverage into this repository.
