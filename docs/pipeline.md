# Source pipeline integration

The source pipeline composes the parser, declaration resolver, constraint
elaborator and Alloy backend. Its proofs connect the generated target to a full
source model, including mathematical integers, under explicit observation bounds.
The M1 resolved-IR API and its comparison domain remain available separately.

## Reuse assessment

The source command composes the existing Parsec parser, checked source resolver,
constraint elaborator, inherited backend, expression attachments and checked
Alloy renderer. The existing strict JSON decoder, diagnostic serializer, atomic
output writer and native/external test harness supply the driver machinery.
No alternative CLI framework or new dependency is needed; see [CLI reuse](cli.md#reuse-assessment).

For assurance, the accepted inherited representation and preservation proofs
supply finite configuration reconstruction. Expression constructor and attachment
proofs supply partial denotation preservation once the actual object/map/scalar
representation is derived. They do not themselves establish that representation
or a full structural integer model. The pinned `ConstraintMeaning.whole_model`
requires actual primitive domains and root/structural obligations, so it cannot
be applied to a truncated integer carrier. The pinned complete telematics
`Input`, `Configuration`, `Satisfaction` and `Compiled` modules provide independent
inventory, full-domain and nonvacuity evidence. The guarded M1 evaluator cannot
check this larger domain.

Mathlib `Equiv.Perm.exists_extending_pair` extends finite injective label maps to
an ambient permutation. Together with existing finite-set and representation
lemmas it avoids custom infinite atom-allocation machinery when constructing the
expression layout relation. Proof-only noncomputability must stay out of the
native compiler. Imported upstream semantics remains MIT; Mathlib and Lean
runtime/Parsec remain Apache-2.0. New downstream code is original MIT with no
new dependency or license cost. The pinned Haskell grammar, desugarer and Alloy
generator remain syntax/compatibility references, never the source truth oracle.

For full primitive composition, the pinned semantics supplies only same-carrier
expression congruence and finite structural renaming by bijections. It has no
generic primitive-domain completion theorem. Mathlib's countable-equivalence
construction and finite permutation extension can complete the integer carrier
while fixing every observed value. This is proof-only existence machinery, not
a native allocator. The domain and query-agreement proofs state
which map reads stay finite and do not equate infinite containment with its
finite observation.

The extended inherited candidate checker reuses the upstream finite semantic
clauses and finite-cardinality theorem, adds the independent inherited group
predicate, and proves its own correctness theorem. It does not call the guarded
M1 `check`. Reimplementing those finite predicates or widening that public guard
would add unnecessary proof and runtime machinery.

## Integration obligations

1. Preserve original declaration IDs, source spans and every constraint occurrence
   through the source-to-inherited/attachment handoff.
2. Decode a closed `clafer-bounds/2` document with explicit nonprimitive budget,
   per-original-ID scopes, signed bitwidth and per-primitive value intervals.
   No solver or Haskell process runs during compilation.
3. Reconstruct observed scalar identity from generated totality, injectivity and
   range facts, and derive concrete expression layout relations from decoded
   structural maps. Do not assume a correct representation or final source truth.
4. Extend only the primitive domain and its root containment to mathematical
   integers; preserve finite nonprimitive extents, original reference occurrences
   and every admitted expression's denotation. Synthetic primitive multiplicity
   must be unrestricted, matching the pinned full model. Primitive containment
   is infinite in the full model. Its finite observation must preserve admitted
   queries such as parent navigation from an observed integer, without claiming
   equality of the entire finite and infinite maps or dropping accepted syntax.
5. Compose soundness and bounded completeness at the independently established
   source boundary. Keep parser recognition, text/Analyzer correspondence,
   native execution and solver trust explicit.
6. Exercise all Appendix 6 bodies and selections, distinct scalar values and
   focused negative mutations. Any extended candidate evaluator needs its own
   justification; the M1 checker remains guarded.

<a id="carrier-decision-exposed-by-composition"></a>

## Full integer carrier

Every constraint-bearing source document receives an implicit unrestricted integer
declaration, including documents without integer references. Authored IDs remain
unchanged; the implicit declaration is appended. Its finite observation scope may
be zero when unused, while its source domain contains all mathematical integers.
Source bounds must name this ID and its interval explicitly. Constraint-free
source resolution adds it only when an integer reference requires it.

This rule is necessary even for `[0 = 0]`. A root-only structural configuration
has a singleton carrier by `Rooted`, while `IntegerBinding` requires an injective
realization of all integers in that carrier. The kernel theorem
`Tests.PipelineLimits.root_only_no_integer_realization` proves the contradiction
using 0 and 1. Separate structural and expression theorems cannot establish a
whole-model result without a compatible carrier. Likewise, a restricted synthetic
primitive multiplicity would conflict with the full integer domain.

The [integer-carrier review](https://github.com/kbak/clafer-compiler-lean/pull/44)
records this choice. The counterexample remains a regression against incomplete
elaboration; upstream meanings and the guarded M1 API are unchanged.

## Composed assurance

`Pipeline.source_sound` constructs a single rooted selected source configuration,
its realization of all mathematical integers, and satisfaction of every original
body on its full owner head. `all_source_sound` also covers the constraint-free,
no-primitive case. Successful elaboration proves that every authored constraint
has the primitive carrier needed by `IntegerBinding` (`body_has_primitive`).

The chain derives scalar identity from generated totality/range/injectivity facts,
decodes original tables, constructs their atom embedding, and completes the
primitive head and its root containment. `completed_structure` proves every
upstream structural clause, including inherited groups and global disjointness.
`elaborated_navigation` derives query locality from the existing elaboration
rules. `query_agreement` preserves partial denotation on the completed model;
it covers primitive-parent navigation and quantifiers without equating an
infinite map with a finite table. Full support spans retain original head/link
identity and use actual composite link pairs for target roles. `source_body_meaning`
connects the unchanged typed terms to the independently stated source rules.

`Pipeline.source_complete` starts with `SourceSat` and data-only `Fits` and
constructs `encodeObservation`, proves its decoding and target satisfaction.
`restricted_structure` derives the finite structural model from full satisfaction;
finite source satisfaction is not hidden in `Fits`. The observation relation
uses the common `Atom` universe, an injective finite labeling, exact nonprimitive
heads/maps, observed scalar values fixed by the integer realization, and primitive
root containment. Completeness is for source models with this concrete observation
witness; it does not claim a separately proved normalization theorem from every
arbitrary carrier. `FiniteFits` adds table hygiene/live labels, original exact or
upper scopes, count capacities, total functional scalar rows, range/identity data,
and the nonprimitive object budget. It contains no target satisfaction, authored
constraint truth or preservation equivalence. `constraint_free_complete` handles
the finite structural branch. This implements the finite-observation theorem
shape in the architecture contract rather than bounding mathematical integers.

The lower-level `candidate_constraint_iff` and `candidate_complete` deliberately
remain candidate lemmas. Their structural/numeric premises are discharged by the
composed theorems. In particular, `ObservationFacts.structural` alone would be an
inappropriate premise for a source-based completeness claim.

Parser recognition, strict JSON correspondence, native execution, emitted-text
interpretation by Alloy, and the solver are tested boundaries. The in-memory
Lean proofs do not certify those external components. No public M1 checker guard
is widened. The [qualification inventory](qualification.md) retains these limits.

## Complete example and exact replay

The committed Appendix 6 source contains all twelve bodies and all three final
selections. Its explicit bounds have 36 nonprimitive objects, width 7, and two
observed integer values in [2,3]. The declared integer capacity is not the size of
its full source domain. The external suite solves that complete source, records
all original owner/body identities, decodes the XML without guessing atom names,
and fixes every extent, original field and scalar row for exact Analyzer replay.

The inherited checker separately evaluates the pinned finite semantic predicates
and has a kernel `Verification.Inherited.check_correct` theorem. Per-body native
formula evaluation is justified by `candidate_constraint_iff` under independently
checked inherited/numeric data. It is not an executable checker of infinite sets.
The suite compares this justified observation boundary with the emitted target AST
and actual pinned Analyzer. Haskell's M1 checker is not a fourth or widened oracle.

Focused standalone witnesses flip version ordering, display counts and parent
navigation; other mutations omit a body or inherited group fact. Each replay
retains source, bounds, complete candidate tables, scalar payloads, generated text,
source/runtime hashes, commands and Analyzer results. For the fixed exact bounds,
every single-object deletion is checked against an original exact declaration
scope and ruled out. This establishes object-deletion minimality for those bounds,
not a global minimum, arbitrary row minimality, or source-syntax minimality.

The mandatory source tests run in a separate process alongside the existing M1
comparison/CLI worker and remaining regressions. The existing unittest/subprocess
runner supplies process isolation; failure, skipped, missing and empty groups
remain failures. The [build contract](build.md) records the full validation scope
and execution deadline.

## Traceable implementation and proof artifacts

`impl~compiler-source-pipeline~1`

[Frontend handoff](../ClaferCompiler/Frontend/Pipeline.lean) retains the checked
AST, resolved certificate and attachment derivations. The [source driver](../ClaferCompiler/Driver/Source.lean)
checks version-2 bounds and constructs the actual checked module;
[command integration](../ClaferCompiler/Driver.lean) retains diagnostics and atomic
output. [Source observations](../ClaferCompiler/Backend/Alloy/SourceObservation.lean)
retain every original map occurrence and scalar value. The
[extended checker](../ClaferCompiler/SemanticsBridge/InheritedChecker.lean) directly
reuses the pinned finite predicates with inherited groups. The
[complete example](../tests/fixtures/constraints/telematics.cfr) and
[explicit bounds](../tests/fixtures/pipeline/telematics.bounds.json) exercise this
same production pipeline.

Covers:
- `req~compiler-pipeline-correctness~1`
- `req~compiler-telematics~1`

`proof~compiler-source-pipeline~1`

[Construction](../ClaferCompiler/Correctness/PipelineConstruction.lean),
[scalar facts](../ClaferCompiler/Correctness/PipelineScalars.lean),
[layout correspondence](../ClaferCompiler/Correctness/PipelineLayout.lean),
[observation validity](../ClaferCompiler/Correctness/PipelineObservation.lean),
[bounds](../ClaferCompiler/Correctness/PipelineBounds.lean) and
[body correspondence](../ClaferCompiler/Correctness/PipelineConstraints.lean)
derive the accepted constructor/attachment theorem premises from target data.

[Integer completion](../ClaferCompiler/Correctness/PipelineIntegers.lean),
[full structural completion](../ClaferCompiler/Correctness/PipelineCompletion.lean),
[restriction](../ClaferCompiler/Correctness/PipelineRestriction.lean),
[full binding](../ClaferCompiler/Correctness/PipelineFullBinding.lean),
[navigation](../ClaferCompiler/Correctness/PipelineNavigation.lean) and
[query agreement](../ClaferCompiler/Correctness/PipelineQueryAgreement.lean)
connect that observation to one full source model.
[Source satisfaction](../ClaferCompiler/Correctness/PipelineSourceSatisfaction.lean),
[completeness](../ClaferCompiler/Correctness/PipelineCompleteness.lean) and
[the no-primitive branch](../ClaferCompiler/Correctness/PipelinePresence.lean)
state the composed results and their exact hypotheses. All auxiliary project
declarations are discovered and kernel/axiom-audited by the mandatory build.

Covers:
- `req~compiler-pipeline-correctness~1`

`utest~compiler-source-pipeline~1`

[Source CLI tests](../tests/test_source_cli.py) check bounds, spans, deterministic
output and fail-before-write behavior. [Runtime isolation](../tests/test_cli_external.py)
executes the linked source command without development tools. The
[exact candidate suite](../tests/test_source_pipeline.py) checks numeric `1..1`
groups with two unannotated children: either choice satisfies native evaluation,
the independent structural checker and generated Alloy, while zero/both violate
them under matching exact scopes. The suite uses the
[Lean harness](../tests/PipelineNative.lean), all twelve original attachments,
independent inherited checks and actual pinned Analyzer replay. The
[kernel counterexamples](../tests/PipelineLimits.lean) preserve the reason finite
or root-only carriers cannot stand for a full integer realization.

Covers:
- `req~compiler-pipeline-correctness~1`
- `req~compiler-telematics~1`
- `req~compiler-defaults~1`

Generic atom completion, source navigation shape and full support spans are
independent of decoded target bounds and final source satisfaction. Their module
imports allow Lean to check these lemmas concurrently.

External suites use a private Java bridge build directory per invocation, sharing
only the hash-checked JAR/JDK. This prevents concurrent compilation from replacing
classes while another JVM loads them. The bridge identity checks remain mandatory.
