# What the compiler experiment establishes

An independent mathematical semantics can guide an executable structural and
behavioral Clafer-to-Alloy compiler with machine-checked preservation proofs.
This project
provides a concrete implementation, explicit proof assumptions and comparisons
against real external tools. Its guarantees apply to the
[static](architecture.md#feature-matrix) and [behavioral](behavioral.md#complete-feature-and-evidence-matrix)
profiles, not every Haskell Clafer input.

## Key proved properties

Successful compilation means that the input was admitted and translated; it does
not mean that a satisfying model exists. The central guarantees connect the
in-memory source and target meanings: a satisfying target yields a source model,
and a source model with the required finite representation and bounds yields a
satisfying target. The entries below state which version of that claim is proved
at each stage.

The declaration links identify accepted compiler main
[`e8d0d3a`](https://github.com/kbak/clafer-compiler-lean/tree/e8d0d3a48ff073a0fe587cdd196b3159929f4063)
and its immutable Clafer Semantics dependency
[`f00e5da`](https://github.com/kbak/clafer-semantics/tree/f00e5dacb07eed51026f69fcf699683210d394d3).
The [source register](sources.md) owns the pins and accepted language corrections.
These are selected general theorems, not an inventory of every lemma or example;
the [qualification inventory](qualification.md#feature-and-evidence-inventory)
and [behavioral source inventory](behavioral-source.md#feature-and-evidence-inventory)
provide the detailed feature and test coverage.

### 1. Structural admission matches the independent source domain

The guarded M1 representation is admitted exactly when its interpretation is
well-formed and supported by Clafer Semantics, provided a suitable auxiliary
certificate is supplied. Admission preserves the entire input table and its
certificate. This prevents validation from silently repairing a declaration or
changing an identity. Admission does not require that the model be satisfiable.

In `ClaferCompiler.SemanticsBridge.Structural`, the proofs are
[`admission_iff`][admission] and [`validate_preserves`][admission-preserves].
The equivalence quantifies over certificates: incorrect supplied hierarchy ranks
can still fail. It covers the effective M1 core, not unrestricted source syntax,
JSON decoding, or authored defaulting. See the [IR contract](ir.md#proof-trace-and-assumptions).

### 2. Successful source elaboration follows declared rules

Successful static resolution obeys the independent name-binding and defaulting
rules, rather than merely producing a structurally valid table. Constraint
elaboration supplies a typed source derivation, preserves each original body
position, and gives the returned expression an independent source meaning,
including undefined results. This connects the backend's input to the model the
author wrote and prevents a repeated attachment from being silently dropped.

In `ClaferCompiler.SemanticsBridge.Resolution`, see
[`elaborate_correspondence`][resolution] and [`defaults`][defaults]; in
`ClaferCompiler.SemanticsBridge.Constraints`, see
[`denote_sound`][constraint-meaning] and [`attachments_preserved`][attachments].
These are success guarantees within the [selected static language](architecture.md#feature-matrix).
They neither prove that every valid document elaborates nor that every possible
declarative derivation has the same meaning. Typing does not make integer
extraction defined or prove absence of overflow. Grammar-to-parser correspondence
is outside this proof. See [resolution](resolution.md) and
[constraint elaboration](constraints.md#meaning-and-proof-boundary).

### 3. Structural translation preserves configurations in both directions

Every satisfying instance of a successfully compiled M1 target decodes to a
source configuration satisfying all structural obligations. The proof constructs
the representation and decoder success; neither is assumed. Conversely, every
finite satisfying source configuration that fits the stated scopes and numeric
capacities has a satisfying target produced by the concrete encoder. Objects,
containment and reference occurrences correspond: two bag-reference heads with
the same target remain two heads.

In `ClaferCompiler.Correctness.Structural`, the proofs are
[`compiled_sound`][structural-sound] and [`compiled_complete`][structural-complete].
Completeness requires a finite source carrier, successful compilation,
`ObservationScopesFit` for the exact/upper target scopes, and `SourceCountFits`
for the actual counts and emitted bounds at the selected signed bitwidth.
The latter is an explicit premise; there is no general theorem discharging it
from `safeBounds` alone. The domain is guarded M1, with the concrete object/extent/
tuple correspondence defined by `Represents`. See
[structural correctness](structural-correctness.md#kernel-checked-preservation).

### 4. Static expressions preserve undefinedness as well as values

For admitted static expressions, the target preserves definedness and every
defined Boolean, integer or collection result. In particular, negating an
undefined singleton extraction cannot turn it into a satisfied hard constraint.
An attached constraint holds exactly when its source body is defined and true
at every original owner. This matters for empty or multiple integer-reference
targets, quantifiers and inherited attachments, where truth alone is insufficient.

In `ClaferCompiler.Correctness.ExpressionMeaning`, see
[`admitted_full_agrees`][expressions] and [`encoded_body_iff`][body].
The premises include valid finite observations within the requested budgets,
the concrete object/map/scalar layout correspondence, related lexical environments
and an integer realization extending those observations. Successful source range
admission supplies intermediate representability; it does not supply singleton
extraction success. Whole primitive integer extents are excluded from finite
observation. Arithmetic uses mathematical integers whose observed values and
intermediates fit the signed bitwidth, not modular arithmetic. See
[expression preservation](expression-encoding.md#constructor-and-attachment-proofs)
and [source range analysis](expression-encoding.md#source-range-analysis-proofs).

### 5. The static source pipeline constructs one whole source model

A satisfying compiled source target yields one configuration satisfying both
the selected inherited structure and every original constraint body. Where
integers are present, that configuration realizes all mathematical integers;
the finite Alloy observations are not substituted for the whole integer domain.
The converse constructs a satisfying target from a fitting full source model.
This closes the gap between separate structural and expression proofs.

In `ClaferCompiler.Correctness.Pipeline`, see
[`source_sound`][source-sound], [`all_source_sound`][all-source-sound],
[`source_complete`][source-complete] and
[`constraint_free_complete`][constraint-free]. The theorems consume the actual
in-memory compiled `Driver.Source.Product`. Integer completeness requires
`SourceSat`, the concrete `Observes` equations and data-only `Fits`: original
nonprimitive heads/maps, finite injective labels, scalar identities and ranges,
table hygiene, scopes and count/object capacities. It uses the common `Atom`
universe and a supplied observation witness; arbitrary-carrier normalization is
not proved. The constraint-free branch has its own finite structural theorem.
See [composed source assurance](pipeline.md#composed-assurance).

### 6. Behavioral normalization retains lifetime and partial meanings

Executable signed normalization and lifetime lowering agree with the independent
source meaning. Parent cancellation, captured identities and the distinction
between a source's positive and negative signs survive translation. For partial
expressions, normalized truth is paired with the original formula's strict
definedness: normalization cannot discard an undefined operand just because a
Boolean truth calculation would not need it.

The first-slice theorem is
[`ClaferCompiler.SemanticsBridge.Behavioral.normalize_lower_agrees`][normalization].
For arbitrary partial observations, see
[`ClaferCompiler.SemanticsBridge.Behavioral.Generic.satisfies_iff_normalized`][partial-normalization].
Both require the stated traversal-size witness and retain the trace, environment,
time and source sign. The first uses the total set-observation fragment; the
second states original definedness explicitly. See
[behavioral interpretation](behavioral-ir.md#proof-handoff) and
[partial primitives](behavioral-frontend.md#partial-primitives-and-grouped-counting).

Resolved pattern, transition and modifier expansions also agree with their
accepted source meanings. In
`ClaferCompiler.SemanticsBridge.Behavioral.Surface`, see
[`Patterns.expand_agrees`][patterns], [`Transitions.expand_agrees`][transitions]
and [`Modifiers.expand_agrees`][modifiers]. The first covers the six patterns
in all five scopes; the second retains chain entry/continuation conditions.
Modifier agreement additionally requires upstream `Structural.Valid`, including
the inherited reference view. These are resolved reductions, not parser proofs;
see the [surface reduction contract](behavioral-frontend.md#executable-reductions-and-proved-boundary).

### 7. A behavioral trace keeps the same identities across time

For the narrower `behavioral-core/1` resolved profile, a satisfying compiled
target lasso yields a decoded source trace, its validity and every attachment.
A lasso is a finite sequence of stored states with a loop, interpreted over all
natural times. One global correspondence preserves the root, types, fixed
parents, live objects, reference heads, frames and loop; an object cannot be
renamed independently in each state. The concrete encoder also realizes fitting
valid source lassos as satisfying targets.

In `ClaferCompiler.Correctness.Behavioral`, see
[`compiled_sound`][trace-sound] and [`compiled_complete`][trace-complete].
Completeness requires successful compilation, sufficient formula fuel, unique
identity labels, duplicate-free reference rows, identity-pool/declaration scopes,
step limits, per-frame `SourceCountFits`, source validity and attachment truth.
Allocated but absent identities still consume pool capacity. These theorems do
not extend the resolved profile to the complete behavioral source language.
See [trace representation and correctness](behavioral-encoding.md#kernel-boundaries).

### 8. Full behavioral lowering preserves partial computations

The full expression pass preserves the original partial values, strict domain,
raw truth and both source signs. It covers the actual recursive lowering,
including grouped counting, captures, arithmetic and conditional branches.
This keeps an undefined source result distinct from a default target value and
preserves the meaning used by temporal constraints and property commands.

The proof is
[`ClaferCompiler.Correctness.Behavioral.Full.Expressions.lower_preserves`][full-lowering].
Its premises are successful checked lowering, sufficient fuel, `ModelRows`
for primitive observations and finite identity/range bounds, and `LexicalRows`
for the related captured environments. The successful range pass supplies
intermediate and fold-prefix range obligations; source truth is not a premise.
The full compiler's composition derives the observation premises from its
structural facts. See [full-profile proof components](behavioral-encoding.md#full-profile-proof-components).

### 9. Full model, assertion and scenario requests retain their meaning

For successful full compilation, a satisfying target produces checked decoding
and the corresponding source result on a trace completed with all integers.
A model request supplies a source model. A scenario request additionally satisfies
its extra attached constraints. An assertion check supplies a model counterexample
to the selected whole property. Assertion failure is classical negation of that
property, so undefinedness can be a counterexample; it is not strict source
negation.

In `ClaferCompiler.Correctness.Behavioral.Full`, see
[`compiled_sound`][full-sound] and [`sourceResult_request`][request].
The direct IR theorem requires the built-in integer declaration and its origin
proof. [`frontend_sound`][frontend-sound] composes successful authored-AST
elaboration and compilation, deriving primitive existence for a request whose
model equals the elaborated model. [`elaborate_source`][elaborate-source]
retains authored/header derivations; [`check_source`][check-source] and
[`run_source`][run-source] connect successful request construction to the
assertion index and ordered scenario bodies, owners and spans.

These results cover the explicit full behavioral profile with admitted bounds
and fuel. They start at authored ASTs or IR and independent in-memory target
satisfaction. A solver's returned bytes are not a theorem premise until they
have been related to that target meaning. See
[full encoding](behavioral-encoding.md#full-profile-proof-components) and the
[source workflow](behavioral-source.md).

### 10. Full behavioral completeness is relative to a finite observation

A satisfying source model, counterexample or scenario with the required finite
observation is represented by the concrete target encoder. The observation uses
one global embedding of ordinary identities and the source integer realization;
it preserves all live observations while allowing unused identities outside the
finite inventory. Thus the theorem can start with the original source carrier,
without replacing infinite integers with Alloy's finite integer universe.

The composed theorem is
[`ClaferCompiler.Correctness.Behavioral.Full.frontend_complete_observed`][frontend-complete].
It requires successful elaboration and compilation, the same elaborated request
model, primitive origin, source `SourceResult`, `ObservesCompletion` equations
and `Fits`. The latter bounds identity labels/capacity, scalar observations,
structural counts, exact/upper declaration scopes and stored lasso length.
Neither target truth nor a preservation equivalence is hidden in `Fits`.
The theorem does not construct a finite lasso for every infinite trace, and does
not imply unbounded completeness or unbounded UNSAT. See
[full completeness](behavioral-encoding.md#full-profile-proof-components).

### 11. Successful rendering reconstructs the checked target

Successful static and temporal rendering produces text that the repository's
reconstruction parser reads back as the same checked target module. This checks
that serialization has retained facts, identities, binders, command and scopes.
The proofs are
[`ClaferCompiler.Backend.Alloy.Text.render_reconstructs`][static-text] and
[`ClaferCompiler.Backend.Alloy.Temporal.Text.render_reconstructs`][temporal-text].
They assume a successful rendering call; total successful renderability and
correspondence of that parser with the external Alloy grammar/meaning are not
proved. See [static text](alloy-text.md#proved-boundary-and-review-obligation)
and [temporal text](alloy-temporal.md).

### Where these guarantees end

The declarations above are compiler-specific Lean theorems. Clafer Semantics
owns the independent source meanings and reusable semantic lemmas, including
structural admission, model correspondence and signed temporal laws. Those
upstream results do not themselves establish correctness of this Alloy compiler.
The [companion semantics guide task](https://github.com/kbak/clafer-semantics/issues/152)
tracks its curated list; until that guide is accepted, use the pinned
[semantic architecture](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/docs/architecture.md)
and [behavioral qualification](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/docs/behavioral-qualification.md).
Here, as upstream, *soundness* preserves satisfaction, *bounded completeness*
requires the stated representation/capacity conditions, and *definedness* is
separate from truth. Source signed negation need not be classical complementation
under lifetime cancellation.

| Evidence | What it establishes and what it does not |
| --- | --- |
| Lean kernel checking and axiom audit | The linked propositions follow under their actual premises and permitted logical axioms. They do not prove that every specification captures the intended language. |
| Parser, JSON and native execution tests | Exercise recognition, decoding and the compiled Lean/C runtime. No grammar-to-parser or verified native executable theorem is claimed. |
| External Alloy parsing and solving | Test emitted text against the pinned Analyzer; parsing, translation and SAT solving remain trusted external components. |
| Decoded-instance checks | Examine a particular finite observation. A decoder round trip establishes data correspondence, not source satisfaction. The full behavioral Python source observer is tested, not kernel certified. |
| Exact Lean/Haskell/Alloy comparisons | Supply bounded evidence for identical candidates within the recorded common profile. They do not establish unrestricted compiler equivalence, arbitrary infinite-trace representation or unbounded UNSAT. |

See the [execution boundary](architecture.md#serialized-text-and-execution-trust),
[comparison contract](comparison.md) and [qualification contracts](qualification.md)
for the corresponding trust and review obligations.

<a id="what-we-learned"></a>

## Established boundaries

**Component proofs need a compatible whole model.** Structural and expression
results must use compatible carriers, roots and primitive domains. Even `[0 = 0]`
requires a full integer realization under the pinned source semantics. The
[kernel counterexamples and carrier contract](pipeline.md#full-integer-carrier)
explain why a root-only carrier or a restricted primitive multiplicity cannot
support that model. The composed proof constructs one source configuration
satisfying both structural and constraint meanings.

**Finite solving needs a connection to infinite meanings.** Alloy represents
bounded observations; the source model realizes all mathematical integers.
[Source pipeline proofs](pipeline.md#composed-assurance) establish that completing
the observed carrier preserves admitted queries and constraints. Unsafe arithmetic
bounds are rejected. Completeness requires the concrete observation witness and
`Fits`; no arbitrary-carrier normalization theorem is claimed.

**Comparisons need identical questions.** Two translations can both be satisfiable
while allowing different instances. The [comparison harness](comparison.md) fixes
the same candidate and retains original objects, reference occurrences, scopes
and tool options. Mutations test whether missing constraints or altered relations
are detected. Haskell comparisons stay inside the common admitted domain;
defaulting differences are recorded explicitly.

**Proofs and execution tests cover different boundaries.** Kernel replay checks
the stated Lean declarations. Parser, native binary, serialized Alloy and Analyzer
tests exercise components outside those proofs. Traceability and source-bound
evidence make the claims reviewable; they do not establish that the requirements
are complete or the proofs state the right properties.

## Comparison with the Haskell compiler

| Dimension | Supported conclusion |
| --- | --- |
| Semantic assurance | This project supplies kernel-checked admission, elaboration and preservation results against independent meanings, with explicit assumptions. The inspected Haskell reference pipeline does not supply an equivalent proof chain. This does not measure overall defect rates. |
| Executable correctness | Parser recognition, JSON decoding correspondence, generated native code, emitted-text interpretation and solving remain tested boundaries. No end-to-end verified executable claim follows. |
| Language coverage | Haskell supports a wider language. This compiler keeps the static and behavioral profiles explicit, including their different inheritance/arithmetic admission and documented source-policy departures. |
| Performance | Measurements apply to the recorded candidate, input corpus and host. The [benchmark method](qualification.md#measurements-and-replay) separates compiler costs from solving; the [native optimization measurements](https://github.com/kbak/clafer-compiler-lean/issues/50) retain results and their source identities. |
| Reliability in use | Field defect rates, long-term maintenance costs, adversarial robustness and user outcomes have not been measured. |

<a id="use-for-other-projects"></a>

## Reuse and alternative implementations

Researchers can reuse the source/target relations, finite-observation construction
and nonvacuous counterexamples. Compiler developers can use the executable
implementation and exact-candidate corpus as references for regression testing.

A faster implementation in Lean or another language can use this compiler as an
executable reference and Clafer Semantics as the mathematical specification.
Matching test results provides comparison evidence. To inherit a preservation
claim, the replacement needs a proof connecting its behavior to the verified
translation or directly to the independent source and target meanings.

Within Lean, this project uses kernel-proved function equalities for cached indices,
shared rendering and early fixed-point termination. These replacements retain
the existing preservation proofs; native tests and benchmarks still check execution
and cost. The [build contract](build.md) describes that boundary.

The compiler source is available under MIT. Reuse remains subject to the
documented scope and dependency licenses.

[admission]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Structural.lean#L117
[admission-preserves]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Structural.lean#L90
[resolution]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Resolution.lean#L32
[defaults]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Resolution.lean#L97
[constraint-meaning]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Constraints.lean#L28
[attachments]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Constraints.lean#L80
[structural-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/StructuralReferences.lean#L151
[structural-complete]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/StructuralCorrectness.lean#L65
[expressions]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/ExpressionPreservation.lean#L271
[body]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/ExpressionAttachments.lean#L196
[source-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/PipelineSourceSatisfaction.lean#L49
[all-source-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/PipelinePresence.lean#L53
[source-complete]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/PipelineCompleteness.lean#L42
[constraint-free]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/PipelinePresence.lean#L73
[normalization]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Behavioral/Syntax.lean#L94
[partial-normalization]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Behavioral/Formula.lean#L52
[patterns]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Behavioral/Surface.lean#L39
[transitions]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Behavioral/Surface.lean#L109
[modifiers]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/SemanticsBridge/Behavioral/Surface.lean#L151
[trace-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Correctness.lean#L36
[trace-complete]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Completion.lean#L17
[full-lowering]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/ExpressionsCorrectness.lean#L64
[full-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/CompilerCorrectness.lean#L122
[request]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/CompilerMeaning.lean#L46
[frontend-sound]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/FrontendCorrectness.lean#L14
[elaborate-source]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/FrontendElaboration.lean#L46
[check-source]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/FrontendElaboration.lean#L88
[run-source]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/FrontendElaboration.lean#L129
[frontend-complete]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Correctness/Behavioral/Full/FrontendCorrectness.lean#L54
[static-text]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Backend/Alloy/Print.lean#L164
[temporal-text]: https://github.com/kbak/clafer-compiler-lean/blob/e8d0d3a48ff073a0fe587cdd196b3159929f4063/ClaferCompiler/Backend/Alloy/Temporal/Print.lean#L122
