# Structural representation and preservation work

[Issue #11](https://github.com/kbak/clafer-compiler-lean/issues/11) is selected after
acceptance of the [structural backend](structural-encoding.md) in PR #28. PR #29
supplied finite representation and decoding but left preservation unfinished.
This follow-up proves M1 soundness and bounded completeness against the independent
source and target meanings. The maintainer accepted these proofs through
PR #33 at `67b9137cde9e2b486733aecd6eb4f5559b780ea3`, authorizing #13.
The [inherited extension](inherited-realization.md) reuses the proved allocation
lemmas through `Structural.Layout`; the M1 entry points retain their support guards.

The result covers exactly the admitted M1 effective core. Completeness constructs
a target for any finite satisfying source whose observation fits the manual scopes
and signed integer ranges below. Native execution, Analyzer output decoding and
serialized target correspondence retain their separate boundaries.

## Reuse assessment

The representation reuses #10's `order`, `signatureId`, `fieldKeys`, `fieldId`,
`schema` and generation/inventory theorems, and #8's `Instance`, `wellFormed`,
`declarations`, `Satisfies` and evaluators. It introduces no second target evaluator.
Pinned upstream `Configuration` and `Configuration.rename` supply source data and
renaming directly. Upstream `Verification.Candidate` and its noncomputable
`encode` use canonical `Fin` labels and belong to the proof dependency; importing
them into the native runtime would violate the existing import boundary and would
not preserve raw target label/list order. The proof-only `sourceObservation` instead enumerates the original arbitrary finite
`Configuration` directly through `Fintype.equivFin`; it preserves its whole carrier
and exact role relations without requiring a prior finite `Candidate` encoding.

Lean `List` operations, `Option`/`Except`, and Mathlib `Equiv`, `Fintype.ofFinset`
and `Fintype.card_ofFinset` provide the machinery. The new proofs supply the
missing stack-composition lemmas for the existing postfix algebras and injective
`eraseDups` mapping; they reuse the library's membership, filter, sort and index
lemmas. `Relation.ReflTransGen.total_of_right_unique` establishes comparability
of occupied signature paths; it avoids a second custom forest theory.
`DPGraph.Predicates.inRange_card` supplies finite multiplicity equivalence.
Pinned `Configuration.structural_model_iff`, `erasure_correspondence` and
`SpanModel.normalize_satisfies` provide the bank/erasure/span compositions.
The compiler-specific gap is the correspondence from the accepted generated target
layout to those existing source meanings. #9 already owns parsing/printing, so no parser or external decoding package
is added. All reused dependencies retain their pinned revisions/licenses; this
stage adds no package or native runtime dependency.

## Executable finite presentation

`impl~compiler-structural-representation~1`

[StructuralRepresentation.lean](../ClaferCompiler/Backend/Alloy/StructuralRepresentation.lean)
defines `Backend.Alloy.Structural.Observation`, `encode`, `observation`,
`readPairs`, `DecodeError` and `decode`.

An observation records the ordered live object labels, distinguished root label,
each declaration's extent, and owner/head and head/target tuple lists. These are
data; no source or target truth is stored. Encoding uses #10's signature and field
allocation. It introduces no auxiliary atom and does not collapse reference heads.
Ordinary link identity is its tuple; composite owner/target links retain their
intermediate head. Two bag occurrences with equal owner and target stay distinct.

Decoding rejects malformed target tables, a nonsingleton root, and a root absent
from the object union. It retains well-formed semantic violations and does not
call the upstream checker. Nonroot atoms outside the union also remain in the raw
observation; they are excluded from its semantic carrier. Such inputs cannot have
the full `Represents` relation because its explicit `Live` condition forbids them.
The theorem below derives `Live` from target satisfaction, rather than assuming it.
All unused allocation slots are absent from the carrier. A live but uncovered
object is retained for eventual source coverage rejection, not silently removed.

This API consumes in-memory target tables. Parsing Analyzer output remains #12;
text serialization, IR CLI integration, and external runtime trust retain their
separate boundaries. The pure encoder does not perform bounds admission. Manual
bounds remain #10's checked compilation inputs. The completeness theorem below
requires the source observation to fit them; it does not infer bounds.

Covers:
- `req~compiler-structural-representation~1`

## Kernel-checked representation results

`proof~compiler-structural-representation~1`

The declarations are in `ClaferCompiler.Correctness.Structural`:

- [StructuralRepresentation.lean](../ClaferCompiler/Correctness/StructuralRepresentation.lean)
  defines `Objects`, `objectsFintype`, `realize`, `Live`, `Represents` and
  `TableWellFormed`. `objects_card` counts the distinct live labels.
  `Objects` is precisely the subtype of labels in the object union. `Represents`
  carries a bijection from source objects to that carrier, the root singleton,
  exact extent and active-role tuple equations, target table well-formedness, and
  `Live`. Together these
  equations account for every target extent/tuple atom; no source truth appears.
  `Represents.rename` transports those equations through an arbitrary source
  object bijection. The independent upstream configuration is used directly.
- `encode_objects`, `encode_heads`, `encode_field`, `encode_dereference`,
  `mem_readPairs` and `readPairs_map` establish data lookup and occurrence identity.
  `observation_encode` requires only empty inactive relation slots.
  `encode_wellFormed` requires duplicate-free tables and empty inactive slots.
  `decode_encode` additionally requires the chosen root singleton and membership
  in the object union. It applies to violating as well as satisfying candidates.
- [StructuralDecoding.lean](../ClaferCompiler/Correctness/StructuralDecoding.lean)
  proves `satisfying_root`, `satisfying_decode`, `satisfying_live`,
  `compiled_decode` and `compiled_representation`. The last theorem takes a
  successful actual `compile` result and independent `Satisfies`; it constructs
  the executable decoder output, root-membership proof and concrete `Represents`
  witness. It assumes neither source satisfaction nor a supplied representation.
  `declarations_live` derives full atom coverage using the checked finite extends
  forest, inclusion, and typed field endpoints.
- [AlloyEvaluation.lean](../ClaferCompiler/Correctness/AlloyEvaluation.lean) supplies
  postfix construction/stack laws, strict conjunction and quantification laws,
  duplicate elimination lemmas and `Module.fact_true`. These laws establish
  evaluation facts; they do not redefine either satisfaction relation.

Covers:
- `req~compiler-structural-representation~1`

## Tests and nonvacuity

`utest~compiler-structural-representation~1`

[Kernel witnesses](../tests/StructuralRepresentation.lean) establish satisfaction
of a generated bag target with two distinct heads sharing a target, its complete
representation, and its encode/decode round trip. A missing-owner mutation both
violates the ownership fact and still round-trips, so decoding cannot be confused
with a semantic checker. These are concrete witnesses, not general preservation.

[Native fixtures](../tests/StructuralRepresentationNative.lean) replay the existing
39-case structural corpus. The 36 decodable cases each round-trip with their
original labels and with injectively renamed, nonconsecutive labels (72 round
trips). Missing/multiple/zero-scope roots and six additional malformed or
out-of-carrier-root inputs are rejected. Semantic negative cases retain every
tuple. An additional dangling-tuple round trip retains an out-of-carrier referent
for later rejection. Explicit bag assertions preserve both occurrences at their
common target.
The [Python runner](../tests/test_structural_representation.py) links and executes
the real native implementation, keeping Lean/C execution distinct from kernel
proofs. Existing upstream finite comparisons and real external oracle gates remain
mandatory and unchanged.

Covers:
- `req~compiler-structural-representation~1`

## Finite source construction

`impl~compiler-structural-correctness~1`

[StructuralSourceObservation.lean](../ClaferCompiler/Correctness/StructuralSourceObservation.lean)
defines the noncomputable proof-only `sourceObservation` and `sourceObjects`.
An injective `Fintype.equivFin` labelling enumerates every original object, each
head extent and every containment/dereference pair. `source_represents` proves
the exact representation from source typing and root singleton data. It does not
assume target satisfaction. All ordinary relation tuples are retained, and bag
reference heads remain distinct even with equal owners and targets. This supplies
existence for the proof, not a new executable source enumerator. The runtime
compiler, encoding, decoding and admission domain are unchanged.

Covers:
- `req~compiler-structural-correctness~1`

## Kernel-checked preservation

`proof~compiler-structural-correctness~1`

The public entry points are in `ClaferCompiler.Correctness.Structural`, exported
through [Correctness](../ClaferCompiler/Correctness.lean):

- `compiled_sound` in
  [StructuralReferences.lean](../ClaferCompiler/Correctness/StructuralReferences.lean)
  takes the actual equation `compile v b = .ok c` and independent target
  `Satisfies c.module.raw i`. It constructs the successful decoder output, root
  membership, a concrete `Represents` witness, and full upstream
  `StructuralSatisfies`. Source truth, decoder success, a preconstructed source
  and a supplied preservation equivalence are absent from its hypotheses.
- `compiled_complete` in
  [StructuralCorrectness.lean](../ClaferCompiler/Correctness/StructuralCorrectness.lean)
  takes an arbitrary `Configuration (Fin n) U` with `Fintype U`, actual compilation
  success, independent source `StructuralSatisfies`, `ObservationScopesFit` and
  `SourceCountFits`. Its witness is exactly `encode v (sourceObservation s)` with
  a concrete representation and independent target satisfaction.
- `compiled_sound_bank` uses upstream `structural_model_iff` to retain source
  `Typed`, all `GlobalConditions` and the independent local compiled-bank model.
  `compiled_complete_bank` accepts the actual constraint-free AST `Compile.Input`
  and `SatisfiesAST`, together with an effective-core erasure *data equality*;
  it uses upstream `erasure_correspondence`. `normalized_complete` applies
  `SpanModel.normalize_satisfies` to arbitrary original span/link carriers,
  preserving its local model and explicit normalized global premises. Finiteness
  is local to the concrete model carrier; DPGraph universes remain unrestricted.

`ObservationScopesFit` compares each explicit exact/upper scope with the object
or head count in generated declaration order. `source_object_count` and
`source_head_count` identify those lengths with the original finite carrier and
extent cardinalities. Compilation separately checks the complete scope inventory.
`SourceCountFits` in
[StructuralCompletionFacts.lean](../ClaferCompiler/Correctness/StructuralCompletionFacts.lean)
checks only numeric representability for actual local/group fibers at actual
quantifier environments. Its `IntervalFits` condition requires every count and
nontrivial bound observed by a generated comparison to fit signed bitwidth;
`0..*` emits no integer observation. These hypotheses contain neither source nor
target truth and are not a substituted preservation obligation. Safe range
admission remains checked and tested independently; no general theorem that
`safeBounds` implies these numeric hypotheses is claimed.

The proof decomposition accounts for every source clause and target obligation:

| Proof module | Obligation |
| --- | --- |
| [StructuralHierarchy](../ClaferCompiler/Correctness/StructuralHierarchy.lean) | Global source declaration disjointness from occupied target paths and sibling disjointness |
| [StructuralSatisfaction](../ClaferCompiler/Correctness/StructuralSatisfaction.lean) | Typed role endpoints, inheritance, abstract cover, root freshness and whole-carrier coverage |
| [StructuralRelations](../ClaferCompiler/Correctness/StructuralRelations.lean) | Concrete role fibers and injective tuple cardinalities |
| [StructuralCardinality](../ClaferCompiler/Correctness/StructuralCardinality.lean) | Ownership, local intervals and union-of-child-head group counts |
| [StructuralReferences](../ClaferCompiler/Correctness/StructuralReferences.lean) | Reference functionality, set keys and assembled soundness |
| [StructuralCompletionFacts](../ClaferCompiler/Correctness/StructuralCompletionFacts.lean) | Every generated fact from source truth and numeric observation ranges |
| [StructuralCompletionDeclarations](../ClaferCompiler/Correctness/StructuralCompletionDeclarations.lean) | Signature inclusion/cover/disjointness and field typing/multiplicity from source truth |

These are in-memory mathematical preservation theorems. They do not prove Lean/C
execution, external Analyzer behavior, serialization semantics or unbounded UNSAT.
No extra axiom, proof placeholder, scope amendment or dependency upgrade is used.

Covers:
- `req~compiler-structural-correctness~1`

## Preservation witnesses and sensitivity

`utest~compiler-structural-correctness~1`

[StructuralCorrectness.lean](../tests/StructuralCorrectness.lean) kernel-checks
successful actual compilation of the nontrivial bag fixture, decoded source
satisfaction and canonical finite-source completeness. It also applies soundness
after bijective relabelling. The fixture contains two distinct reference heads
with the same owner and target.

Two counterexamples remove one generated fact at a time: omitting a child's
upper bound admits two children against `0..1`; omitting a leaf abstract's cover
admits an inhabitant with no concrete subtype. Each mutated target is independently
proved satisfying, and its realized source is proved violating. A third witness
shows that collapsing a repeated bag occurrence cannot represent the original
source because the required object bijection would equate different cardinalities.
The production generator is not mutated. Existing native finite representation
and Haskell/Lean/Alloy comparison gates remain mandatory.

Covers:
- `req~compiler-structural-correctness~1`

## Review and dependent handoff

The #11 preservation obligations, including compiled bank/erasure/span composition
and theorem-level sensitivities, were accepted by the maintainer through PR #33
at `67b9137cde9e2b486733aecd6eb4f5559b780ea3`. The retained full-check evidence
and that explicit review, rather than IntentBond exit 4 alone, support the handoff.

The [comparison layer](comparison.md) owns generated-text/external instance
comparison and integration. The inherited extension adds ordinary inherited
fields, explicit abstract families and the Appendix 6 structural skeleton through
a separate checked API. Its [contract](inherited-realization.md) states the primitive/domain/context limits. No scope,
admission domain, coverage floor, source pin or review gate is weakened here.
