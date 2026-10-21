# Structural representation and preservation work

[Issue #11](https://github.com/kbak/clafer-compiler-lean/issues/11) is selected after
acceptance of the [structural backend](structural-encoding.md) in PR #28. This is
an incomplete implementation of that issue. The current artifacts establish the
finite representation and successful decoding of satisfying target instances.
They do **not** prove source satisfaction or bounded completeness. Issue #11 was closed with merged PR #29, but
its global correctness requirement remains outstanding; none of these lemmas substitutes
for the two preservation directions in the [architecture](architecture.md).

## Reuse assessment

The representation reuses #10's `order`, `signatureId`, `fieldKeys`, `fieldId`,
`schema` and generation/inventory theorems, and #8's `Instance`, `wellFormed`,
`declarations`, `Satisfies` and evaluators. It introduces no second target evaluator.
Pinned upstream `Configuration` and `Configuration.rename` supply source data and
renaming directly. Upstream `Verification.Candidate` and its noncomputable
`encode` use canonical `Fin` labels and belong to the proof dependency; importing
them into the native runtime would violate the existing import boundary and would
not preserve raw target label/list order. They remain candidates for the later
finite-source completeness composition, not a reason to duplicate source meaning.

Lean `List` operations, `Option`/`Except`, and Mathlib `Equiv`, `Fintype.ofFinset`
and `Fintype.card_ofFinset` provide the machinery. The new proofs supply the
missing stack-composition lemmas for the existing postfix algebras and injective
`eraseDups` mapping; they reuse the library's membership, filter, sort and index
lemmas. #9 already owns parsing/printing, so no parser or external decoding package
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
bounds remain #10's checked compilation inputs. This stage makes no theorem about
source configurations fitting those bounds.

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

## Remaining issue #11 obligations

The reservation `compiler-structural-correctness` is not adopted as a delivered
requirement by this stage. Remaining work includes:

1. Derive every upstream `StructuralSatisfies` conjunct from generated target
   satisfaction: root freshness/whole-carrier coverage, ancestry/disjointness,
   abstract cover, typed relations, ownership, reference functionality, keys,
   local intervals and group unions. Root existence and target-side atom coverage
   alone do not establish these clauses.
2. Construct target models from arbitrary admitted finite source configurations,
   with exact manual scope, representation and integer-count/bitwidth hypotheses
   independent of satisfaction. Prove bounded completeness; do not interpret
   bounded absence as unbounded UNSAT.
3. Compose both directions with the pinned effective-core/local compiled-bank
   theorems while retaining their actual whole-model global hypotheses.
4. Add theorem-level sensitivities for omitted upper bounds, collapsed bag
   occurrences and missing global facts. Existing native omission tests and the
   missing-owner witness do not complete that acceptance criterion.

No scope, admission domain, coverage floor, source pin or proof audit is weakened.
IntentBond exit 4 leaves semantic review pending, and this partial delivery does
not establish the remaining acceptance criteria of #11. The maintainer selected
#12 after merging PR #29; it uses this representation API while preserving the
missing-proof obligations. No selection of #13 is implied.
