# Aggregate abstract multiplicity

Select `behavioral-abstract-multiplicity/1` in the behavioral bounds document.
It extends `behavioral-rich-core/1` with the accepted upstream
[abstract multiplicity contract](https://github.com/kbak/clafer-semantics/blob/6093ed5ac584ddc5d110c094e3da914897725d6b/docs/abstract-multiplicity.md).
Historical behavioral profiles and the static `compile-source`/M1 normalization
retain their existing meanings. Models without temporal syntax use the same
extended source workflow; the generated obligations still hold at every state.

## Source meaning and representation

An authored bound on a top-level abstract declaration constrains its entire
inherited head set, across all concrete subtypes and actual parents. For example,
`abstract Tools 3..6` permits sibling realizations contributing one and two heads,
but rejects four plus four. The bounds are not individually inherited by each
subtype, and heads along an inheritance chain are counted once. Reference heads
are counted independently of their targets.

A nested abstract declaration constrains its children separately for each live
instance of its declared parent, including instances through parent inheritance.
An absent parent contributes no obligation. Both endpoints apply at every state;
initial satisfaction alone is insufficient. Omitted bounds mean `0..*` while
remaining distinguishable from an authored `*`, `0`, or finite interval.

`Frontend.BehavioralResolution.SourceRow` retains the authored interval and
normalizes the effective local slot of an explicitly abstract declaration to
`0..*` in this profile. Invalid intervals remain admission errors. Ordinary
concrete bounds and group bounds keep their existing meanings. Effective
optimizer zeroing of a parentless abstract slot cannot replace or erase its
authored aggregate constraint. There is no subtype interval-refinement rule,
naive sum-of-local-bounds feasibility check, inferred scope cap or automatic scope
increase. Explicit identity scopes are search limits, not source constraints.

`Frontend.Behavioral.AbstractMultiplicity.generate` emits ordinary cardinality
comparisons for each authored abstract declaration. Global comparisons attach to
the permanent root and count `.extent`; nested comparisons attach to the declared
parent and count `.child`. The existing attachment semantics quantifies over live
owners at every time. No synthetic parent edge is added to an abstract type.
The constraints enter the common model before Alloy compilation or rich/core
export. Imported core preserves them even when all optional authored metadata is
removed. Rich replay re-elaborates and checks the entire lowered model.
Explicit core v2 carries aggregate and finality constraints together, with no
modifier table. Legacy v1 rich/core imports retain the selected profile and
migrate to v2 using the shared modifier lowering. Combined exact candidates
check stable populations, identity swaps and both aggregate endpoints.

The existing bitwidth, arithmetic range and finite observation checks also apply
to aggregate literals and counts. The integer value interval does not restrict
cardinality results. Oversized literals or count ranges produce diagnostics;
they cannot wrap into a weaker constraint. Bounded parentless abstract `:=`
initializers retain the explicit unsupported clock diagnostic. Only the already
admitted omitted/unrestricted clock forms are available; aggregate support does
not select an initializer clock. To combine those bounds with an authored clock,
select the [initializer clock profile](behavioral-frontend.md#explicit-initializer-clocks).

## Proof and executable boundaries

`SemanticsBridge.BehavioralResolution.aggregate_bounds` proves the effective
normalization and validity of the retained authored range from successful
elaboration. Source rows and `source_coverage` preserve original declarations,
paths, authored bounds and attachments.

`SemanticsBridge.Behavioral.AbstractMultiplicity.formula_inRange`, `global` and
`fiber` connect the ordinary generated formula to upstream `InRange`, `Global`
and each parent fiber. They require finiteness of the counted set, not a finite
ambient integer universe. `normalized_valid_iff` relates the lowered structural
validity plus upstream `Always` to upstream `Valid`, assuming unrestricted
effective bounds for authored abstracts. It changes no ownership, reference,
key or group obligations.

`Correctness.Behavioral.Full.AbstractMultiplicity.generated_iff` and `model_iff`
prove that all generated attachments are exactly upstream `Always` in an
otherwise unchanged source model. `source_valid_iff` discharges effective
normalization from successful elaboration for the upstream `Valid` equivalence. `frontend_sound` composes this with actual
target compilation and decoding; finite abstract heads follow from decoded
occurrence tables. `frontend_complete` takes the independent aggregate obligation
alongside the existing structural/modifier/property and command obligations,
primitive declaration, successful compilation and `Fits` conditions. Scopes,
integer ranges, occurrence capacity and lasso bounds remain explicit premises.
The completed mathematical integer domain remains infinite.

The independent Python observation checks authored counts directly from live
head/fiber sets rather than reading generated constraints. The
[exact candidate corpus](../tests/behavioral_abstract_multiplicity_cases.py)
covers zero, optional, exact, ranged, unbounded and omitted bounds, sibling totals,
cross-parent totals, absent ancestors, inherited parents, shared reference targets,
inheritance chains and later-state violations. The
[comparison tests](../tests/test_behavioral_source_comparison.py) fix complete
candidate traces in Alloy and replay a dropped-aggregate mutation. The eight-head
witness uses a larger Analyzer parser heap, retained in replay settings; its
identity scopes, bitwidth and solver deadline are unchanged. The
[native tests](../tests/test_abstract_multiplicity.py) check provenance, profile
isolation, rich/core fixed points, metadata erasure, stale rich rejection,
optimizer slots and unsafe ranges. These parser/JSON/Python/Analyzer checks are
executable evidence, separate from kernel proofs and independent semantic review.

## Reuse and implementation limits

The implementation reuses the existing declaration certificates, typed expression
families, cardinality/range analysis, attachment compiler, core interchange,
exact-lasso comparison and Mathlib finite-cardinality lemmas. The accepted upstream
predicates supply the independent meaning; the pinned Haskell resolver and
rich/core candidate supply syntax/defaulting evidence, not an aggregate oracle.
Their historical profiles are not relabelled as this extension.

Generic cardinality lowering enumerates bounded alias membership cases. Integer
aliases outside a collection's established value interval cannot contribute;
`Expressions.Context.captureAliases` and its existing coverage proof now serve
cardinality lowering as well as captured binders. This avoids enumerating the
whole signed integer domain for ordinary head counts without changing definedness
or relaxing range checks. Enumeration can still grow exponentially with identity
bounds. Direct target `#` would need different totality/range proofs and is not
substituted into this literal-based lowering.

Lean/Std lists and vectors, Mathlib sets and the existing solver tooling meet the
infrastructure needs. No new runtime dependency or license obligation is added;
compiler/upstream code is MIT and Lean retains its Apache-2.0 license.
