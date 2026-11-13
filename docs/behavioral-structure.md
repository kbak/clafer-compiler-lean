# Behavioral structural prerequisites

`impl~compiler-behavioral-structural-bridge~1`

The `behavioral-0.5.7-candidate/v1` library APIs supply the structural handoff in
the [behavioral matrix](behavioral.md#complete-feature-and-evidence-matrix).
They use the accepted upstream S4 meaning at the [installed pin](sources.md).
They do not constitute a behavioral source command or an Alloy temporal encoding.
C7 owns complete source parsing and expression elaboration; C8 owns composition
with modifiers, transitions, patterns and temporal target preservation. The
existing static CLI, expression rules and admission profiles retain their contracts.

Covers:
- `req~compiler-behavioral-structural-bridge~1`

## Resolved declarations and admission

[`IR.BehavioralStructural`](../ClaferCompiler/IR/BehavioralStructural.lean)
retains the structural table, authored abstractness and effective group provenance
separately. Declared references remain declared; inherited references identify
their nearest original owner. `validate` and `validateRaw` require explicit profile
selection and return checked data or malformed/unsupported diagnostics.
The supported primitive domain is mathematical integers; string, Boolean and
other runtime primitive domains are outside this profile.

Admission checks unique IDs and root, containment and super ranks, bounds,
authored/effective abstractness, nested/refined parents, concrete supers,
nearest inherited references, target refinement and kind refinement. Set references
may refine bag references; bag references may not refine set references.
An impossible group remains a valid model description whose instances may be
unsatisfiable. Admission does not assume source constraint truth or target truth.

`analyze` iterates finite ancestor/owner tables for the declaration count.
`Analysis.Valid` checks their exact recursive equations before they can be used;
rank checks rule out cycles. In the
[`BehavioralStructural` bridge](../ClaferCompiler/SemanticsBridge/BehavioralStructural.lean),
`ancestor_sound`/`ancestor_complete` and `owner_sound`/`owner_complete` identify
those tables with upstream relations. `validated_wellFormed` derives upstream
`Structural.Core.WellFormed` from successful admission. `checks_iff` proves the
guard equivalent to that meaning on supported primitives, checked tables and
supplied decreasing ranks. The iteration's convergence for every acyclic table
is tested on generated forward chains, not a separate proved totality theorem.

`childDeclarations` returns own and inherited child declarations.
`childObjects_iff` proves that upstream effective groups use the union of their
original head fibers. A head present in multiple inherited views counts once;
distinct bag heads with an equal target remain distinct. Ordinary inherited fields
remain attached to their original declarations. State validity, including abstract
cover, live targets, coherent shared reference assignments, keys, multiplicities
and effective groups, is the upstream `Structural.Valid` predicate. This library
does not replace it with a finite trace checker or an asserted validity premise
hidden inside a target representation.

## Source identity and defaults

[`Frontend.BehavioralResolution.elaborate`](../ClaferCompiler/Frontend/BehavioralResolution.lean)
accepts an authored `Document` and the explicit profile. It reuses finite inventory,
source spans, forward/lexical/unique-global lookup, group provenance and rank
construction. `SourceRow` and `Elaboration` independently check coverage,
preorder identity, source paths, exact names, authored data, parent/super/reference
targets and defaults. Direct-name concrete and nested supers are permitted. Missing or
ambiguous names remain errors; no `noclafer` navigation shortcut is introduced.
Current super lookup uses authored lexical/global candidates, without an
inherited-child search or self exclusion; same-name redefinitions can therefore
fail as inheritance cycles. Qualified type paths are rejected by the parsers.
The [super-lookup review candidate](super-lookup.md) records distinguishing native
and reference cases and the proposed behavioral rules; it does not change this
implemented policy or the static profile.

The [resolution bridge](../ClaferCompiler/SemanticsBridge/BehavioralResolution.lean)
proves original declaration coverage, per-row correspondence, upstream
`Clafer.Defaults` and well-formedness. Keyword `opt` retains optional child
defaults; numeric `0..*` retains mandatory child defaults. Inherited group
provenance and explicit overrides survive resolution. Constraints remain in the
original document at their owner paths; this API does not claim to elaborate them.
Parsing the existing declaration subset is tested; full behavioral grammar
correspondence remains C7's obligation.

[`BehavioralDeclarations`](../ClaferCompiler/Frontend/BehavioralDeclarations.lean)
expands an enum into an authored abstract family and singleton literal subtypes.
It retains every literal token in `finalLiterals` for C7's dynamic modifier binding.
The static parser continues to reject enums. `constantInitializer` constructs
`some heads => left = value`, preserving spans and the supplied views, and rejects
`:=` explicitly. This is syntactic sugar for an ordinary attachment at every live
enclosing state; it adds no birth operator. C7 must prove the resulting expression
elaboration against upstream `Initializers.constant` and carry enum final markers
to resolved declarations. Native tests check these sugar shapes and inventories;
there is no claim that arbitrary parser output already has that temporal proof.

## Navigation, bindings and expressions

[`IR.BehavioralSupport`](../ClaferCompiler/IR/BehavioralSupport.lean) checks each
class/map occurrence against declaration IDs and head, parent, dereference,
target or inclusion roles. Integer flags must identify exactly the integer
declaration; they cannot hide a primitive extent. `referenceView` returns distinct
head, nearest-owner and target identities and follows exactly one reference.
`Navigation.parent` denotes the actual identity parent, including heterogeneous
parentless abstract contexts; it invents no single typed parent edge.

The [support bridge](../ClaferCompiler/SemanticsBridge/BehavioralSupport.lean)
proves `role_iff`, builds upstream `StructuralBinding.Resolution` from checked
roles and an explicit valid source trace, and derives full link-carrier coherence.
Target-map links retain the intermediate reference head. `referenceView_sound`
establishes nearest ownership and target; `current_target_live` derives liveness
from source validity. `actual_parent` preserves actual-parent observation.
`finite_captured_targets` needs only a finite captured head set and a valid trace,
not a finite integer universe or a finite whole class extent.

`static_agreement` reuses every existing checked static expression constructor
through the richer binding. Its explicit premises are a valid source trace,
live `this`, singleton-compatible captured locals, and full integer-domain equality
for integer classes. Arbitrary captured sets use the accepted behavioral
`Environment`/`SetExpr` APIs; their full executable syntax and source elaboration
belong to C4/C7. Boolean/set/relation operators and finite binders retain the
[existing expression contract](expressions.md) on that common domain.

## Integers and strict definedness

[`IR.BehavioralArithmetic`](../ClaferCompiler/IR/BehavioralArithmetic.lean)
operates on finite observations of mathematical `Int`. `coerce` sums distinct
integer targets (empty is zero); `extract` reuses historical exact-singleton
extraction. Explicit sum/product folds instead preserve every occurrence and
every syntactic operand, including overlapping operands. Empty sum/product are
zero/one. Minimum/maximum yield a singleton extremum or a defined empty set.
Division/remainder truncate toward zero and are undefined at a zero divisor.
All arithmetic operands and both conditional branches are strict; zero products
and false guards cannot hide an undefined operand.

The [arithmetic bridge](../ClaferCompiler/SemanticsBridge/BehavioralArithmetic.lean)
proves scalar agreement, finite-set conversion for any full integer realization,
extremum agreement and occurrence-indexed fold agreement. `extract_common`
reuses the static extraction proof. `range_contains`, `admitted_range`,
`observation_range`, `fold_sum_range`, `fold_product_range`, `extrema_range`,
`negate_range` and `count_range` state conservative numeric bounds separately
from source truth. Budgets must cover all observations/occurrences, including
fold prefixes. `validateOperation` checks operand/result ranges and excludes
possible zero divisors for a selected width in the existing 1–16-bit target range.
It can reject safe expressions conservatively; it never uses a satisfying
candidate to weaken the bound. Fold/observation clients check the returned ranges
with `Interval.fits`. The [frontend range pass](behavioral-frontend.md#whole-expression-range-obligations)
composes these checks over complete expressions. Structural scope budgets and their
connection to target admission remain explicit C8 obligations.
Finite lists cannot stand in for arbitrary infinite or noninteger observations.

## Reuse and evidence

Before implementation, the existing structural admission, inherited realization,
resolver/defaults, expression typing/observation, native harness and validation
tools were inspected. The old `IR.Inherited`/M1 guards exclude the required nested
abstracts, concrete supers and inherited references. Their runtime data types,
lookup, certificates and diagnostics are reused, while behavioral admission has
its own guard. Upstream S4 relations, support binding, captured-static agreement,
finite observations and folds supply the proof boundary; they remain outside the
native import closure. The pinned Haskell grammar, `ResolverInheritance`
(`resolveNSuper`, `analyzeCard`, `analyzeGCard`) and `Desugarer` enum/initializer/
aggregate cases supply syntax/comparison evidence, subject to accepted D1–D5.

Lean/Std supplies vectors, lists, options, traversal, strict extraction and
`List.min?`/`max?`; existing Mathlib supplies finite-set and relation proofs.
The small executable set sum recurses over membership because it needs a
computable duplicate-insensitive fold without importing noncomputable finite sets
into runtime. It uses the existing bounded `Nat.rec` pattern to avoid generated
unsafe workers; the pinned compiler does not generate native code for `List.rec`.
No graph package, parser framework, new package or license is added.
Project code and upstream semantics remain MIT; Lean is Apache-2.0.

[Kernel witnesses](../tests/BehavioralStructural.lean),
[native assertions](../tests/BehavioralStructuralNative.lean) and the
[native harness](../tests/test_behavioral_structural.py) cover structural/profile
mutations, distinct parent/head/owner/target roles, inherited child unions,
defaults, finite arithmetic and unsupported domains. The original
[resolved source fixtures](../tests/fixtures/behavioral-structural) are inputs for
subsequent modifier/pattern/transition work. They are not full temporal target
qualification. The mandatory check retains all static regressions, kernel replay,
axiom audit and real static oracle comparisons. Independent review remains
required before feature acceptance and full behavioral qualification.
