# Selected inherited structural realization

Issue [#13](https://github.com/kbak/clafer-compiler-lean/issues/13) is selected after
the maintainer accepted the #11 proofs in [PR #33](https://github.com/kbak/clafer-compiler-lean/pull/33)
at `67b9137cde9e2b486733aecd6eb4f5559b780ea3`. This is the starting commit for
this extension. Its semantic acceptance remains a separate review gate.

## Reuse and source boundary

The implementation reuses the accepted structural allocator, finite observations,
independent Alloy evaluator and #11 preservation lemmas. `Structural.Layout`
extracts the checked allocation assumptions those lemmas actually require:
core checks, parent/super ranks and a root that cannot be a supertype. It is not
an admission profile. The original `Structural.Validated`, `validateRaw`, document
profile and `compile` still enforce the exact M1 support guards. Calls to shared
allocation/representation helpers now use `v.toLayout` explicitly.

Pinned upstream `Semantics.Realization.Core.Selected`, `Satisfies`, `View`,
`headView`, `derefView`, `targetLink`, and `RealizationCompatibility` already supply
the reusable semantic interfaces. `Compile.Groups.Ancestor`, `ChildObjects` and
`Holds` supply inherited union semantics. No missing upstream bridge, dependency
upgrade or new library is needed. Mathlib's existing finite-cardinality, equivalence
and reachability lemmas remain proof-only dependencies. All new code is original
MIT project code; no upstream meanings or Haskell implementation are copied.

The supplementary Haskell source is S6's pinned `Generator/Alloy.hs`, particularly
`genGroupConst` (hierarchy-wide children), `genParentConst` and `genOptParentConst`.
Its abstract/empty-child skips do not replace the adopted source meaning.
The [source register](sources.md) records the pins and published locators. Runtime
modules import only the local executable IR/target and the Lean standard library.

## Admission and generation

`impl~compiler-inherited-realization~1`

[IR/Inherited.lean](../ClaferCompiler/IR/Inherited.lean) adds a separate opt-in
`Core`, `Raw`, `Validated`, `checks`, `validate` and `validateRaw` API. Inputs retain
the original resolved effective table, with mandatory authored `explicitAbstract`
flags and realization ranks. The existing raw ID resolver is shared, preserving
names, IDs, source metadata, input order and dangling-ID diagnostics. The original
optional `authored` record remains informational; `explicitAbstract` is the semantic
flag for this API. No parser/defaulting or CLI integration is implied.

Admission checks core shape and acyclicity, explicit families' effective abstractness
and parentless placement, explicit basic supertype targets, basic subtype references,
parented references, realization ranks, nested effective abstractness, and origins.
Only root/user origins and a unique optional integer primitive are supported.
The primitive must be basic, root-owned and have no supertype; reference targets
must be user declarations or that integer declaration. Boolean/string primitives,
nonbasic subtyping and broader inherited forms remain unsupported.

The allocation projection retains every ID, edge, origin, local bound and occurrence.
It uses the explicit flag for abstract-family cover and temporarily replaces group
bounds by `0..*`. Ordinary fields made effectively abstract by containment therefore
retain their realized heads and ownership links. They are not abstract Alloy leaves.

[Backend/Alloy/Inherited.lean](../ClaferCompiler/Backend/Alloy/Inherited.lean)
reuses that allocation and appends actual group constraints for each ordinary
declaration. `ancestors` uses structural recursion with checked super-rank fuel;
`mem_ancestorWalk` proves that no source path is truncated; `children` collects original
children of every ancestor. `childHeads` unions their original containment fibers.
The count is a set union of head objects, with neither contextual copies nor counts
of reference target values. Five explicit families in Appendix 6 receive cover;
incomparable extents retain the existing extends/disjointness encoding.

`compile` and `compileRaw` require the same explicit total-object and per-declaration
scopes and signed bitwidth as M1. They run the independent target checker and retain
source declaration maps and obligation tags. `encode`/`decode` reuse the shared
finite carrier and preserve distinct bag occurrences. No automatic bounds inference
or solver-output parser is introduced.

[InheritedViews.lean](../ClaferCompiler/Backend/Alloy/InheritedViews.lean) provides
`viewContains`, `viewHeads` and `viewDeref` over a decoded observation. Each filters
original tables by actual context-owner membership. These views retain opaque labels
and intermediate reference heads; they allocate nothing and do not equate a
context membership with an ownership edge.

Covers:
- `req~compiler-inherited-realization~1`

## Preservation statements and assumptions

`proof~compiler-inherited-realization~1`

[SemanticsBridge/Inherited.lean](../ClaferCompiler/SemanticsBridge/Inherited.lean)
interprets the original effective table and explicit flags directly as the pinned
`Realization.Core`. `selected` and `wellFormed` derive the upstream domain predicates
from executable guards. `satisfies_iff` proves that independent inherited satisfaction
is exactly projected structural satisfaction plus the original inherited groups.
`m1_compatibility` proves equality with the old source meaning on the admitted M1
intersection, deriving flag equality from selection/support guards. The old M1
compiler, its preservation proofs and existing tests remain in force.

In namespace `ClaferCompiler.Correctness.Inherited`:

- [InheritedGeneration.lean](../ClaferCompiler/Correctness/InheritedGeneration.lean)
  proves `mem_ancestors`, `mem_children` and `compile_output`: executable inventories
  match upstream paths/parents, and successful compilation returns the actual target.
- [InheritedFacts.lean](../ClaferCompiler/Correctness/InheritedFacts.lean) proves
  `represented_children`, `group_eval_iff`, `groups_iff` and `base_satisfies`.
  The existing data-only `Structural.Represents` relates the common live carrier,
  all extents and active-role tuples. It assumes no source/target satisfaction.
- [InheritedCorrectness.lean](../ClaferCompiler/Correctness/InheritedCorrectness.lean)
  proves `compiled_sound`: any independently satisfying actual compiler output
  successfully decodes, has a concrete representation, and satisfies the original
  `Realization.Satisfies`. It constructs these conclusions rather than requiring them.
- `compiled_complete` constructs a satisfying encoded target for any finite source
  satisfying that independent meaning, given a successful compilation,
  `Structural.ObservationScopesFit` and `Inherited.CountFits`. These are numeric
  scope and signed-count representability conditions, separate from semantic truth.
  Counts cover local fibers and the inherited unions actually observed by groups.
- [Correctness/InheritedViews.lean](../ClaferCompiler/Correctness/InheritedViews.lean)
  proves `view_contains`, `view_heads`, `view_deref`, `observation_owner_live` and
  `context_links_injective`. The head/dereference correspondence requires owners
  to be in the live carrier; `observation_owner_live` derives this from target
  liveness, itself derived by soundness. The final theorem reuses upstream's
  injective map on original composable link pairs, including repeated bag targets.

These are structural, finite-observation theorems. The integer declaration denotes
observed primitive objects here; no valuation identifies its labels with mathematical
integers or Alloy's builtin `Int`. `Realization.Satisfies` does not assert the separate
primitive-domain interpretation. A model containing every mathematical integer
cannot have this finite live carrier. The fixture uses `int 0..*` and one observed
integer object, without claiming a complete primitive-domain interpretation.
Value preservation, expression denotation, c01–c12, final selection and the full
finite/infinite primitive bridge belong to #14/#15/#20. These statements neither
prove unbounded UNSAT nor transfer to native/serialized/Analyzer execution without
their respective assurance boundaries.

Covers:
- `req~compiler-inherited-realization~1`

## Fixtures and mutations

`utest~compiler-inherited-realization~1`

[Inherited.lean](../tests/Inherited.lean) kernel-checks a nonempty ordinary xor field
under an explicit abstract family, a concrete context whose group counts an inherited
field, the actual successful compilation, and both preservation directions.
It uses the kernel decision procedure and proved inventory equations.

[InheritedNative.lean](../tests/InheritedNative.lean), executed as a linked native
binary by [test_inherited.py](../tests/test_inherited.py), contains the entire
Appendix 6 structural inventory. IDs 1–26 correspond to the paper's d01–d26;
0 is the synthetic root and 27 is the integer primitive. Duplicate display names
retain distinct IDs. The inventory is:

| IDs | Declarations |
| --- | --- |
| 1–7 | options, size, small, large, cache, cache.size, fixed |
| 8–13 | comp, version, ECU, display, server, display.options |
| 14–18 | plaECU, plaDisplay, ECU1, ECU2, master |
| 19–26 | telematics, channel, single, dual, extraDisplay, size, small, large |

Seven super edges are `10→8`, `11→8`, `13→1`, `14→10`, `15→11`, `16→14`,
`17→14`; explicit families are 1, 8, 10, 11 and 14. Xor groups are 2, 20 and 24.
References are `6→27`, `9→27`, `12→10`, `18→16`. The plaDisplay multiplicity
is `1..2`, ECU2/cache/alternatives/extraDisplay are optional and other authored
parented declarations have multiplicity one; integer observation is `0..*`.

[InheritedInventory.lean](../tests/InheritedInventory.lean) kernel-checks every
semantic declaration field and parent against the complete pinned upstream
`Telematics.Input` inventory by original ID, including parentless default bounds
and `int 0..*`. No source definitions are copied.

The positive witness realizes both ECUs, one display each, distinct version heads
sharing one primitive object, distinct display options and choices, master and the
telematics alternatives. Mutations add a second owner to one original version
head, remove an entire optional choice to violate inherited ordinary-field xor,
and add an uncovered explicit-family object. All three remain decodable and
round-trip unchanged while the target evaluator rejects them. Further tests check
context labels/links, no copied declarations, M1 rejection of this extended input,
missing flags/ranks, cyclic realization ranks, a false explicit-family claim and
an unsupported primitive. This is the structural skeleton, not the complete
constraint model or a generated-text differential oracle.

Covers:
- `req~compiler-inherited-realization~1`
