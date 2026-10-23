# Guarded structural Alloy encoding

The backend accepts the guarded effective M1 domain and explicit manual bounds,
returning a checked target AST and declaration map. The
[correctness layer](structural-correctness.md) proves M1 soundness and finite
bounded completeness with explicit scope/range hypotheses.

[Text serialization](alloy-text.md), [native commands](cli.md) and
[generated-text comparison/decoding](comparison.md) compose this API while
retaining their own assurance boundaries.

## API and admission

`impl~compiler-structural-backend~1`

[Structural.lean](../ClaferCompiler/Backend/Alloy/Structural.lean) defines the
runtime API in `ClaferCompiler.Backend.Alloy.Structural`:

```text
compile    : IR.Structural.Validated n → Bounds → Except Error Compiled
compileRaw : IR.Structural.Raw → Bounds → Except Error Compiled
```

`compileRaw` first calls the existing `validateRaw`; it does not reinterpret
defaults, erase expressions or weaken admission. The typed API receives the
actual checked source table. No extra source-feature restriction is introduced.
Unsupported primitives, reference inheritance, abstract bodies and other excluded
forms retain the IR rejection. Source text, JSON decoding and version/profile
dispatch must go through their respective boundaries before this API.

`Bounds.declarations` contains exactly one `(input declaration ID, Scope)` for
every declaration, including root and abstracts. `Bounds.objects` is an upper
budget for all distinct source objects, including the root; inherited extents
overlap and are not summed. `Bounds.bitwidth` selects the target's signed 1–16
profile. Duplicate, missing, unknown or extra scope IDs return `malformedBounds`.
Scope entry order does not affect allocation. No scopes or rank certificates are
inferred, and no solver is run.

`unsupportedBounds` denotes the independent target's conservative integer/literal
range rejection or invalid bitwidth. It is not UNSAT. `source diagnostic` preserves
the IR category/code/pointer/ID. `internalTarget` denotes failed generated target
typing, an implementation failure rather than a source rejection. General absence
of that error is not yet proved; successful results carry both target checks.
The [native driver](cli.md) serializes these errors with the architecture's phase/category conventions.

`Compiled.module` is a `CheckedModule`, carrying syntax/binding and bounds proofs.
`Compiled.declarations` preserves input declaration order, IDs, names and source
spans, with signature and optional containment/dereference field indices.
`Compiled.obligations` parallels the emitted facts and identifies each obligation
and source declaration. Numeric target identity never comes from a display name.
The original validated IR remains the source of authored metadata and diagnostics.

Native compilation shares a dense `cachedAllocation` across schema, facts and
metadata generation. It uses Lean's `Vector.ofFn` and existing `order`/`fieldKeys`
functions; no indexing library is added. `cachedAllocation_eq` proves equality
with the reference allocation, including lookups of absent field roles.
`compile_eq_compileCached` registers the complete result equality with Lean's
`@[csimp]` mechanism for both structural and inherited compilation. The reference
definitions remain the basis of preservation proofs; emitted identities, metadata
and errors are equal. Native code generation remains a tested boundary.

Covers:
- `req~compiler-structural-encoding~1`

## Concrete representation

Signature 0 is an abstract **object union**, not a new object or an auxiliary token.
It equals the union of every declaration extent and receives `Bounds.objects` as
an upper scope. There are no auxiliary atoms. Signature positions 1 through n
represent source declarations, ordered by checked super rank, then input position.
This orders every super before its children, including reverse-ordered input and
abstract chains. Names, timestamps and private paths do not affect this ordering.

Each declaration extends its super signature, or the object union if it has no
super. Alloy's extends forest supplies identity-preserving inclusion and disjoint
incomparable extents, including across containment contexts. The source's checked
root has no super and cannot be a super target, so root freshness follows from
this same layout. Every signature uses `set` multiplicity. The root singleton is
a fact, allowing exact scope zero to remain a valid contradictory request.

The object carrier for decoding is exactly signature 0. Every live atom
must occur in a declaration extent. Allocation slots absent from all extents are
unobservable and excluded from the source carrier. An atom in signature 0 but
outside all source extents violates cover. The object union is counted once,
even for an object inhabiting several signatures along a super chain.

Fields are allocated in original declaration order, containment first and then
dereference when present, in a separate positional namespace:

| Source relation | Field endpoints and declaration | Generated obligation |
| --- | --- | --- |
| Containment for d with parent p | `p -> set d` | Every d head has exactly one incoming owner; each p owner satisfies d's local interval |
| Set/bag reference d to t | `d -> one t` | Every reference head has exactly one target; only set references add a per-owner key |
| Super d to s | `d extends s` | The same atoms inhabit d and s; no object copying or extra inclusion links |

Each reference occurrence is its head atom. Ordinary link identity is its typed
owner/head or head/target tuple. A derived owner/target span retains the intermediate
head and must never be quotiented by equal endpoints. Bag heads 2 and 3 may both
refer to atom 1; set references reject that pair for one owner, while allowing
different owners to reference the same target. Reference cycles do not affect
signature order or cause recursive traversal.

## Complete obligation bank

The emitted schema and facts jointly enforce every conjunct of S1's
`StructuralSatisfies`; target truth remains independently defined by #8.

| Upstream obligation | Generated target mechanism |
| --- | --- |
| `Typed` | Field owner and target signatures; no fields for absent relations |
| `Rooted` | Root singleton fact, disjoint root branch, object-union cover and the decoding carrier policy |
| `Inherits`, `DeclarationDisjoint` | Extends forest, with all unrelated declarations in disjoint branches |
| `Abstracts` | Abstract signature plus explicit equality with the union of immediate subtype heads, including an empty union |
| `Parents` | `all head : D` requires one owner through the transposed containment field |
| `References` | Per-head `one` target field multiplicity |
| `Keys` | For each owner, two contained heads with equal dereference images must be equal |
| `Multiplicities` | Local interval over each owner's containment fiber |
| `Groups` | Effective group interval over the union of child-head fibers for each concrete context |

Abstract cover is explicit even for leaves: Alloy allows a nonempty unextended
abstract signature, whereas the source requires the empty subtype family to cover
an empty extent. Unused zero-bound abstract chains become empty through cover.
Parentless abstract local slots do not invent parent-fiber predicates.

Group unions use direct children because all supported abstract ancestors are
childless. S1's direct group inventory is thus exact for M1; #13 owns the richer
inherited-field case. Reference children contribute their heads, not dereferenced
values. Empty inventories remain explicit empty relations: zero-containing bounds
hold, while positive lower bounds fail for an inhabited context. A positive group
lower bound without any child declaration is already outside exact M1 admission;
an admitted xor with child declarations but zero realized children fails normally.

Intervals emit a lower comparison only when the lower bound is nonzero, and an
upper comparison only for a finite upper bound. Unrestricted intervals introduce
no integer operation. Counts use distinct tuples; infinity is never an integer.
The independent range analysis uses scope inventories (and conservative union
sums), not facts or successful satisfaction. This may require a larger bitwidth
even when a particular candidate's count is small. No interval, scope or arithmetic
policy is weakened to obtain admission. General no-overflow correctness remains
the existing #8 boundary; runtime representability checks remain active.

## Proof and test boundary

`proof~compiler-structural-generation~1`

[StructuralGeneration.lean](../ClaferCompiler/Correctness/StructuralGeneration.lean)
kernel-checks the following local facts, without assuming source satisfaction:

- `order_perm`, `mem_order`, `order_nodup`, `order_length`,
  `signatureId_bounds`, `signatureId_injective`, `signature_inventory`:
  complete, unique declaration allocation with no collision with the object union.
- `nameMap_inventory`, `declarationMap_preserves`: source identity, names and spans.
- `containment_inventory`, `dereference_inventory`, `fieldId_bounds`,
  `fieldId_injective`, `field_lookup`, `containment_direction`,
  `dereference_direction`: relation presence, identity and endpoint orientation.
- `child_inventory`, `subtype_inventory`: exact resolved-edge inventories.
- `root_generated`, `object_cover_generated`, `declaration_fact_generated`,
  `abstract_cover_generated`, `ownership_generated`, `local_bounds_generated`,
  `group_generated`, `set_key_generated`: required formula membership.
- `compile_output`: successful compilation returns the specified generated target,
  declaration map and fact labels. `compiled_checked` extracts its two target checks.

Covers:
- `req~compiler-structural-encoding~1`

## Kernel witnesses and finite comparisons

`utest~compiler-structural-generation~1`

[Kernel witnesses](../tests/StructuralAlloy.lean) check unrestricted/empty group
behavior, head counting, the nested set-key binders and generated bag facts.
[Native tests](../tests/StructuralAlloyNative.lean) exercise 39 hand-authored positive
and negative candidates, every existing 28-case source-admission fixture, bound
rejection/contradiction cases, reverse super order and scope order. Six mutations
remove root, owner, local-bound, group, key or abstract-cover facts; the corresponding
negative candidate then passes, demonstrating assertion sensitivity.

[Independent comparison](../tests/StructuralAlloyComparison.lean) evaluates those
39 fixtures and 256 generated candidates against the pinned upstream finite
checker plus independently read manual bounds. The generated domain enumerates
all subsets of two owner/head and four head/target tuples on five atoms, for bag,
set and two group inputs; ten satisfying generated witnesses prevent a vacuous
all-negative comparison. Missing/multiple links are retained. Its test-only finite
adapter uses the output declaration map, retains tuples and heads, and maps an
empty target carrier to a nonmember root so source rejection is observable.
This finite adapter is not the production encode/decode bridge or a proved relation.
The [Python runner](../tests/test_structural_alloy.py) executes both checks without
adding a production CLI command. Native Lean/C execution remains trusted.

The mandatory full check also retains the existing actual Haskell/Lean/Alloy
oracles and independent target/Analyzer comparisons. This task adds no generated
Alloy text claim. All checks, dependency pins, module/import/axiom audits and kernel
replay remain mandatory. IntentBond exit 4 means semantic review remains pending.

Covers:
- `req~compiler-structural-encoding~1`

## Handoff to #11 and #12

Prove the concrete object bijection, declaration extent equations and per-role
tuple equations for this layout. Derive all source obligations from target
satisfaction, including full-carrier root coverage and disjointness, and construct
a target from any source configuration fitting the explicit bounds. Discharge
ancestry/rank ordering and range assumptions independently; do not assume either
preservation conclusion in a representation hypothesis. Define executable finite
encode/decode and prove their adequacy. Compose these with S1's actual structural
and finite-representation theorems with their hypotheses discharged.

General generation well-typing, global soundness/bounded completeness, totality
under safe manual bounds, production decoding and text/runtime correspondence are
not established by the local lemmas or finite tests above. #11 owns the global
proofs; #9/#12/#19 retain their serialization, external-tool and CLI boundaries.
