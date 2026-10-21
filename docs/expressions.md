# Typed static expressions and finite observation

[Issue #14](https://github.com/kbak/clafer-compiler-lean/issues/14) is accepted
through merged PR #32 after structural IR #7. It implements the expression API and
its proof-only upstream interpretation.
[Expression encoding #15](https://github.com/kbak/clafer-compiler-lean/issues/15)
and [source elaboration #18](https://github.com/kbak/clafer-compiler-lean/issues/18)
consume this boundary. The M1 structural admission and `clafer-ir/1` profile still
reject static constraints; this API does not silently extend either contract.

## Runtime representation and admission

`impl~compiler-expression-runtime~1`

[Expr](../ClaferCompiler/IR/Expr.lean) supplies finite `Support` vectors, `Local`,
`Collection`, `Ty`, raw `Syntax` and `Path` trees, and executable `Term`/`Widen`
builders. Each builder caches a structural traversal budget and a proof that it
cannot run out. Native checks recurse through the standard-library natural
recursor, satisfying the project declaration audit. Integer magnitude and source
metadata do not contribute to the budget. `Term.certify` witnesses in the logic
that every raw finite tree can be represented; it adds no language restriction.
Support positions identify occurrences; resolved class IDs, map owners/roles and
names remain separate fields. Repeated maps and equal IDs are retained. Every
constructor in the [M2 inventory](architecture.md#m2-typed-core-exhaustive-constructor-inventory)
has a direct representation. `located` retains original byte spans at any node;
metadata is erased only by the mathematical interpretation. The returned checked
tree preserves the entire input, including spans, order and duplicate occurrences.

`Term.Typed` has an executable decision procedure. `check s Γ t e` returns
`Checked s Γ t` or a deterministic diagnostic. It verifies the declared sort,
collection shapes, map incidence, explicit widening paths, primitive extraction,
lexical positions, fresh binder IDs and nonreversed spans. Locals are nearest-first;
quantifier domains use the outer context. Names may shadow. Binding IDs must be
fresh relative to the enclosing context. `this` is unaffected by a binder.
`Widen.same` requires equal resolved IDs; inclusion paths require inclusion-role
map edges with the specified endpoints. There are no casts based on names.

The input is already resolved, with bounded `Fin` indices. The frontend owns
construction of support against the real AST, declaration/attachment identity,
primitive annotations, external-local freshness and original file lengths.
`support s` preserves every upstream support field; its `Resolved` and constraint
boundary obligations remain required at that handoff. A successful expression
check alone does not prove AST resolution or structural satisfaction.

`Term.extents` and `Term.maps` are proof-only ordered occurrence lists. `Term.Observed` rejects
every direct primitive extent, including inside equality, cardinality, Boolean
branches and quantifier bodies. Primitive type positions, finite singleton
variables and navigation to observed integer values remain available. A support
may have zero maps: literal constraints use direct independent denotation.

Diagnostics use the existing IR category/code record:

| Code | Category | Trigger |
| --- | --- | --- |
| `expr.type-scope-or-span` | malformed | Failed type, lexical, widening or span check |
| `expr.infinite-primitive-extent` | unsupported | Direct primitive extent observation |
| `expr.unsafe-bounds` | unsupported | Invalid width/interval or uncertifiable integer range |

These are an in-memory API. JSON parsing, text diagnostics, source elaboration,
Alloy constraint generation and production CLI changes are separate tasks.

Covers:
- `req~compiler-expressions~1`

## Arithmetic and candidate obligations

`impl~compiler-expression-bounds~1`

[ExprBounds](../ClaferCompiler/IR/ExprBounds.lean) uses mathematical `Int` intervals.
`validateBounds` first checks syntax, then checks the explicit width (1–16) and
computes an `Estimate`. The result retains proofs of the width check and the
actual analysis result. No modular arithmetic or implicit scopes are used.
Addition maps intervals to `[a.lower+b.lower, a.upper+b.upper]`; subtraction to
`[a.lower-b.upper, a.upper-b.lower]`. Negation is subtraction from zero.
Every literal, extraction interval and arithmetic intermediate must fit the
signed width. All Boolean branches and binder bodies are inspected independently
of their truth, even with an empty domain.

Collection budgets are conservative upper bounds: singleton 1, declared extent
budget, map endpoint product, union sum, difference left budget, intersection
minimum, image relation budget and join product. Cardinality checks `[0,budget]`.
A large budget alone is not an integer expression; it is checked when observed by
cardinality. Finite primitive budgets count observed integer objects, not the
infinite primitive extent. The analysis may reject an individually safe candidate;
it does not assert UNSAT. The arithmetic interval-transfer and representability
lemmas are kernel checked. Selected #15 now supplies
[general analyzer-to-denotation proofs](expression-encoding.md#source-range-analysis-proofs)
and scalar target representability, pending semantic review. Source-to-Alloy
constructor and attachment correspondence remain unfinished. The analyzer is
also exercised natively.

[ExprObservation](../ClaferCompiler/IR/ExprObservation.lean) distinguishes
`Atom.object id` from `Atom.integer value`. `Observation` contains finite object
lists and original links with IDs and endpoints. `Observation.withinBounds`
checks distinct-object budgets, primitive/object tags, every observed integer's
interval and bitwidth, and inclusion of both link endpoints in the recorded
observations. Equal resolved class IDs must have equal observed sets (including
primitive positions), so identity widening cannot evade a destination interval. `Environment.valid` checks complete lexical membership and `this`
against full class domains. `Environment.bounded` additionally requires every
external variable and `this` to occur in the finite bounded observation. Neither
check evaluates a constraint or replaces structural candidate satisfaction.

The standalone `extract` helper implements set singleton extraction: duplicates
of the same integer object are one value; empty, distinct multiple or off-domain
objects return `none`. It is proved equal to upstream extraction on every finite
list. There is **no general finite expression evaluator** in this task.

Covers:
- `req~compiler-arithmetic~1`

## Independent meaning and proofs

`proof~compiler-expression-semantics~1`

[Expr bridge](../ClaferCompiler/SemanticsBridge/Expr.lean) supplies a total,
proof-only `interpret` from any typed raw tree (`checked.term.raw`) to `Clafer.Constraints.Expr`. It maps
each constructor to its existing upstream constructor, retaining lexical position,
operand order and support incidence. `denote` calls upstream `Expr.denote` directly.
No DP graph compilation or positive-map hypothesis is inserted.

The result is `Option (Value ...)`: `none` is undefined; `some ⟨False⟩` is defined
false. Hard satisfaction requires defined true. Boolean operators retain strict
definedness. Empty universal domains return true without evaluating bodies.
Quantified bodies use one actual domain object at each lexical position.

[Observation bridge](../ClaferCompiler/SemanticsBridge/ExprObservation.lean)
constructs a full integer extension over `Atom`. `ObservationValid` states the
independent binding obligations: equal IDs denote equal classes, endpoints are
well typed, link IDs are unique per map, repeated owner/role occurrences retain
the same links, and inclusion maps are identity bijections onto their source.
These obligations do not assume the expression's denotation, definedness or truth.
The canonical `extend` retains all nonprimitive extents and original link records,
and assigns **all** mathematical integers to primitive vertices.

`ExtendsObservation` relates any full binding to these observations using actual
link bijections. `finite_observation_agreement` proves equal denotation in every
such extension. `extend_realizes` provides a canonical extension, and
`extend_coherent` proves repeated-map coherence. `environment_admissible` turns a
successful executable environment check into actual upstream admissibility.
[ExprFinite](../ClaferCompiler/SemanticsBridge/ExprFinite.lean) proves finite meaning
for every admitted collection, including integer navigation. Cardinality operands
and quantifier domains are therefore finite without a finite ambient universe.

Primitive/root obligations stay explicit: `extend` is an `IntegerBinding`, not a
full structural configuration or a proof of its root/parent/primitive axioms.
The caller must supply the actual resolved context and its admissible `this`;
no primitive parent or synthetic root edge is invented. #13/#20 own composition
with structural realization. Kernel witnesses show a singleton nonprimitive root
coexisting with every integer, including values outside the finite observation.
M2 end-to-end assurance still requires that structural composition and #15.

Principal checked declarations in `ClaferCompiler.SemanticsBridge.Expr`:

| Declaration | Conclusion / assumptions |
| --- | --- |
| `check_iff`, `check_preserves` | Exact type/observation admission and unchanged input tree |
| `interpret` | Typed upstream syntax from the executable typing judgment |
| `interpret_footprint`, `checked_nonprimitive` | Exact support observations; no admitted whole primitive extent |
| `extend`, `extend_realizes`, `extend_coherent` | Full-Int, identity-preserving coherent binding under `ObservationValid` |
| `finite_observation_agreement` | Denotation agreement for any full extension with the specified objects/links/realization |
| `checked_collection_finite` | Finite set/relation meaning in the canonical extension |
| `extract_iff`, `extract_agreement` | Exact partial singleton extraction for every finite list |
| `environment_admissible` | Checked lexical/context membership implies upstream admissibility |
| `add_contains`, `subtract_contains`, `fits_representable` | Mathematical interval transfer and signed representability |

Covers:
- `req~compiler-expressions~1`
- `req~compiler-arithmetic~1`

## Validation and source correspondence

`utest~compiler-expression-regressions~1`

[Native fixtures](../tests/ExprNative.lean) and their
[linked runner](../tests/test_expressions.py) exercise all constructors, malformed
sorts/positions/paths/spans, repeated support, shadowing, primitive observation
rejection, hidden unsafe branches, width/count/value bounds and singleton failures.
An exhaustive grid checks 882 width-4 addition/subtraction cases against direct
mathematical range tests. [Kernel witnesses](../tests/Expr.lean) check actual
interpreted denotations: two heads versus one target, integer extraction and empty
failure, strict undefined conjunction, defined false, subtraction order,
shadowing, vacuity, repeated maps, full integers and root/context preservation.
The normal inventory, native/import audit, axiom audit and kernel replay include
all new modules. Full repository checks still run the existing real comparison
tools; they do not claim Haskell/Alloy expression equivalence for this new API.

Sources S4/S5/S6 retain their [pinned revisions](sources.md). Upstream `Typing`,
`Support`, `Denotation`, `DenotationSupport`, `Integer`, `CollectionMeaning` and
`DenotationInvariance` supply the semantic declarations. Haskell `clafer.cf`
static productions and `Generator/Alloy.hs` (`genPExp'`, `genIFunExp`, `genOp`)
provide the supplementary constructor/order guide. Wider grammar operators and
Haskell bounded arithmetic do not override the adopted mathematical meanings.
The implementation and fixtures are original MIT project code; upstream definitions
and Haskell source are not copied. No dependency or trusted scope change is made.

Covers:
- `req~compiler-expressions~1`
- `req~compiler-arithmetic~1`

## Reuse decisions

The implementation reuses the pinned upstream typed core and denotation for all
meaning, including support congruence, lexical variables and integer extraction.
Those modules depend on mathematical sets and proof libraries; importing them
into the native runtime would violate the existing import boundary. The runtime
therefore has a finite annotated representation and an explicit proof-only bridge.
The existing structural IR supplies spans and diagnostics. Lean Std supplies
vectors, finite indices, list membership, folds and natural recursion; no new
container, equality or arithmetic library is introduced.

The accepted Alloy target's postfix fold was inspected as a traversal precedent.
For the source tree, cached structural budgets with erased proofs retain direct
constructor-to-constructor interpretation while using Std recursion and satisfying
the declaration audit. A general evaluator would require an additional agreement
proof and is unnecessary for this task's admission API, so upstream denotation is
used directly. No dependency or license cost is added.
