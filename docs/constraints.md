# Source constraint elaboration

The source constraint elaborator consumes [resolved declarations](resolution.md)
and produces [typed static expressions](expressions.md). It retains authored
source locations and the backend's independent definedness, finite-observation
and overflow obligations.

## Reuse assessment

The elaborator reuses `Frontend.Surface`, `Resolution.Candidate`, the source
attachment accessor, `IR.Expr.Term`, its checked typing/observation API, and
`SemanticsBridge.Expr.interpret`.
The pinned upstream `Constraints.Support`, `Typing`, `DenotationSupport` and
`Examples.Telematics.Expressions` provide independent typed meanings and the
manual c01–c12 inventory, but consume resolved expressions and contain no
executable source elaborator. Their noncomputable semantic interpretation remains
outside the production import closure.

The pinned Haskell `ResolverName.hs` and `Desugarer.hs` provide comparisons for
local bindings, contextual/inherited navigation and connective expansion. Their broader
language and Haskell runtime are comparison references, not production dependencies.
Lean's existing macro elaborator resolves Lean syntax and namespaces; it does not
implement Clafer's reference heads, inherited field views or partial integers.
Standard `List`, `Vector`, `Except` and natural-number iteration supply the finite
traversal machinery. No additional graph, parser or symbol-table package is needed.
Ancestry predicates inspect the standard optional endpoint directly, avoiding
finite searches over identities that cannot be that endpoint; their decisions
remain derived from the declarative predicates.
The existing native harness and upstream constructor laws are reused. No dependency
or license changes, copied semantic definitions, or Haskell source redistribution
are needed; new compiler code remains MIT and existing Lean primitives Apache-2.0.

<a id="implementation-and-assurance-plan"></a>

## Elaboration stages

The elaborator constructs a support table from original declaration/map identities,
resolves names, inserts explicit navigation/coercions, expands the adopted sugar,
and checks typing and finite observation. Successful elaboration carries an
independent declarative derivation, including source owner and position. Frontend
typing alone does not prove parser correspondence, backend preservation, runtime
singleton cardinality or overflow freedom.

## API and lookup

`Frontend.Constraints.elaborate doc structural` consumes the resolver's
`Resolution.Elaborated doc` and returns every original body paired with its
`Occurrence`. Each occurrence records owner, bracket-group index and body index;
its expression and spans are accessed from the unchanged source document. Results
are ordered by owner preorder (root first), then group and body. Empty groups
remain in the document and contribute no body; conjunction of zero bodies is true.
Inherited attachments are retained once on their original owner, without cloning.

Each `Attached` contains a `Layout` and a `Body`. The layout uses the original
class IDs and actual containment/head, parent, dereference and super maps. Its
checked `Resolved` predicate equates class/primitive annotations with the core and
proves every map's owner and endpoints belong to the actual structural table.
Parentless abstracts have global extents and no fabricated root parent. The body
contains the existing `IR.Expr.Checked` Boolean term and a source derivation.
`elaborateBody`/`synthAt` are lower-level APIs; callers using custom supports must
supply their support-to-table agreement separately.

The independent rules are in `ConstraintsRules`: `Field`, `NameRule`, `Navigate`,
`ScopePath`, `Coerces`, `UnaryRule`, `BinaryRule`, `QuantifierRule`, and `Elaborates`.
They do not call candidate construction. A field selects the unique declaration
at the nearest super level; direct fields shadow inherited fields. Navigation
checks a reference head's fields before following its target, preserving
`cache.size.fixed`. Explicit `parent` and `dref` retain their map roles.
Unqualified names select the nearest lexical binder, then the context's own or
inherited field, then fields in enclosing parent scopes from nearest to farthest,
then a field of the original context's reference target, and finally a unique
global user declaration. The target fallback includes inherited fields and
finite reference chains starting from that target. It does not inspect reference
targets of ancestors or descendant fields.
This [adopted precedence](sources.md#constraint-name-lookup-policy) follows the
Haskell compiler's ancestor-before-target order, deliberately differing from
SoSyM Appendix 4's Targets-before-Ancestors order.

`this`, `parent` and `dref` are special names; reserved spellings cannot bind local
variables. Root-context names use global extents. Dotted right operands use the
selected left collection as their navigation context; `this.field` can therefore
select a target field even when an enclosing scope has that name. Explicit
`this.dref.field` starts from the dereferenced target, while `parent.field` starts
from the parent. Qualified navigation retains the existing finite reference-chain
traversal and cycle diagnostic. Parentheses and collection operations can group
relative paths. Missing or ambiguous choices are errors.

The selected field lookup checks immediate children at the nearest super level.
It does not implement Haskell's general breadth-first descendant search or all
of its global lookup/ambiguity rules. The precedence agreement is bounded by this
existing frontend contract; the exact nested-abstract example in the upstream
issue is also outside the selected declaration domain.

Raw synthesis and context-directed adaptation are distinct judgments. Counts and
`some`/`no`/`one`/`lone` consume raw collections, so numeric reference heads are
not silently dereferenced there. Boolean adaptation inserts exactly `0 < #E`.
Numeric adaptation follows explicit dereferences and inserts `integerOf` only at
an integer class. Equality uses dereferenced values, extracts integer operands,
and widens object operands along actual super paths to a common class. Set
operations first retain matching head types or a common super; when those cannot
match, they try reference values. Explicit `.dref` selects target collections.
No heterogeneous equality by display name, arbitrary casts, or scalar join is
accepted. The full adopted sugar equations are the rule constructors, including
strict partial disjunction/xor/implication/equivalence and swapped comparisons.

Binders get fresh IDs above the active environment's IDs and positional lookup.
Their domain is elaborated before pushing the binder, and the body retains the
original `this`. Single-object universal, existential and no/not binders are
accepted; the existing finite-observation checker rejects infinite primitive
extent observation. Distinct lexical positions survive shadowing.

## Empty collection literal

The reserved spelling `noclafer` avoids taking `none`, which remains available
for existing declaration and binder names. Alloy output uses its native `none`.

`noclafer` is reserved and denotes a defined empty unary collection. Its bottom
element type is instantiated at the other collection operand before ordinary
reference/value adaptation. Thus `a = noclafer` tests the collection of reference
heads for emptiness, even when `a` refers to integers; it does not extract an
integer. Explicit `a.dref = noclafer` tests the target collection. Unrelated element
classes need no invented common superclass to combine with this literal.

Standalone `#noclafer`, `no noclafer`, `noclafer = noclafer` and empty quantifier domains use an
arbitrary context element annotation with no extent observation. The resolved
core remains monomorphic: `Syntax.EmptyUnary` recognizes the literal through
source locations; computed collections keep their resolved types and strict
definedness. This is contextual instantiation, not a general polymorphic type
inference system. Integer extraction from an empty integer collection remains
undefined; a bare literal is not adapted to a scalar or binary relation.

For `noclafer.field`, the elaborator tries the right operand in each supported
element context with an empty receiver. Exactly one successful context is
required. Missing and ambiguous navigation remain errors. Existing set operations,
counts, multiplicities and quantifiers then use their ordinary meanings, including
vacuous universal truth. General conditionals and the full Haskell ResolverRoot
transformation remain outside the selected source language. See the
[source decision](sources.md#empty-collection-extension) and
[typed representation](expressions.md#empty-collection-typing-and-preservation).

## Meaning and proof boundary

`SemanticsBridge.Constraints.Meaning` is a relational source denotation: an
independent source-rule derivation into typed syntax followed by the pinned
partial expression denotation. It contains no executable elaborator call,
source/target satisfaction premise, or backend translation. The public results
are:

- `body_sound` and `success`: source derivation, lexical/type checks and finite
  observation admission for the returned term.
- `denote_sound`: the returned expression's independent denotation is an admitted
  source meaning, including undefined results. This is not a uniqueness theorem
  for all possible declarative derivations.
- `attached_owner` and `attached_maps`: original context and actual map incidence.
- `occurrence_coverage` and `attachments_preserved`: every original body occurs
  and successful traversal preserves the complete ordered occurrence list.
- `boolean_coercion`: Boolean adaptation cannot dereference before counting.
- `implicit_some`: the emitted cardinality expansion has the pinned nonempty-set
  meaning under the explicit finite-operand assumption.

`IR.Expr`'s existing interpretation supplies every typed constructor and lexical
binding. Runtime imports remain Std/project-only; the denotation and proofs remain
in `SemanticsBridge`. Singleton extraction, finite operand realization and target
ranges are handled by [constraint encoding](expression-encoding.md) and the
[source pipeline](pipeline.md). These frontend results alone do not establish
bounded UNSAT, backend preservation or whole-AST construction. Grammar/parser
correspondence, total elaboration and declarative uniqueness remain unproved. Standard finite
iteration is bounded by the declaration count; source traversal uses the original
byte length plus one. Manually built trees exceeding that budget fail explicitly;
there is no proof that every valid manually built document will succeed.

## Diagnostics and validation

The first failing owner/group/body is reported, with recursive operands visited
left to right. Diagnostics retain phase `type`, original UTF-8 span and one-based
line/scalar column. Codes distinguish missing/ambiguous names/navigation, absent
parent or dereference, incompatible endpoints, noncollection/binder domains,
reserved binders, unsupported operators/quantifiers, primitive observation,
traversal exhaustion and internal certificate failure. The unchanged parser can
reject an excluded surface form before elaboration. Diagnostics do not report
source contradictions as malformed or claim anything about satisfiability.

`tests/ConstraintsInventory.lean` independently projects the pinned upstream
manual c01–c12 trees and kernel-checks the expected trees. This proof-only test
privately imports the typed recursor and standard numeric printers' implementations
for closed reduction; kernel replay and axiom auditing still apply. Native tests compare
automatic elaborations against that checked inventory after erasing only source
locations and identity widenings. Resolved IDs, map roles, super paths, operators,
operand order and head counts remain in the comparison. The original fixture
reconstructs the selected declaration/body inventory; no Haskell source is copied.

Regression groups cover all twelve bodies and attachment positions, changed
server/comparison/count/fixed operands, head versus target counts, large integer
and zero/many extraction obligations, binders and shadowing, all accepted operators,
wrong joins and ambiguity, CRLF/UTF-8 diagnostics, reference chains,
ancestor/target precedence, original-context target fallback, inherited common
types, empty/multiple bodies, and generated inheritance/alpha-renaming/
parenthesis cases at depths 1–12. These are finite native searches, not completeness
proofs. Tool/source hashes, inputs, native output and comparison receipts are
retained outside source by the existing harness workflow. The unchanged full check
also exercises the pinned Haskell/Alloy tools; it is not an M2 Haskell semantic
agreement claim.

## Trace links

`impl~compiler-constraint-elaboration~1`

[Rules](../ClaferCompiler/Frontend/ConstraintsRules.lean),
[support](../ClaferCompiler/Frontend/ConstraintsSupport.lean),
[names](../ClaferCompiler/Frontend/ConstraintsNames.lean),
[coercions](../ClaferCompiler/Frontend/ConstraintsCoercions.lean),
[operators](../ClaferCompiler/Frontend/ConstraintsOps.lean), and
[elaboration](../ClaferCompiler/Frontend/Constraints.lean) implement the checked API.

Covers:
- `req~compiler-constraint-elaboration~1`
- `req~compiler-diagnostics~1`

`proof~compiler-constraint-elaboration~1`

The [proof bridge](../ClaferCompiler/SemanticsBridge/Constraints.lean) supplies the
source derivation, denotation and attachment results above. The
[manual inventory](../tests/ConstraintsInventory.lean) kernel-checks the reference
projection. [Native tests](../tests/ConstraintsNative.lean) and
[regressions](../tests/test_constraints.py) exercise automatic elaboration separately.

Covers:
- `req~compiler-constraint-elaboration~1`

The [source pipeline](pipeline.md) retains these derivations through encoding
and composes their meaning with full source-model preservation.
