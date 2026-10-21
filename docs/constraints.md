# Source constraint elaboration

Selected [issue #18](https://github.com/kbak/clafer-compiler-lean/issues/18) follows
accepted declaration resolution #17 (PR #35) and typed expressions #14 (PR #32).
This work retains the authored parser boundary and the backend's independent
definedness, finite observation and overflow obligations.

## Reuse assessment

Before implementation, inspected `Frontend.Surface`, `Resolution.Candidate`,
the source attachment accessor, `IR.Expr.Term`, its checked typing/observation
API, and `SemanticsBridge.Expr.interpret`. Reuse these representations and checks.
The pinned upstream `Constraints.Support`, `Typing`, `DenotationSupport` and
`Examples.Telematics.Expressions` provide independent typed meanings and the
manual c01–c12 inventory, but consume resolved expressions and contain no
executable source elaborator. Their noncomputable semantic interpretation remains
outside the production import closure.

Inspected the pinned Haskell `ResolverName.hs` and `Desugarer.hs`, including local
bindings, contextual/inherited navigation and connective expansion. Their broader
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

Fresh-snapshot validation reached the final structural tests at the existing
deadline. Before changing scheduling, checked the accepted `check.sh` kernel/test
overlap and the accepted isolated unittest worker. Reuse the same Bash background
process and `wait` pattern for the whole-project axiom audit: it only reads the
completed build outputs, as kernel replay does. All three exit statuses remain
mandatory, and the gate regressions check overlap and failure propagation. This
adds no runner, dependency, cache of proof results or policy exception.

## Implementation and assurance plan

Construct a support table from original declaration/map identities, resolve names
and insert explicit navigation/coercions, expand the adopted sugar, then check
typing and finite observation. Successful elaboration must carry an independent
declarative derivation, including source owner and position. Test all twelve manual
Appendix 6 expansions, shadowing, ambiguity, wrong endpoints, counts and undefined
numeric extraction separately from the kernel proofs. Do not claim parser
correspondence, backend preservation, runtime singleton cardinality or overflow
freedom from frontend typing.

## API and lookup

`Frontend.Constraints.elaborate doc structural` consumes #17's
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
Unqualified names select the nearest lexical binder, then contextual fields
(including inherited fields and reference-target navigation), then enclosing
parent scopes, and finally a unique global user declaration. `this`, `parent`
and `dref` are special names; reserved spellings cannot bind local variables.
Root-context names use global extents. Dotted right operands use the selected
left collection as their navigation context; parentheses and collection operations
can group relative paths. Missing or ambiguous choices are errors.

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
ranges are still obligations for #15/#20. No bounded-UNSAT claim, source constraint
backend preservation, whole-AST construction, grammar/parser correspondence,
total elaboration or declarative uniqueness theorem is asserted. Standard finite
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

Nine regression groups cover all twelve bodies and attachment positions, changed
server/comparison/count/fixed operands, head versus target counts, large integer
and zero/many extraction obligations, binders and shadowing, all accepted operators,
wrong joins and ambiguity, CRLF/UTF-8 diagnostics, reference chains, inherited
common types, empty/multiple bodies, and generated inheritance/alpha-renaming/
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

The selected [source pipeline #20](pipeline.md) now retains these derivations
through encoding and composes their meaning with full source-model preservation.
Its primitive-carrier corrections and composed assurance await semantic review.
