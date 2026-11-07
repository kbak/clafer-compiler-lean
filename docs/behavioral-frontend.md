# Behavioral source frontend

The explicit `behavioral-0.5.7-candidate/v1` parser accepts authored behavioral
syntax and retains the original source. It is separate from the static parser
and from first-slice `behavioral-core/1` admission. The
[completion matrix](behavioral.md#complete-feature-and-evidence-matrix) retains
all C7 obligations. `parseAndElaborate` now constructs source model/check/run
requests for the implemented expression fragment. Full expression coverage,
whole-expression range composition and the independent authored-elaboration
correctness theorem remain outstanding. Parsing success is not successful
compilation or semantic admission.

## Authored syntax and grammar

[`Frontend.Behavioral.parseBehavioral`](../ClaferCompiler/Frontend/Behavioral/Parser.lean)
takes an explicit profile, logical filename and source string. It returns
[`Behavioral.Document`](../ClaferCompiler/Frontend/Behavioral/Surface.lean) or the
existing diagnostic schema. The document preserves the full input bytes, every
expression/element span, aliases, declaration headers, repeated modifier tokens,
guards, binder names and assertion-versus-constraint kind. Spans remain zero-based
half-open UTF-8 byte offsets into the original source, including CRLF and Latin-1
identifiers. The structural resolver is not run by this API.

The independent grammar below specifies the accepted source categories. `E27`
contains names, `noclafer`, natural literals and parenthesized `E0`; tighter categories
coerce to looser ones. Ordinary infix rows associate left. Transitions associate
right. The operand categories matter: a lower-precedence prefix needs parentheses
in a tighter context.

| Category | Productions / operand categories |
| --- | --- |
| `E0` | `E1 arrow E0`, or `E1` |
| `E1` | `quant [disj] names : E21` followed by a bar and `E1`; `if E1 then E1 else E1`; `let name = name in E1`; or `E2` |
| `E2` | `never`, `sometime`, `lonce`, `always` followed by `E3 scope`; `E3 must precede E3 scope`; `E3 must follow E3 scope`; `initially E3`; `finally E3`; or `E3` |
| `E3`–`E7` | `<=>`, `=>`, `\|\|`, `xor`, `&&`, respectively |
| `E8`–`E9` | `U`/`until`, `W`/`weakuntil`, respectively |
| `E10` | `X`/`next`, `F`/`eventually`, `G`/`globally` followed by `E10` |
| `E11` | `! E11` |
| `E15` | comparisons `=`, `!=`, `<`, `>`, `<=`, `>=`, `in`, `not in` |
| `E16` | `some`, `no`/`not`, `one`, `lone` followed by `E20` |
| `E17`–`E18` | `+`, `-`; then `*`, `/`, `%` |
| `E19` | `min E20`, `max E20` |
| `E20` | `sum E21`, `product E21`, `# E21`, `- E21` |
| `E21`–`E26` | `<:`, `:>`, `++`/comma, `--`, `**`, then `.`/`&` |

`quant` is `all`, `some`, `no`/`not`, `one` or `lone`. `names` is a nonempty
semicolon-separated name list. `arrow` is `-->`, `-->>`, `-[ E1 ]->` or
`-[ E1 ]->>`. `scope` is empty, `before E11`, `after E11`,
`between E11 and E11` or `after E11 until E11`. All six pattern rows in all five
scopes are retained as authored syntax; parsing does not replace their meanings
with the pinned Haskell expansions.

A declaration contains optional `abstract`, a list of `initial`, `final`,
`finalref` and `finaltarget` tokens, optional group, name, optional super/reference,
optional cardinality, optional `= E0`, optional `arrow E0`, and children.
Both reference-modifier orders and repeated tokens are legal. The selected
structural type positions remain single names. The use shorthand retains its
existing name/cardinality/children shape. Enums are top-level nonempty
`enum name = literal | literal ...` declarations. Properties are bracketed lists
of `E0`, optionally preceded by `assert`, at top level or within a declaration.
There is no new `scenario` keyword. `Elaborated.run` accepts additional bracketed
constraints with caller-selected attachment IDs from the elaborated model;
`Elaborated.check` selects an authored assertion by index.

Indentation and explicit braces follow the existing
[layout contract](parser.md). Tabs in leading indentation and inconsistent
indentation are malformed. Runtime strings/reals/doubles/Booleans, objectives,
backend escapes, directives, qualified module names and `:=` remain unsupported.
Profile rejection precedes lexing. Source negation stays in the tree; the parser
does not change assertion failure into source negation or move nested properties.

## Declaration and modifier binding

[`bindDeclarations`](../ClaferCompiler/Frontend/Behavioral/Declarations.lean)
expands enums using the C6 declaration constructors, retains a behavioral tree,
and projects declarations into the accepted structural resolver. Successful
results carry inductive `ExpandsList` and `ProjectsList` derivations as well as
the resolver's independent source/table correspondence and structural admission.
Enum literals acquire explicit `final` markers. The retained headers preserve
initializers, declaration transitions and every authored modifier token.

Properties keep their kind, owner, element/body positions, expressions and spans.
Inherited properties occur once at their authored attachment. The projection uses
empty structural constraint markers to request the integer universe for authored
expressions. Header expression markers are appended after existing children, so
they cannot shift those children's paths. These markers are not behavioral
constraints; expression interpretation always uses the retained behavioral tree.

[`bindModifiers`](../ClaferCompiler/Frontend/Behavioral/Modifiers.lean) checks the
exact ordered token-to-modifier correspondence, including repetitions.
[`effective` and `expansions`](../ClaferCompiler/IR/Behavioral/Modifiers.lean)
accumulate every modifier along validated ancestor lists and emit every required
placement/formula. The [modifier bridge](../ClaferCompiler/SemanticsBridge/Behavioral/Modifiers.lean)
proves correspondence with upstream `Modifiers.Effective` and, under
`Structural.Valid`, equivalence with model-wide `Modifiers.Holds`. Neither
reference-modifier order collapses to `final`. These results establish modifier
meaning independently of the still-missing full property elaborator.

[`headerProperties`](../ClaferCompiler/Frontend/Behavioral/Headers.lean) inventories
constant initializers in their enclosing scope and outgoing declaration transitions
at the declaration itself. Each result carries its declaration of origin, generated
expression, source span and a checked attachment rule. Initializers become
presence-guarded equations; they acquire no lifetime anchor. Transitions retain
`this` as their source, guards and the remainder of the chain. The original headers
and ordinary property inventory remain available separately. Source-to-generated
expression inventory is tested; the full composed source elaboration theorem is
still required.

## Executable reductions and proved boundary

[`IR.Behavioral.Surface`](../ClaferCompiler/IR/Behavioral/Surface.lean) supplies
resolved reductions. Patterns and transition chains are parameterized by atom
and domain families; modifiers retain the total-set specialization. These are library operations on resolved formulas; the source synthesizer below
uses them after resolving their operands.

| API | Behavior | Proof in [`SemanticsBridge.Behavioral.Surface`](../ClaferCompiler/SemanticsBridge/Behavioral/Surface.lean) |
| --- | --- | --- |
| `Patterns.expand` | All 30 accepted pattern/scope cells, including response-between and first-opener precedence-after | `Patterns.expand_interpret`, `expand_agrees`, `normalized_agrees` |
| `Transitions.sequence`, `expand` | First link conditional; subsequent sources/guards required; eventual persistence excludes entry guards | `Transitions.sequence_interpret`, `expand_interpret`, `expand_agrees` |
| `Transitions.declaration` | Retains `this` as source and context | `Transitions.declaration_interpret` |
| `Modifiers.expand` | Distinct initial, final, finalref and finaltarget placements/formulas; captured views and explicit self-survival | `Modifiers.expand_interpret`, `expand_agrees` |

Interpretation theorems establish exact equality with the accepted upstream
syntax transformations. Pattern/transition agreement then uses the independent
upstream interval/sequence meaning, for arbitrary signs, times, environments and
observations. Pattern normalization uses the existing executable normalizer and
its size witness. Modifier meaning agreement additionally requires the upstream
`Structural.Valid` premise; inherited reference observation comes from that
source interface. No source/target satisfaction assumption is hidden in syntax
agreement. The
[generic surface bridge](../ClaferCompiler/SemanticsBridge/Behavioral/GenericSurface.lean)
provides the same pattern and transition interpretation for partial atom/domain
families. These results do not establish source expression resolution,
whole-document elaboration, target translation or native execution correctness.

The raw authored bodies remain available for strict definedness. The
[upstream partial-domain contract](behavioral.md#bounds-arithmetic-and-outcomes)
requires retaining the original expanded formula's `Defined` predicate alongside
normalized truth. The C6 initializer/range obligations still require composition
with authored expression elaboration.

## Partial primitives and grouped counting

[`FormulaF`](../ClaferCompiler/IR/Behavioral/Syntax.lean) parameterizes the original
executable normalizer by atom/domain families. The original `Formula k n` remains
its total-set specialization, and original admission still excludes partial atoms.
[`Primitive`](../ClaferCompiler/IR/Behavioral/Primitive.lean) represents the accepted
collection/integer expressions, distinct coercion/extraction, extrema and
occurrence-indexed folds. Its `Normalized` record retains the original tree and
the normalized truth with their correspondence proof. The
[generic normalization theorem](../ClaferCompiler/SemanticsBridge/Behavioral/Formula.lean)
establishes signed satisfaction as original strict definedness plus normalized
truth for arbitrary partial observations; the
[primitive bridge](../ClaferCompiler/SemanticsBridge/Behavioral/Primitive.lean)
instantiates the theorem with the pinned primitive syntax. No missing arithmetic
result becomes zero or a Boolean value.
`Primitive.constantInitializer` has exact interpretation equality with upstream
`Initializers.constant`; `initializer_truth` reuses its presence-guarded equation
under explicit operand-definedness premises. This resolved theorem does not resolve
the source header's head/value views or prove their typing.

[`Grouped.Atom.count`](../ClaferCompiler/IR/Behavioral/Grouped.lean) retains a
complete `one`/`lone` body, arity, outer-domain expression and disjointness flag
behind the raw-body barrier. Its
[proof interpretation](../ClaferCompiler/SemanticsBridge/Behavioral/Grouped.lean)
reuses upstream `Quantifier.eval` on ordered `Fin arity` assignments, primitive
domain evaluation and upstream `Defined`/`raw`. Every admissible assignment must
have a defined body, including assignments where it is false. Captures extend
the environment without changing `this`; lexical index zero denotes the last
authored binder. The interpretation uses `U : Type` for identity carriers and
proof-only function atoms; those atoms never enter the native import closure.
Normalization preserves the grouped observation and original definedness.

[`Frontend.Behavioral.Binders`](../ClaferCompiler/Frontend/Behavioral/Binders.lean)
retains named lexical slots and anonymous generated slots. Successful lookup carries
the nearest-binding rule and original token. A checked group plan rejects empty,
duplicate or reserved binders, permits nested shadowing and indexes the exact
supplied outer context and binder list. Its new locals precede one hidden domain
capture and then the shifted outer captures.

[`IR.Behavioral.Binders.elaborate`](../ClaferCompiler/IR/Behavioral/Binders.lean)
captures the shared domain once with `letSet`. Repeated `all`/`some` use that
capture; `no` negates the grouped existential. Disjoint domains remove previously
chosen identities before body evaluation. `one`/`lone` use the single ordered-tuple
counting atom. The [binder bridge](../ClaferCompiler/SemanticsBridge/Behavioral/Binders.lean)
proves the exact domain exclusions, retained domain/outer captures and unchanged
attachment identity, and the counting interpretation. Native tests exercise group
lowering and shadowing. The source synthesizer below uses this lowering; the general composed
authored-binder meaning theorem remains required.

This grouping rule is a compiler composition of upstream primitives with the
adopted Alloy assignment rule. It is not an upstream authored-binder elaboration
theorem. The source synthesizer below wires the supported typed expressions into this
representation; complete source correspondence remains required.

## Resolved properties and requests

[`Properties.Model` and `Request`](../ClaferCompiler/IR/Behavioral/Properties.lean)
keep model constraints, assertions and scenario additions distinct. A check
selects an existing assertion by a bounded index; a run supplies extra constraints.
Scenario extension retains every model constraint and the assertion inventory.
The [property interpretation](../ClaferCompiler/SemanticsBridge/Behavioral/Properties.lean)
uses upstream `Properties.Model.behavioral`, `Asserts` and `Possible`. It proves
scenario-extension correspondence and reuses the theorem that assertion failure
is classical negation of the complete interpreted property, including its strict
domain. Every constraint preserves its root or nested declaration attachment.
These resolved APIs assume an explicit atom/domain interpretation and observation.
The source adapter below supplies their syntax; target command execution remains
separate.
`Grouped.syntaxObservation` keeps formula syntax fixed while observations vary
with the candidate trace. `syntax_satisfaction` proves equivalence to the recursive
counting interpretation. Its generic pullback proof preserves raw truth, signed
truth and strict definedness; a model uses the inherited-reference observed trace.

## Authored expressions and document requests

[`Values`](../ClaferCompiler/Frontend/Behavioral/Values.lean) resolves nearest
captured locals, contextual fields, enclosing scopes and unique global names.
Field selection reuses the static independent `Field`/`Global` predicates;
reference ownership uses the behavioral structural analysis. A reference cycle
without a reachable target field still permits unique global-name lookup.
`this.parent`
retains direct fixed-identity navigation, while navigation from an observed set
uses an ordinary step. The typed result distinguishes object heads, integer
sets, integer scalars, empty sets, formulas and unexpanded transition chains.
Implicit value conversion performs one inherited dereference. Arithmetic then
uses D3 finite-set coercion, while presence and cardinality inspect heads.

[`Expressions.synthAt`](../ClaferCompiler/Frontend/Behavioral/Expressions.lean)
composes these values with the existing partial primitives, capture plans and
surface reductions. It preserves negation until normalization. A chain is retained
until its enclosing formula is needed, so only its first source is conditional.
All thirty pattern/scope cells and Boolean conditionals use their accepted
reductions. `let` captures a complete collection; grouped quantifiers resolve
the domain before introducing names and retain the hidden domain slot.
`sum`/`product` split syntactic union operands into separate occurrence folds,
using strict singleton target extraction per head. Ordinary arithmetic instead
coerces the distinct target set. Missing values remain partial operations.
`Operands` independently specifies syntactic union splitting; each successful
`operandsAt` result carries its source derivation. Insufficient traversal fuel
produces a diagnostic and cannot collapse an unvisited union subtree into one
occurrence family. This local source rule does not prove complete expression
elaboration or aggregate evaluation agreement.

[`parseAndElaborate`](../ClaferCompiler/Frontend/Behavioral/Elaborate.lean) runs
parsing, declaration/modifier binding and expression elaboration for every
property and generated header equation/transition. Its result retains the source
document and full occurrence inventories, with body vectors indexed by their
lengths. `Elaborated.model` separates assertions from constraints and appends
header constraints. `authored_owner` proves that each emitted authored property
retains its source owner, kind, body slot and span; this is an attachment theorem,
not a source-expression correctness theorem.

`Elaborated.check` rejects an out-of-range assertion index. `Elaborated.run`
resolves additional scenario constraints against the same declaration table,
retaining their caller-selected attachment and authored anchors. It rejects
assertions in scenario input instead of promoting them to constraints. Scenario
objects must already be declared in the model. These APIs construct requests;
they do not execute a target solver or widen the static CLI.

The [native source tests](../tests/test_behavioral_elaboration.py) cover all thirty
pattern/scope forms, guarded chains, inherited integer references, repeated
aggregate operands, shadowing, captures, direct versus observed `this`, strict
undefined operands, header attachments, checks/runs and located diagnostics.
Expression synthesis is currently tested, not proved against an independent
complete source judgment. The following accepted cases still require implementation:

- Scalar and collection conditionals, including strict branch definedness.
- Relation restrictions (`<:`, `:>`), heterogeneous collection types and actual
  parent typing for parentless abstract views.
- General typed navigation over partial collection expressions and polymorphic
  navigation from emptiness.
- Composed authored-expression correctness, grouped-binder meaning and complete
  intermediate range obligations.

These cases produce diagnostics rather than successful compilation; they remain
C7 obligations. Successful construction of an IR model is not full-profile
qualification or independent semantic acceptance.

## Reuse and evidence

The existing lexer supplies Latin-1 scanning, comments, original spans and typed
diagnostics. `lexWith` parameterizes its exclusion predicate; static `lex` and
`lexStep` retain their exact policy. Existing `Cursor`, `StateT`, layout helpers,
cardinality parsing and `Nat.repeat` supply the parser framework. A separate AST
retains constructs which the static AST cannot represent. Std containers suffice;
Parsec's partial `many` and a new BNFC runtime dependency would not meet the
existing audit and native import boundaries. No package or license dependency is
added.

The source grammar and `Desugarer.hs` at the pinned Haskell candidate were checked
for categories, arrows, enum placement, modifier lists and syntax erasure. The
accepted upstream `Patterns`, `Transitions` and `Modifiers` equations are adapted
with MIT attribution in the runtime module; their mathematical meanings remain
upstream. Existing compiler normalization is generalized, preserving its original
specialization. `PrimitiveExpression` supplies the primitive constructors;
`StaticObservation`/`CapturedStatic` supplies existing relation-expression
interpretation, but its historical extraction and singleton common-domain
agreement cannot replace D3 coercion/folds or arbitrary set captures. The native
C6 arithmetic operations remain available for runtime arithmetic. Grouped counting
uses the generic atom interface because repeated unary counts and Boolean
rewriting before signed normalization are unsound. No trace evaluator or new
library is introduced by that interpretation.
Binder plans reuse `Vector`, `Fin`, the existing reserved-name policy and checked
`Nat.rec` traversal. A hidden domain capture avoids introducing a separate syntax
renaming framework. The header adapter follows the existing C6 initializer sugar
and upstream `Initializers.constant`; its distinct AST and attachment provenance
prevent passing temporal expressions through the static parser or resolver.
The [source register](sources.md#behavioral-frontend-sources) records exact pins.

[Native parser tests](../tests/test_behavioral_parser.py) check all pattern/scope
cells, anchors/signs, every pair of infix operators, arrows/chains, multiple/disjoint
binders, modifier order/repetition, attachment shape, layout, byte spans and typed
failures. The live pinned exporter checks representative syntax. Its `LetExp`
desugaring crash is retained as a tool failure, not compilation or meaning
agreement. [Native reduction tests](../tests/test_behavioral_surface.py) exercise
guard placement, both corrected expansions and distinct reference views without
proof imports. The kernel-checked
[binder counterexample](../tests/BehavioralSurface.lean) demonstrates that tuple
uniqueness differs from naive nested uniqueness. Grouped binders use Alloy's
complete ordered assignments: `one` counts exactly one satisfying assignment,
`lone` at most one, and `no` excludes every satisfying assignment. `disj`
restricts those assignments to distinct identities; it does not identify
permutations. Explicitly nested quantifiers retain their authored meaning.
The shared domain is resolved before introducing the group's variables. Counting
must preserve the accepted raw-body barrier and strict definedness; ordinary
repeated unary `one`, `lone` or `no` is not a valid elaboration. The upstream
unary definitions remain unchanged. The source register records the agreement
between Alloy, the Haskell translation and the papers; the composed source and
temporal proof remains an implementation obligation.

[Native declaration tests](../tests/test_behavioral_declarations.py) cover enum
finality, both modifier orders, repetitions/inheritance, retained header
expressions and property ownership. [Native primitive tests](../tests/test_behavioral_primitive.py)
exercise the original-domain retention and grouped raw-body barrier without
proof imports. [Kernel examples](../tests/BehavioralPrimitive.lean) distinguish
joint uniqueness and disjoint ordered assignments from incorrect alternatives.
[Native binder tests](../tests/test_behavioral_binders.py) exercise shared-domain
capture, disjoint exclusions, outer captures, nested shadowing and joint counts.

Grammar recognition and token/AST correspondence remain tested boundaries.
Independent semantic review, complete authored elaboration coverage and its
correctness/range composition remain required; this API inventory does not close C7.
