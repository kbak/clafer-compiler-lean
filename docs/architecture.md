# Structural compiler contract

This contract defines the selected structural language, interfaces, independent
meanings and assurance obligations. The
[structural roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) retains
delivery dependencies and acceptance history.

The [source pipeline](pipeline.md) implements the integrated source command;
the [qualification inventory](qualification.md#feature-and-evidence-inventory)
links supported features to their contracts and evidence. The theorem shapes
below are specifications. Component contracts state the exact proved boundaries,
while [requirements](spec.md) record the compiler and workflow obligations.

## Ownership and dependencies

Use a separate Lake package with one-way imports:

```text
ClaferCompiler -> Clafer -> FormalCD -> DPGraph -> Mathlib
```

Upstream owns independent mathematical meanings, accepted paper corrections,
reusable structures and lemmas. Compiler-specific efficient representations,
frontend, target semantics, translation and assurance live downstream. Interpret
executable structures into upstream definitions; do not copy those definitions
or expect noncomputable functions to become native compiler code. A direct proof
from source meaning to Alloy is allowed; constructing DP graphs at runtime is
not required. Generic DPGraph/FormalCD universes must not be restricted to finite
ones to accommodate the backend.

Module ownership is binding. The [build contract](build.md) records the module
roots and their permitted import boundaries.
Each owner delivers implementation, proofs where promised, positive/negative
fixtures, exact declaration names, source-matched evidence and unresolved limits.

| Module/responsibility | Contract | Evidence and boundary |
| --- | --- | --- |
| Lake, root module, check/CI and proof audit | [Build](build.md) | Native smoke run, module inventory, kernel/axiom audit, reviewed check scope |
| External comparison tooling and corpus | [Oracles](oracles.md), [comparison](comparison.md) | Pins, same-generation Haskell receipt, exact-candidate replay and mutation sensitivity |
| `ClaferCompiler/IR`, `SemanticsBridge` | [Structural IR](ir.md), [expressions](expressions.md) | Validated executable data, upstream interpretation, admission/denotation agreement |
| `Backend/Alloy` syntax/semantics/printer | [Target core](alloy-core.md), [serialization](alloy-text.md) | Independent finite meaning, scopes, hygiene, syntax correspondence |
| `Backend/Alloy` translation and `Correctness` | [Structural encoding](structural-encoding.md), [preservation](structural-correctness.md), [inherited realization](inherited-realization.md), [constraints](expression-encoding.md) | Concrete model relations, soundness and bounded completeness |
| `Frontend` parser/resolver/elaborator | [Parser](parser.md), [resolution](resolution.md), [constraints](constraints.md) | Source spans, authored provenance, declarative elaboration relation and success proofs |
| `Driver`, instance decoder and integration | [Decoding](comparison.md), [CLI](cli.md), [source pipeline](pipeline.md), [qualification](qualification.md) | Stable protocol, actual Alloy integration, complete telematics, candidate artifacts/benchmarks |

New work follows the roadmap's dependencies and explicit manual selection. Shared
IR/target changes require coordination and review of the affected contracts.

## Feature matrix

The matrix has three delivery columns. M2 includes M1. Every accepted row inherits
the proof and positive/negative test obligations above. The detailed
constructor/surface tables below close the M2 inventory. Sources S1–S8 refer to
[pinned source locators](sources.md#source-locators).

| M1: guarded effective structural core | M2: static constraints, inherited realization, text frontend | Explicitly deferred/rejected |
| --- | --- | --- |
| Resolved declaration IDs, separate names/origins, finite containment, root and parent/super ranks (S1) | Authored/default provenance, lexical/global lookup, forward references, layout and spans (S2/S5) | Import/module system, guessed resolution, declaration identity from display names |
| Effective valid local/group intervals, unbounded upper marker, concrete group counts as unions of child heads (S1) | Keyword/numeric defaults, inherited group overrides, ordinary-field group enforcement (S2/S3) | Automatic scope inference; silently replacing authored defaults with Haskell behavior |
| Parentless leaf abstract basics with unrestricted bounds, or zero bounds only for unused abstract chains; basic inheritance into abstract basics (S1) | Selected ordinary inherited fields and explicit abstract families with realization ranks (S3) | Explicit nested abstract types, concrete superclasses, unequal-parent refinement, relocation, reference-super/target narrowing |
| Direct user-class set/bag references on concrete declarations, including cyclic references; occurrence identity retained (S1) | Selected parented integer references and inherited views of the same objects/links (S3/S4) | Parentless abstract references, expression-valued reference targets, arbitrary reference inheritance |
| Constraint-free; global root, abstract cover, ownership, group and declaration-disjointness obligations (S1) | Every core constructor and selected hard-constraint surface form below (S4/S5) | Dropping constraints to obtain M1; treating assertions or goals as hard constraints |
| No runtime primitives; numeric bounds/cardinalities still need checked bitwidth (S1/S7) | Mathematical integer observations with finite domains, definedness and no-overflow policy (S4) | Runtime string/real/double/Boolean domains, enums, infinite primitive-extent observation, general aggregation |
| Resolved-IR API and native CLI | Source frontend, integrated source CLI and all Appendix 6 declarations/c01–c12/final selections at M3 | Production Haskell dependency; blanket full-Haskell compatibility |
| Static Alloy only (S7) | Same static target with selected integer/constraint constructs | Behavior, temporal operators/modifiers/transitions, backend escapes, optimization goals, other backends and post-SoSyM extensions |

### Exact M1 admission

Use S1's `Clafer.Semantics.EffectiveCore.WellFormed` **and** `Supported`, with
`Clafer.Verification.coreChecks` / `supportChecks` and the
`admitted_wellFormed`, `admitted_supported`, `certificate_exists` theorems as the
reference admission contract. This is an exact domain, not a list of examples:

- Unique resolved IDs; exactly one synthetic root, basic/concrete/parentless with
  no super; finite decreasing parent/super ranks; valid local and group ranges;
  other parentless declarations abstract. Only root/user origins occur.
- Every abstract is parentless, basic, without containment children, with group
  `0..*`. Its local slot is `0..*`, or `0..0` with no concrete super-descendant.
  Leaf means no children; abstract subtype chains are allowed.
- Every super target is abstract and every extending declaration basic. Reference
  targets are user declarations. No reference declaration participates as a subtype.
- Positive group lower bounds require at least one child declaration. Empty
  default groups are admitted; zero realized children is still a candidate outcome.
- There are no primitive origins or constraint bodies. No undocumented combinations
  beyond `Supported` are admitted. Invalid auxiliary certificates are not UNSAT;
  a native validator can compute ranks rather than require them from users.

The syntactic guard does not assume candidate satisfaction. Reference cycles are
legal; parent/super cycles are malformed. Overlapping unrelated candidate extents
remain representable negative cases; satisfaction enforces declaration disjointness.
Set references enforce uniqueness per owner/target; bags may repeat a target through
separate head objects. Counting heads, links and distinct dereferenced targets are
three different operations. The [IR bridge](ir.md) proves agreement in both
directions with admission. The [structural proofs](structural-correctness.md)
preserve all global obligations.
Haskell capture adds receipt/option restrictions for comparison; those are not
extra semantic restrictions on the compiler's own IR API.

### M2 typed core: exhaustive constructor inventory

S4 is the authority for meanings. The [expression API](expressions.md),
[encoding](expression-encoding.md) and [source elaboration](constraints.md) state
their respective implementation and proof boundaries. Every row needs
positive and rejecting/violating examples, including undefined cases where relevant.
`Expr` below is `Clafer.Constraints.Expr`; the corresponding executable representation is
`ClaferCompiler.IR.Expr.Term` with `Checked` typing evidence.

| Accepted constructor(s) | Meaning and boundary | Surface route |
| --- | --- | --- |
| `boolean`, `integer` | Boolean values; mathematical integer constants | IR Booleans; decimal integer literal and unary minus. No new Boolean keyword syntax is implied. |
| `this`, `extent`, `var` | Context singleton, resolved global extent, lexical-position singleton | `this`, resolved name, binder name; parentless abstract extents are global, never fake root children |
| `map`, `image`, `join` | Resolved binary map, unary image, binary composition | Typed paths and `.`; parent/child/dereference steps resolved explicitly; internal binary map terms need no new surface keyword |
| `and`, `not` | Strict partial Boolean conjunction/negation | `&&`, `!`; selected derived connectives below |
| `equal`, `less` | Same-sort equality including sets/relations; integer comparison | `=`, `<`, derived comparisons below |
| `arithmetic` with `add`, `subtract` | Mathematical addition/subtraction | `+`, `-`, unary minus as `0 - e` |
| `integerOf` | Exact singleton extraction from a realized integer collection | Explicit IR conversion inserted for numeric navigation; empty/multiple/off-domain is undefined |
| `cardinality` | Finite unary-set or binary-relation cardinality | `#`; counts heads before dereferencing, targets after it |
| `setOp` with `union`, `difference`, `intersection` | Ordinary set/relation operations of matching shape | `++`, `--`, `**`; intersection is the corrected ordinary intersection |
| `subset` | Same-shape inclusion | `in`, derived `not in` |
| `widenObjects`, `widenRelation` | Identity-preserving inclusion on objects/endpoints | Checked elaborator coercions along actual super paths; no casts by name |
| `all` | One fresh resolved binder over a finite object collection; nested binders may shadow names | `all x : E` followed by a bar and body; selected existential/no forms below |

Support vertices/maps, owners, operand order, attachment occurrences, fresh binder
IDs and outer domains must survive elaboration. No tuple/higher-arity or relation
binder is added. Literal-only constraints use direct denotation; do not add dummy
maps to meet upstream `Compile.Input`'s positive-map-support condition.

### M2 surface forms and explicit exclusions

This is a whitelist against the pinned Haskell `src/clafer.cf` (S5), not adoption
of that entire grammar. Preserve its precedence/associativity for retained
productions and parentheses; the [parser contract](parser.md) records an
independent grammar for this subset.
The paper locators and selected corrections in S2–S4 control meaning.

Retain the pinned `PosIdent` shape (a letter followed by letters, digits,
underscore or apostrophe), decimal `PosInteger`, and line/block comments. The
parser must pin the lexer character classes and test Unicode rather than silently
narrowing names to ASCII. Preserve original spelling without Unicode
normalization; repeated names in different contexts are legal. Reserved primitive
names/aliases and the synthetic root are classified explicitly by the resolver, never
allocated as ordinary user declarations. Escapes and option directives are
recognized for rejection even where the reference lexer treats them as comments.

| Accepted production/form | Elaboration/validation contract |
| --- | --- |
| `Module`, `ElementDecl`, `Clafer`, `Subclafer`; empty/list elements | declarations with indentation layout or explicit braces, comments and blank lines; reject inconsistent layout and tabs in indentation |
| `AbstractEmpty` / `abstract`; empty super / `: Name` | preserve authored/effective flags; super is one resolved parentless abstract basic in the selected realization domain |
| `ReferenceEmpty`, `-> Name`, `->> Name` | direct class target or `integer`/`int` alias to the canonical integer primitive; no arbitrary target expression |
| Empty group; `xor`, `or`, `mux`, `opt`, `n..m`, `n..*` | bounds respectively `1..1`, `1..*`, `0..1`, `0..*`; retain keyword provenance |
| Empty card; `?`, `+`, `*`, `n`, `n..m`, `n..*` | valid nonnegative intervals; omitted parented card follows upstream `Defaults` |
| `ClaferUse` backtick plus a single resolved type name, card and body | the Appendix 6 use shorthand creates a local declaration extending that type; no import/module-qualified use |
| `Constraint`, `Subconstraint`: square-bracketed hard bodies, local or global | preserve each body and owner occurrence; multiple bodies conjoin, empty list means true |
| `ClaferId`, `Name` with one `ModId`, `EInt`, parentheses | lexical binder, `this`/`parent`, then contextual/inherited or global declaration lookup per Appendix 4; ambiguity is an error, never first-match lookup |
| `EJoin`, `EUnion`, `EDifference`, `EIntersection` | `.`, `++`, `--`, `**` with typed navigation and explicit head-versus-value coercions; no automatic collapse of reference occurrences |
| `EAnd`, `ENeg`, `EOr`, `EXor`, `EImplies`, `EIff` | `&&`, `!`, `\|\|`, `xor`, `=>`, `<=>`; disjunction is `not (not p and not q)`, xor is `(p or q) and not (p and q)`, implication `not (p and not q)`, iff both implications |
| `EEq`, `ENeq`, `ELt`, `EGt`, `ELte`, `EGte`, `EIn`, `ENin` | `=`, `!=`, `<`, `>`, `<=`, `>=`, `in`, `not in`; `>` swaps `<` operands, `<=` negates swapped `<`, `>=` negates `<`; no heterogeneous equality without a justified widening |
| `EAdd`, `ESub`, `EMinExp`, `ECard` | integer `+`, `-`, unary minus and `#`, under the arithmetic policy below |
| `EQuantExp`: `some`, `no`/`not`, `one`, `lone` on a collection; bare collection in Boolean context | respectively `0 < #E`, `#E = 0`, `#E = 1`, `#E < 2`; bare navigation inserts `some`; `not E` here is zero cardinality, `!p` is Boolean negation |
| `EDeclAll`; `EDeclQuant` only `some`/`no`/`not`, single `LocId` | finite object binder `all x : E` bar body; `some` is `not (all x : E` bar `not body)`, `no`/`not` is universal negation; multiple binders require explicit nesting |

Defaulting follows S2's `Defaults`: omitted group inherits the super's effective
group including keyword provenance, else `0..*`; omitted parented local bound is
`0..1` under any keyword or numeric group except numeric `0..*`, else `1..1`;
authored bounds override defaults. Effective abstractness is authored abstractness
or the parent's effective flag. Parentless abstracts have no invented local
parent-fiber predicate. The [adopted numeric policy](sources.md) deliberately evolves
Appendix 3; `opt` and numeric `0..*` retain distinct provenance and child defaults.
M1 imports only effective values and never reconstructs authored provenance.

M2 inherited admission uses S3's `Realization.Core.Selected`: explicit abstracts
are parentless; supers are explicit abstract basics; references are parented;
a realization rank decreases from explicit types to realizations and from
ordinary fields to owners. Contextual views restrict existing objects/links.
Cover/disjoint subtype families and overlapping inherited context views are
separate. The [inherited preservation contract](inherited-realization.md) covers
the complete Appendix 6 skeleton; the [source pipeline](pipeline.md) adds all
twelve bodies and final selections.

Everything outside the whitelist is unsupported. In particular, the remaining
pinned grammar productions are deliberately classified:

- `EnumDecl`/`EnumId`; runtime `string`, `real`, `double`, `bool`/`boolean` domains;
  `EDouble`, `EReal`, `EStr`: deferred. Boolean expressions are still supported.
- `EMul`, `EDiv`, `ERem`, `EGMax`, `EGMin`, `ESum`, `EProd`: deferred arithmetic
  and aggregation. Numeric `*` as a multiplicity upper marker remains supported.
- `EImpliesElse`, `LetExp`/`VarBinding`, `EDomain`, `ERange`, `EUnionCom`,
  `EIntersectionDeprecated`, `EDeclAllDisj`, `EDeclQuantDisj`, multi-`LocId`
  declarations and binder `one`/`lone`: deferred sugar/operators. Core `all` and
  the explicitly listed single-binder forms remain supported.
- `Assertion`/`SubAssertion` (Haskell soft/non-hard constraint path), all four
  `Goal*` and `Subgoal`, nonempty `Init`/`InitHow`: deferred, never discarded.
- All nonempty `TempModifier`, `Transition`, `TransitionExp`, `TransArrow`,
  `TransGuard`, `Tmp*`, `Ltl*`, `PatternScope`: behavior excluded.
- `PosAlloy`, `PosChoco`, source option directives, module-qualified names,
  flattening/redefinition/relocation and other post-SoSyM extensions: unsupported.

Detect erased constructs before desugaring/import. Haskell JSON alone cannot
certify that a source had no enums, escapes, initializers or behavior.
The [oracle adapter](oracles.md) retains
the upstream paired generation receipt; neither that importer nor the upstream
finite checker becomes an M2 oracle without a new proved bridge.

## Resolved-IR API and CLI sequence

The [IR admission API](ir.md) implements `validate`, `validateRaw` and
`validateDocument`. `Backend.Alloy.Structural.compile` implements
[in-memory structural compilation](structural-encoding.md); `Text.render` supplies
[checked serialization](alloy-text.md). The [parser](parser.md),
[declaration resolver](resolution.md) and [constraint elaborator](constraints.md)
provide the source frontend. Their abstract interface shapes are:

```text
admit(profile, rawIR) -> Result ValidatedIR Diagnostics
compileIR(validatedIR, bounds) -> Result (AlloyCore, NameMap) Diagnostics
render(AlloyCore, NameMap) -> Result (AlloyText, SourceMap) Diagnostics
parse(source) -> Result AuthoredSyntax Diagnostics                 [M2]
elaborate(AuthoredSyntax) -> Result ValidatedIR Diagnostics         [M2]
```

The developer interchange is [versioned JSON](ir.md#developer-interchange-contract)
(`clafer-ir/1`; strict decoding is supplied by the native driver), with an
explicit profile, ordered declarations, stable-within-input IDs, separate display
names, origins, parent/super/reference IDs, local/group bounds and optional source
origins. M1 permits effective-only provenance explicitly marked as such.
The source command accepts authored Clafer text; there is no M2 JSON IR protocol.
Unknown versions, semantic fields or constructors are rejected. The
[IR schema](ir.md#developer-interchange-contract) requires duplicate-key rejection,
strict field types and no dangling IDs.
Source locations never substitute for identity; array order never silently changes
reference binding. IDs need not persist across edits. A Haskell capture is a
separate format requiring an explicit adapter.

The selected [native driver](cli.md) is `clafer-compiler`. M1 exposes `compile-ir INPUT --bounds
BOUNDS --output OUTPUT`; `compile-source INPUT` uses the same bound/output
contract. `-` selects stdin/stdout. No implicit input-format detection or default
scope. A versioned bounds file identifies declaration IDs and specifies each
extent's upper/exact object bound, the total nonprimitive object budget and signed
integer bitwidth. M2 also specifies finite intervals for observed integer values.
Inherited extents may overlap along super chains; summing their sizes is not an
object budget. The backend documents its scope mapping for internal signatures,
root singleton and auxiliaries; no analyzer default or inferred scope is relied on.

Compilation needs neither Haskell nor Alloy installed. Those are external
validation tools. No solver is run implicitly. Successful compilation emits the
complete deterministic Alloy text; failure emits no partial successful-looking
output. File output is replaced only after successful rendering. Diagnostics go
to stderr (structured JSON selectable); stdout carries only the requested result.
The same input bytes/profile/options/version produce identical output bytes and
maps, independent of hash-map traversal, timestamps or private absolute paths.

Diagnostics have a version, stable code, phase, category, message, primary location
and related locations/IDs. Source spans use zero-based, half-open UTF-8 byte offsets
in the original file with a logical filename; display line/column are one-based.
CRLF and Unicode offsets refer to original bytes. IR-only locations use a JSON
pointer and declaration/attachment ID, never an invented source span. Sort by
input order, byte offset/pointer, phase and code. Stability covers schema/code
meaning within a major version, not exact English wording.

| Outcome | Interpretation | Compile exit |
| --- | --- | --- |
| Compiled | Admitted and translated; no SAT assertion | 0 |
| Malformed | Bad syntax/layout/schema/IDs/types, invalid intervals or cyclic parent/super graph | 2 |
| Unsupported | Recognized excluded feature/profile, behavior, insufficient bitwidth/range evidence or unsupported bounds configuration | 3 |
| Operational failure | Missing input, IO/resource error or internal failure | 1 |

A structurally valid but impossible source still compiles. Semantic contradiction
is not malformed input. A candidate checker reports satisfied, violating, undefined
expression, malformed candidate or unsupported independently. A solver adapter
reports SAT (with checked decode), bounded UNSAT, timeout, unknown or tool error.
These are not compile exit codes and are never collapsed into success/UNSAT.
A valid exact bound that excludes all source models yields bounded UNSAT, not an
invalid program. Only malformed/incomplete bound specifications or unsafe encoding
profiles are rejected before solving. The
[runtime-only check](cli.md#native-runtime) exercises the binary without
development tools.

## Arithmetic, definedness and finite observation

The arithmetic policy uses upstream mathematical `Int` meaning and **rejects unsafe
bound/bitwidth combinations**, rather than adopting modular source arithmetic.
For signed width `b`, every encoded integer, count, bound and intermediate result
must fit `[-2^(b-1), 2^(b-1)-1]`. [Target bounds](alloy-core.md) and
[source ranges](expression-encoding.md#source-range-analysis-proofs) provide
conservative, terminating range analysis from explicit scopes and input value intervals, independent of whether
constraints hold. Unary counts are bounded by finite operand inventories,
including integer observations; binary relation counts by the product of endpoint
budgets. Child unions count unique heads,
not child declarations or target values. Infinity is an upper-bound marker, never
an encoded integer. The backend must account for any extra arithmetic it emits.

For M2, propagate intervals through addition/subtraction and negation, check all
literals and both sides of Boolean connectives, and reject when the bound cannot
be certified. For example width 4 cannot support a possible count of 8, or an
addition of two values in `0..7`; increasing width or explicitly narrowing the
value intervals can admit it. This conservative policy can reject safe individual
models: report unsupported bounds and preserve the model, never claim UNSAT.
Use the pinned analyzer's overflow prevention as an additional check; it does not
replace a proof of representability. The [oracle profile](oracles.md) reproduces
the upstream widths 1–16 and exact solver options; widening that tool profile needs reviewed evidence.

Partiality remains explicit. `integerOf` requires one realized integer object;
empty/multiple/off-domain extraction is undefined. Boolean operators are strict
in definedness, even when their truth equation would be vacuous. For `all`, the
domain is evaluated before binding and bodies must be defined for its actual
members; the empty domain is true and requires no body evaluations. Encode
expressions as definedness plus value/truth; hard constraint satisfaction requires
both definedness and truth. Derive the definedness translation constructor by
constructor, including under negation and quantifiers. An undefined candidate is
not reported as a defined false expression. Type checking alone proves neither
singleton extraction nor absence of overflow.

Quantifiers range only over finite nonprimitive extents or finite collections
obtained by navigation to observed integer values. No direct observation,
cardinality, equality test or quantification of the entire primitive `int` extent
is admitted. Primitive names in type positions remain allowed. All observed
integers must fit the user-declared intervals and bitwidth.

The Appendix 6 upstream model realizes **all** mathematical integers. The
[finite-observation bridge](expressions.md) retains nonprimitive objects,
reference occurrences and observed integer values. The
[source pipeline](pipeline.md#composed-assurance) extends this observation to a
full integer realization without changing admitted expression denotations. It
handles the primitive's root/domain obligations explicitly. Representability
bounds finite observations, not the size of mathematical `Int`; whole primitive
domains are not equated with finite sets. The guarded M1 checker does not establish
this larger-domain result.

## Independent meanings and theorem obligations

S1/S3/S4 define source satisfaction. The [target contract](alloy-core.md) defines
target instances and compositional
satisfaction from the Alloy reference: finite atom sets, signature membership,
relations, quantification and bounded integer operations. Target truth is never
source truth or successful compilation by definition.

The specification relation `Rep(ir, bounds, source, target)` has concrete data equations:

- A bijection, up to atom renaming, between live nonprimitive source objects and
  designated target object atoms; the root maps to its distinguished singleton.
- Each nonprimitive declaration extent is exactly the image of its source extent.
  Primitive correspondence covers observed values only, not the full infinite
  extent. Super membership retains the same atom; unrelated extents are disjoint
  when required.
- Containment tuples encode actual owner/head pairs. Each reference head retains
  its identity and one dereference target; two bag heads targeting one object are
  distinct. Source link carriers correspond to those occurrences or documented
  composite link pairs, not just a quotient of equal endpoints.
- Auxiliary atoms/relations have stated deterministic roles and scope accounting;
  they cannot manufacture source objects. Unused target atoms are either forbidden
  or proven unobservable and excluded by decoding, with no hidden cardinality effect.
- In M2 integer atoms encode the same observed mathematical values; inherited
  views restrict the original maps, and the finite-observation bridge above applies.

The [structural representation](structural-correctness.md) supplies a concrete
target layout and executable encode/decode realizing these equations. The
[comparison layer](comparison.md) connects actual Analyzer output to that decoder. A free
hypothesis called "correct representation" is not a substitute for the equations.

The following are theorem **shapes**, not existing declarations. Let `I` be an
admitted IR, `B` a validated bounds profile, `T = compileIR(I,B)`, `S` a source
configuration and `A` a target instance. `O` is an executable finite presentation
of the observable part of `S`. `Observes(I,S,O)` specifies equality of nonprimitive
objects/maps and observed integer values; it contains no satisfaction assumption.
For M1 it presents the whole finite configuration; for M2 `S` may contain the
full infinite integer realization. `Fits(I,B,S,O)` adds only finite object budgets,
exact/upper counts, observed integer ranges and representation capacity to this
observation relation. Executable encode/decode operate on `O`, not on a
noncomputable enumeration of an infinite semantic configuration.

```text
admit(raw) = ok I  =>  UpstreamWellFormed(I) and ProfileSupported(I)
TargetSat(T, B, A) =>  exists O S, Decode(I,B,A) = ok O
                                and Observes(I,S,O)
                                and Rep(I,B,S,A) and SourceSat(I,S)
SourceSat(I,S) and Fits(I,B,S,O)
                  =>  exists A, Encode(I,B,O) = ok A
                              and Rep(I,B,S,A) and TargetSat(T,B,A)
elaborate(ast) = ok I
                  =>  DeclarativeElaboration(ast,I) and UpstreamWellFormed(I)
```

Target soundness derives representation invariants from generated constraints;
it does not assume source satisfaction or successful decoding. Bounded
completeness assumes source satisfaction as its premise, but `Fits` may not
contain target satisfaction, a preservation equivalence, or "the compiler is
correct." Range/definedness lemmas are independently stated; all final truth
obligations remain conclusions of preservation. Retain root, ownership, abstract
cover, groups and declaration disjointness when composing S1's `structural_model_iff`,
`compiled_bank_iff`, `erasure_correspondence` and `finite_model_representable`.
An upstream theorem is used only with its actual hypotheses discharged.

Frontend success must establish independently defined name-resolution, defaults,
scope, attachment and coercion rules; well-formed output alone is insufficient.
[Constraint elaboration](constraints.md) proves source expression meaning; the
[source pipeline](pipeline.md) composes it with backend results.
The declared source grammar and parser are a separate boundary unless grammar
recognition/AST correspondence is proved. Include nontrivial witnesses and negative
mutations (lost bag head, missing group/global fact, swapped operand/parent path)
to expose vacuous or circular statements.

### Serialized text and execution trust

The serializer proves [name-map injectivity and checked print/parse reconstruction](alloy-text.md#proved-boundary-and-review-obligation).
Its successful-render proof uses translation validation; total successful
renderability is not proved. The reconstruction parser alone does not establish
correspondence with Alloy's grammar or meaning. Tests exercise the actual pinned
parser and inspect normalized syntax and meaning on small witnesses. Kernel proofs
about `AlloyCore` stop before unproved text parsing, Analyzer translation/SAT solving
and external instance decoding. The [comparison contract](comparison.md) describes
decoder parsing; the [CLI contract](cli.md) records native Lean/C/runtime trust.
Report a theorem at the strongest established boundary, alongside integration
tests, without describing tested serialized output as kernel-proved execution.

## Validation and review handoff

Every feature needs its assigned implementation, theorem when promised and
meaningful positive/negative tests before delivery. The
[comparison suite](comparison.md) compares the identical
candidate with the upstream checker, Haskell Alloy and compiler Alloy only within
M1's common admitted domain. Preserve both discrepancy directions, repeated
reference occurrences, negative candidates, tool options/hashes, seeds and minimized
replays. Unsupported/timeouts are recorded separately. M2 comparisons use the
[expression/inherited bridge](pipeline.md#complete-example-and-exact-replay); Haskell remains useful supplementary evidence.

The [build check](build.md) builds every compiler/test module, audits axioms,
replays the kernel and exercises the native compiler. IntentBond retains source
and traceability evidence. Kernel-checked declarations establish their stated
properties; passing runtime checks does not prove further compiler statements.
Any scope amendment requires explicit review.

<a id="review-handoff"></a>

Changes to this contract require review of:

1. The exact surface whitelist and upstream defaulting policy, including documented
   Haskell discrepancies.
2. Diagnostic, IR and CLI conventions and the conservative scope/bitwidth/value
   interval policy.
3. Model relations, theorem assumptions and finite-observation obligations.

A passing automated check or IntentBond exit 4 cannot approve changes. Component
contracts state the exact proof assumptions, including [M1 correctness](structural-correctness.md),
[inherited realization](inherited-realization.md) and the [source pipeline](pipeline.md).
Issues and PRs retain acceptance records. New work requires manual intake and
independent review. Broader Haskell compatibility requires a reviewed scope change.

The [comparison contract](comparison.md) records native decoding and exact
three-way execution. The in-memory preservation proofs remain distinct from
finite native/serialized comparisons.
