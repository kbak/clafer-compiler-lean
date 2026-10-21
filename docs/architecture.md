# Structural compiler contract

This is the adopted [contract](https://github.com/kbak/clafer-compiler-lean/issues/2)
under the [structural roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4).
Structural-only development and the upstream typed-core M2 scope are selected.
Issue #2 was closed by merged PR #22; build #5, oracle tooling #6 and structural
IR #7 were accepted through PRs #23–#25. The [comparison tools](oracles.md) provide
external validation; the [IR API and proof inventory](ir.md) record the delivered
M1 admission boundary. The independent [target core](alloy-core.md) belongs to
accepted task #8 (PR #26). The [structural backend](structural-encoding.md) and
[text task #9](alloy-text.md) are accepted through PRs #28 and #27. Selected #11
has a partial [representation proof layer](structural-correctness.md). The
[typed expression API](expressions.md) is selected as #14 after #7 acceptance.
Later tasks require their own manual intake. The remaining contracts below are delivery
specifications, not implemented APIs or proved results.
[Requirements](spec.md) covers the present documentation obligations;
[reserved requirements](spec.md#reserved-implementation-requirements) remain future work.

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

Module ownership is binding. The [build bootstrap](build.md) creates the module
roots; its empty feature modules do not implement their later tasks.
Each owner delivers implementation, proofs where promised, positive/negative
fixtures, exact declaration names, source-matched evidence and unresolved limits.

| Module/responsibility | Owning tasks | Required handoff |
| --- | --- | --- |
| Lake, root module, check/CI and proof audit | [Build #5](https://github.com/kbak/clafer-compiler-lean/issues/5) | Native smoke run, module inventory, kernel/axiom audit, reviewed check scope |
| External comparison tooling and corpus | [Oracles #6](https://github.com/kbak/clafer-compiler-lean/issues/6), [differential #12](https://github.com/kbak/clafer-compiler-lean/issues/12) | Pins, same-generation Haskell receipt, exact-candidate replay and mutation sensitivity |
| `ClaferCompiler/IR`, `SemanticsBridge` | [IR #7](https://github.com/kbak/clafer-compiler-lean/issues/7), [expressions #14](https://github.com/kbak/clafer-compiler-lean/issues/14) | Validated executable data, upstream interpretation, admission/denotation agreement |
| `Backend/Alloy` syntax/semantics/printer | [Target #8](https://github.com/kbak/clafer-compiler-lean/issues/8), [text #9](https://github.com/kbak/clafer-compiler-lean/issues/9) | Independent finite meaning, scopes, hygiene, syntax correspondence |
| `Backend/Alloy` translation and `Correctness` | [Structural #10](https://github.com/kbak/clafer-compiler-lean/issues/10), [proofs #11](https://github.com/kbak/clafer-compiler-lean/issues/11), [inherited #13](https://github.com/kbak/clafer-compiler-lean/issues/13), [constraints #15](https://github.com/kbak/clafer-compiler-lean/issues/15) | Concrete model relations, soundness and bounded completeness |
| `Frontend` parser/resolver/elaborator | [Parser #16](https://github.com/kbak/clafer-compiler-lean/issues/16), [declarations #17](https://github.com/kbak/clafer-compiler-lean/issues/17), [constraints #18](https://github.com/kbak/clafer-compiler-lean/issues/18) | Source spans, authored provenance, declarative elaboration relation and success proofs |
| `Driver`, instance decoder and integration | [Decode #12](https://github.com/kbak/clafer-compiler-lean/issues/12), [IR CLI #19](https://github.com/kbak/clafer-compiler-lean/issues/19), [source pipeline #20](https://github.com/kbak/clafer-compiler-lean/issues/20), [qualification #21](https://github.com/kbak/clafer-compiler-lean/issues/21) | Stable protocol, actual Alloy integration, complete telematics, private artifacts/benchmarks |

Hard dependencies remain those in the roadmap and native GitHub blocked-by links.
Issue #2 precedes #5; acceptance and manual selection are separate gates. Shared
IR/target changes require coordination; no ticket may quietly narrow this matrix.

## Feature matrix

The matrix has three delivery columns. M2 includes M1. Every accepted row inherits
its owning tasks' proof and positive/negative test obligations above. The detailed
constructor/surface tables below close the M2 inventory. Sources S1–S8 refer to
[pinned source locators](sources.md#source-locators).

| M1: guarded effective structural core | M2: static constraints, inherited realization, text frontend | Explicitly deferred/rejected |
| --- | --- | --- |
| Resolved declaration IDs, separate names/origins, finite containment, root and parent/super ranks (S1; #7/#10/#11) | Authored/default provenance, lexical/global lookup, forward references, layout and spans (S2/S5; #16/#17) | Import/module system, guessed resolution, declaration identity from display names |
| Effective valid local/group intervals, unbounded upper marker, concrete group counts as unions of child heads (S1; #7/#10/#11) | Keyword/numeric defaults, inherited group overrides, ordinary-field group enforcement (S2/S3; #13/#17) | Automatic scope inference; silently replacing authored defaults with Haskell behavior |
| Parentless leaf abstract basics with unrestricted bounds, or zero bounds only for unused abstract chains; basic inheritance into abstract basics (S1; #7/#10/#11) | Selected ordinary inherited fields and explicit abstract families with realization ranks (S3; #13) | Explicit nested abstract types, concrete superclasses, unequal-parent refinement, relocation, reference-super/target narrowing |
| Direct user-class set/bag references on concrete declarations, including cyclic references; occurrence identity retained (S1; #7/#10/#12) | Selected parented integer references and inherited views of the same objects/links (S3/S4; #13/#14/#15) | Parentless abstract references, expression-valued reference targets, arbitrary reference inheritance |
| Constraint-free; global root, abstract cover, ownership, group and declaration-disjointness obligations (S1; #10/#11/#12) | Every core constructor and selected hard-constraint surface form below (S4/S5; #14–#18) | Dropping constraints to obtain M1; treating assertions or goals as hard constraints |
| No runtime primitives; numeric bounds/cardinalities still need checked bitwidth (S1/S7; #8) | Mathematical integer observations with finite domains, definedness and no-overflow policy (S4; #14/#15) | Runtime string/real/double/Boolean domains, enums, infinite primitive-extent observation, general aggregation |
| Resolved-IR API and native CLI (#7/#19) | Source frontend (#16–#18), integrated source CLI and all Appendix 6 declarations/c01–c12/final selections at M3 (#20) | Production Haskell dependency; blanket full-Haskell compatibility |
| Static Alloy only (S7; #8–#12) | Same static target with selected integer/constraint constructs (#15) | Behavior, temporal operators/modifiers/transitions, backend escapes, optimization goals, other backends and post-SoSyM extensions |

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
three different operations. #7 proves agreement in both directions with admission,
not just acceptance of a few examples. #10/#11 preserve all global obligations.
Haskell capture adds receipt/option restrictions for comparison; those are not
extra semantic restrictions on the compiler's own IR API.

### M2 typed core: exhaustive constructor inventory

S4 is the authority for meanings; #14 owns executable syntax and interpretation,
#15 translation/constructor proofs, and #18 source elaboration. Every row needs
positive and rejecting/violating examples, including undefined cases where relevant.
`Expr` below is `Clafer.Constraints.Expr`; the corresponding delivered #14 representation is
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
productions and parentheses; #16 records an independent grammar for this subset.
The paper locators and selected corrections in S2–S4 control meaning.

Retain the pinned `PosIdent` shape (a letter followed by letters, digits,
underscore or apostrophe), decimal `PosInteger`, and line/block comments. #16
must pin the lexer character classes and test Unicode rather than silently
narrowing names to ASCII. Preserve original spelling without Unicode
normalization; repeated names in different contexts are legal. Reserved primitive
names/aliases and the synthetic root are classified explicitly by #17, never
allocated as ordinary user declarations. Escapes and option directives are
recognized for rejection even where the reference lexer treats them as comments.

| Accepted production/form | Elaboration/validation owner and contract |
| --- | --- |
| `Module`, `ElementDecl`, `Clafer`, `Subclafer`; empty/list elements | #16/#17: declarations with indentation layout or explicit braces, comments and blank lines; reject inconsistent layout and tabs in indentation |
| `AbstractEmpty` / `abstract`; empty super / `: Name` | #17/#13: preserve authored/effective flags; super is one resolved parentless abstract basic in the selected realization domain |
| `ReferenceEmpty`, `-> Name`, `->> Name` | #17: direct class target or `integer`/`int` alias to the canonical integer primitive; no arbitrary target expression |
| Empty group; `xor`, `or`, `mux`, `opt`, `n..m`, `n..*` | #17/#13: bounds respectively `1..1`, `1..*`, `0..1`, `0..*`; retain keyword provenance |
| Empty card; `?`, `+`, `*`, `n`, `n..m`, `n..*` | #17: valid nonnegative intervals; omitted parented card follows upstream `Defaults` |
| `ClaferUse` backtick plus a single resolved type name, card and body | #17: the Appendix 6 use shorthand creates a local declaration extending that type; no import/module-qualified use |
| `Constraint`, `Subconstraint`: square-bracketed hard bodies, local or global | #18: preserve each body and owner occurrence; multiple bodies conjoin, empty list means true |
| `ClaferId`, `Name` with one `ModId`, `EInt`, parentheses | #18: lexical binder, `this`/`parent`, then contextual/inherited or global declaration lookup per Appendix 4; ambiguity is an error, never first-match lookup |
| `EJoin`, `EUnion`, `EDifference`, `EIntersection` | #18: `.`, `++`, `--`, `**` with typed navigation and explicit head-versus-value coercions; no automatic collapse of reference occurrences |
| `EAnd`, `ENeg`, `EOr`, `EXor`, `EImplies`, `EIff` | #18: `&&`, `!`, `\|\|`, `xor`, `=>`, `<=>`; disjunction is `not (not p and not q)`, xor is `(p or q) and not (p and q)`, implication `not (p and not q)`, iff both implications |
| `EEq`, `ENeq`, `ELt`, `EGt`, `ELte`, `EGte`, `EIn`, `ENin` | #18: `=`, `!=`, `<`, `>`, `<=`, `>=`, `in`, `not in`; `>` swaps `<` operands, `<=` negates swapped `<`, `>=` negates `<`; no heterogeneous equality without a justified widening |
| `EAdd`, `ESub`, `EMinExp`, `ECard` | #18/#15: integer `+`, `-`, unary minus and `#`, under the arithmetic policy below |
| `EQuantExp`: `some`, `no`/`not`, `one`, `lone` on a collection; bare collection in Boolean context | #18: respectively `0 < #E`, `#E = 0`, `#E = 1`, `#E < 2`; bare navigation inserts `some`; `not E` here is zero cardinality, `!p` is Boolean negation |
| `EDeclAll`; `EDeclQuant` only `some`/`no`/`not`, single `LocId` | #18: finite object binder `all x : E` bar body; `some` is `not (all x : E` bar `not body)`, `no`/`not` is universal negation; multiple binders require explicit nesting |

Defaulting follows S2's `Defaults`: omitted group inherits the super's effective
group including keyword provenance, else `0..*`; omitted parented local bound is
`0..1` under any keyword group, else `1..1`; authored bounds override defaults;
effective abstractness is authored abstractness or the parent's effective flag.
Parentless abstracts have no invented local parent-fiber predicate. This deliberately
preserves the documented Haskell numeric-group and `opt` default disagreements.
M1 imports only effective values and never reconstructs authored provenance.

M2 inherited admission uses S3's `Realization.Core.Selected`: explicit abstracts
are parentless; supers are explicit abstract basics; references are parented;
a realization rank decreases from explicit types to realizations and from
ordinary fields to owners. Contextual views restrict existing objects/links.
Cover/disjoint subtype families and overlapping inherited context views are
separate. #13 must prove preservation of M1 and the complete Appendix 6 skeleton;
#20 adds all twelve bodies and final selections.

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
certify that a source had no enums, escapes, initializers or behavior. #6 retains
the upstream paired generation receipt; neither that importer nor the upstream
finite checker becomes an M2 oracle without a new proved bridge.

## Resolved-IR API and CLI sequence

API shapes (`validate`, `validateRaw` and `validateDocument` implement the
[admission API](ir.md); `Backend.Alloy.Structural.compile` implements the
[in-memory structural compilation API](structural-encoding.md), and `Text.render`
implements [checked serialization](alloy-text.md). The [authored parser](parser.md)
implements `parse` under accepted task #16. Selected #17 implements
[checked declaration elaboration](resolution.md); expression elaboration remains #18):

```text
admit(profile, rawIR) -> Result ValidatedIR Diagnostics
compileIR(validatedIR, bounds) -> Result (AlloyCore, NameMap) Diagnostics
render(AlloyCore, NameMap) -> Result (AlloyText, SourceMap) Diagnostics
parse(source) -> Result AuthoredSyntax Diagnostics                 [M2]
elaborate(AuthoredSyntax) -> Result ValidatedIR Diagnostics         [M2]
```

The developer interchange is [versioned JSON](ir.md#developer-interchange-contract)
(`clafer-ir/1` initially; parsing belongs to #19), with an
explicit profile, ordered declarations, stable-within-input IDs, separate display
names, origins, parent/super/reference IDs, local/group bounds and optional source
origins. M1 permits effective-only provenance explicitly marked as such. M2 extends
the version/profile deliberately with authored flags and typed bodies; unknown
versions, semantic fields or constructors are rejected. #7 owns the exact schema,
including duplicate-key rejection, strict field types and no dangling IDs.
Source locations never substitute for identity; array order never silently changes
reference binding. IDs need not persist across edits. A Haskell capture is a
separate format requiring an explicit adapter.

The planned executable is `clafer-compiler`. M1 exposes `compile-ir INPUT --bounds
BOUNDS --output OUTPUT`; #20 adds `compile-source INPUT` with the same bound/output
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

| Outcome | Interpretation | Proposed compile exit |
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
profiles are rejected before solving. Native packaging/runtime-library checks
belong to #19; no public release is authorized.

## Arithmetic, definedness and finite observation

The proposed policy uses upstream mathematical `Int` meaning and **rejects unsafe
bound/bitwidth combinations**, rather than adopting modular source arithmetic.
For signed width `b`, every encoded integer, count, bound and intermediate result
must fit `[-2^(b-1), 2^(b-1)-1]`. #8/#15 establish a conservative, terminating range
analysis from explicit scopes and input value intervals, independent of whether
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
replace a proof of representability. #6 initially reproduces the upstream widths
1–16 and exact solver options; widening that tool profile needs reviewed evidence.

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

The Appendix 6 upstream model realizes **all** mathematical integers. Do not
truncate it and claim equality of whole primitive domains. #14/#15/#20 must prove
a finite-observation relation: retain nonprimitive objects, reference occurrences
and observed integer values; extend the finite observation to the upstream full
integer realization without changing any admitted expression's denotation.
Representability bounds finite observations, not the size of mathematical `Int`.
The bridge must handle the primitive's root/domain obligations explicitly. Until
proved, M2 end-to-end assurance remains incomplete; the M1 checker cannot fill it.

## Independent meanings and theorem obligations

S1/S3/S4 define source satisfaction. #8's [target contract](alloy-core.md) defines
target instances and compositional
satisfaction from the Alloy reference: finite atom sets, signature membership,
relations, quantification and bounded integer operations. Target truth is never
source truth or successful compilation by definition.

Proposed relation `Rep(ir, bounds, source, target)` has concrete data equations:

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

#10/#11 choose a concrete target layout and executable encode/decode realizing
these equations. #12 connects actual analyzer output to that decoder. A free
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
#18 proves expression elaboration meaning, #20 composes it with backend results.
The declared source grammar and parser are a separate boundary unless grammar
recognition/AST correspondence is proved. Include nontrivial witnesses and negative
mutations (lost bag head, missing group/global fact, swapped operand/parent path)
to expose vacuous or circular statements.

### Serialized text and execution trust

#9 supplies [name-map injectivity and checked print/parse reconstruction](alloy-text.md#proved-boundary-and-review-obligation).
Its successful-render proof uses translation validation; total successful
renderability is not proved. Review must explicitly assess this boundary against
the required round trip or accept a stated alternative before closing #9. That
parser alone does not establish correspondence with Alloy's grammar/meaning.
Exercise the actual pinned parser and inspect normalized syntax/meaning on small
witnesses. Kernel proofs about `AlloyCore` stop before unproved text parsing,
Analyzer translation/SAT solving and external instance decoding. #12 documents
external decoder parsing; #19/#20 retain native Lean/C/runtime trust explicitly.
Report a theorem at the strongest established boundary, alongside integration
tests, without describing tested serialized output as kernel-proved execution.

## Validation and review handoff

Every feature needs its assigned implementation, theorem when promised and
meaningful positive/negative tests before delivery. #6/#12 compare the identical
candidate with the upstream checker, Haskell Alloy and compiler Alloy only within
M1's common admitted domain. Preserve both discrepancy directions, repeated
reference occurrences, negative candidates, tool options/hashes, seeds and minimized
replays. Unsupported/timeouts are recorded separately. M2 comparisons require the
new expression/inherited bridge; Haskell remains useful supplementary evidence.

The [build check](build.md) now builds every compiler/test module, audits axioms,
replays the kernel and exercises the native bootstrap. IntentBond retains source
and traceability evidence. These checks do not prove the future compiler statements.
Actual feature declarations and proof/test artifacts arrive in their owning tasks;
any scope amendment requires explicit review.

<a id="review-handoff"></a>

Issue #2 and merged PR #22 adopted these contract decisions before #5 intake:

1. The exact surface whitelist (including omitted sugar) and upstream defaulting
   policy, including the documented Haskell discrepancies.
2. The diagnostic/IR/CLI conventions and conservative scope/bitwidth/value
   interval policy. Exact schema fields and declaration names belong to #7/#19.
3. The model-relation/theorem assumptions and finite-observation obligation;
   its implementation/proof belongs to #14/#15/#20.

The closure and merge record the disposition; historical candidate wording in
that issue is not current task status. A passing automated check or exit 4 cannot
approve future changes. #6–#10 are accepted through PRs #24–#28. #11 is selected;
its representation work is partial and global preservation remains unproved.
Parser #16 is accepted through PR #30; its authored API and
unproved grammar boundary are described in the [parser contract](parser.md).
Selected #17 supplies the [resolution/defaulting contract](resolution.md) after
#16/#7 acceptance; its semantic acceptance remains pending.
No unresolved research tag, publication step or blanket Haskell-parity promise
blocks this plan.

Selected #12's [comparison contract](comparison.md) records the concrete native
decode/export API and exact three-way execution boundary. #11's merged partial
representation layer is its data API dependency; full source soundness and bounded
completeness remain outstanding and are not inferred from finite comparisons.
