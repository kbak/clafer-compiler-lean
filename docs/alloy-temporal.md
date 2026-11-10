# Independent Alloy temporal target

The `ClaferCompiler.Backend.Alloy.Temporal` library supplies independent Alloy 6
syntax, infinite-trace meaning, finite lasso bounds and checked text for the
[behavioral profile](behavioral.md). Source lifetime cancellation and source
compilation belong to the behavioral encoder. The existing [static target](alloy-core.md)
and [static renderer](alloy-text.md) retain their APIs and output.

## Syntax and admission

`impl~compiler-alloy-temporal-target~1`

[Syntax](../ClaferCompiler/Backend/Alloy/Temporal/Syntax.lean) exposes `Schema`,
`Rel`, `Integer`, `Formula`, `Command`, `Module`, `CheckedModule` and `check`.
The declaration vocabulary reuses static `Signature`, `Field`, multiplicity and
positional identities. Separate Boolean tables mark mutable signatures and
fields. Signature parents precede their children; fields have object endpoints.
The temporal syntax follows the static target's finite postfix representation
and standard `List.foldl`. Public builders preserve operand order. Admission
rejects operand underflow and surplus results; no recursion depth cutoff is used.
The folds carry lexical-depth or environment/time functions where needed.

The admitted declaration subset includes the existing static type-signature
forest and mutable top-level type signatures. Every signature has an explicit
scope; mutable signatures use upper identity scopes. Mutable subtype scopes,
subset signatures and exact mutable scopes are not admitted. A scalar signature
adds one mutable `Int` value per object using the existing scalar table; its
owner, uniqueness, totality and signed-width checks hold in every state.
Use static identity carriers and mutable fields for a fixed pool with changing
live membership. These are target representation choices, not exclusions from the
source completion matrix: the full encoder owns additional required integer
operations and their target correspondence. This library does not accept arbitrary
Alloy modules, functions, closures, higher-arity relations or text escapes.

Relations include unary/binary emptiness, signatures, fields, captured singleton
variables, `univ`, `iden`, `Int`, union/intersection/difference, product, join,
transpose and prime. Integer singleton relations and mixed object-to-integer
value relations use distinct tagged atoms. Quantifier domains are unary and resolve in the outer
environment; bodies resolve at the next de Bruijn depth. Integers include
literals, tuple counts, guarded scalar extraction, addition, subtraction,
multiplication, division and remainder with signed bitwidth and conservative
interval checks. Division and remainder truncate toward zero; possible-zero
divisor intervals are unsupported. Extraction selects a bounded fallback outside
its singleton integer interval, with source definedness represented separately. Admission visits both branches and
quantified/temporal bodies. It never assumes fact truth to justify a range.
Mutable `one`/`lone` populations may draw from more than one identity across
time; the static singleton scope restrictions apply only to static declarations.
Unsafe arithmetic reports `unsupportedBounds`; malformed tables, arities and
bindings report `malformedSyntax`. No command silently falls back to static mode.

`Formula` has classical Boolean connectives, universal/existential quantification,
`after`, `always`, `eventually`, strong `until`, `releases`, `before`, `once`,
`historically`, `since` and `triggered`. `Formula.weakUntil p q` expands to
`(p until q) or always p`; Alloy has no `weakuntil` keyword. Facts are evaluated
at time zero. An invariant is a fact containing explicit `always`.

Covers:
- `req~compiler-alloy-temporal-target~1`

## Traces, bounds and history

[Semantics](../ClaferCompiler/Backend/Alloy/Temporal/Semantics.lean) defines
`Atom`, `State`, `Trace`, `Rel.eval`, `Integer.eval`, `Formula.Holds`,
`Formula.Defined`, `scalarValue`, `Trace.Declarations`, `Trace.InScope`, `Satisfies`,
`Lasso`, `checkLasso` and `Lasso.Satisfies`.

A trace has one finite object inventory and a state at every natural-number time.
Object IDs are opaque and distinct from tagged integer atoms. Each state's
`univ` includes its live top-level object extents and every representable integer;
`iden` is the diagonal of that current universe. There are no String constants or
sequence expressions. Unused object slots are invisible to relations and counts.
The sum of top-level identity capacities bounds observable object identities;
overlapping subtype extents must not be added again. The source encoder owns
root/auxiliary roles and its requested total identity-budget accounting.

Declarations hold at every time: inclusion, abstract coverage, multiplicities and
field endpoint/fiber constraints use the existing independent static declaration
predicate. Static signature/field sets remain extensionally equal to time zero; list
ordering is immaterial. Type-signature
disjointness additionally holds across *all pairs of times*, preventing an atom
from moving to a sibling type after a gap. `Trace.InScope` bounds the union of a
signature's values across the entire trace. Two alternating identities require
capacity two even if every state's population is one. Exact static scopes count
used atoms; arbitrary unused inventory entries do not satisfy them.

`Formula.Holds` is mathematical evaluation over infinite natural time. It imports
no source-language truth or encoder. Prime and `after` advance time while keeping
the lexical environment. `until` requires a right-hand witness and left truth
strictly before it; `releases` includes the releasing instant. `since` is its
past-direction strong counterpart; `triggered` is the classical dual of `since`
and requires its right operand at the current instant. `Formula.Defined` is a
separate strict observation obligation: an overflowing comparison cannot become
satisfying by negation or a vacuous Boolean branch. Mathematical target truth is
not an executable finite LTL decision procedure. The pinned Analyzer supplies
bounded search; no new solver or general temporal framework is implemented here.

A lasso has a nonempty frame list and `0 ≤ loop < length`. `checkLasso` rejects
empty traces, bad loops, malformed state tables, duplicate inventory IDs and
signature atoms outside that inventory. It does not assume declaration/fact truth.
`Lasso.index` unfolds the prefix once and then repeats the suffix beginning at
`loop`. `Lasso.Fits` compares the number of stored states with `minSteps` and
`maxSteps`: each stored state has one outgoing edge, including the last-to-loop
edge, so this is Alloy's number of transitions. Both bounds must be explicit,
positive and ordered. Entirely static modules are rejected because Alloy
forbids their explicit `steps` scope. No unbounded `steps` search or exact-loop command is exposed;
the lasso carries its own exact loop for interpreting a candidate.

Past formulas observe the unfolded **time**, not the stored-frame index.
`before p` is false only at time zero; revisiting frame zero does not reset history.
`Formula.birth p` is `p and not before p`, so it holds at an initially present
state and after each actual absent-to-present edge, including the loop edge.
Past formula truth need not have the same period as the frame valuations on their
first traversal. No state-only truth cache is used.

## Serialization and source maps

`impl~compiler-alloy-temporal-text~1`

[Print](../ClaferCompiler/Backend/Alloy/Temporal/Print.lean) exposes
`Text.render`, `Rendered`, `anonymousNames` and unchecked `serialize`.
`render` accepts only a checked module, validates source metadata, and returns
text/maps only after the independent [parser](../ClaferCompiler/Backend/Alloy/Temporal/Parse.lean)
reconstructs the complete raw module. `RenderError` retains `malformedMetadata`
and `syntaxCorrespondence`. Source labels and spans are sidecar data only.

The renderer reuses the [static name namespaces and source-map chunks](alloy-text.md#api-identities-and-mappings).
Every constructor is parenthesized; declarations, facts and the command occupy
separate LF-terminated lines. Mutable declarations add `var`; priming emits
`( relation ' )`; temporal tokens follow their Alloy spellings. Weak-until and
birth helpers reconstruct their explicit AST expansions. Commands emit the
bitwidth, `min .. max steps` and every signature scope. The checked reconstruction
includes mutability, scopes, timing, command polarity, operand order and captures.

The parser reuses `Std.Internal.Parsec`, lexical helpers and positional table
reconstruction from the static parser. Its temporal recognition rules are separate
from the printer. Input length bounds recursive nesting, with no configured depth
cutoff. It recognizes the emitted subset, not all Alloy syntax. Success carries a
kernel-checked reconstruction equation; neither universal rendering success nor
correctness of the official parser/translator/SAT solver follows from that equation.

Covers:
- `req~compiler-alloy-temporal-text~1`

## Source correspondence and reuse

The full encoder's integer extension reuses the temporal postfix traversal,
`IntRange.checked`, Lean's `Int.tdiv`/`Int.tmod`, and the existing checked
printer/parser. The static target only supplies addition/subtraction and a
singleton scalar interface; it cannot express the selected product, quotient
and remainder operations. The frontend's `BehavioralArithmetic` supplies
conservative magnitude bounds and their semantic proofs. Target interval
calculations use those same bounds over the target's existing `IntRange`, with
the correspondence proved in the compiler correctness layer. They introduce
no source-truth dependency into target interpretation. Division and remainder
admission must exclude zero throughout the denominator interval, and every
intermediate must fit. The pinned Alloy integer built-ins supply the text
correspondence; native Analyzer tests remain separate from Lean evaluation.
No dependency or license pin changes are required.

The guide is the [official Alloy 6 reference](https://alloytools.org/alloy6.html)
and [language reference](https://alloytools.org/spec.html), especially temporal
operators, signatures, facts, relational priming and commands. Immutable Analyzer
source at `794226dd07b536fe35c5ca44b529417183cd629b` supplies the implementation
locators below; the [source register](sources.md) pins the actual 6.2.0 JAR.

| Locator | Independent target correspondence |
| --- | --- |
| `ScopeComputer`: temporal bounds and bitwidth | Explicit signed width and bounded `steps`; no implicit ten-step default |
| `BoundsComputer`: `allocatePrimSig`, `size` | Shared identity scopes, time-wide disjointness, mutable versus static declarations |
| `TranslateAlloyToKodkod`: unary/binary temporal cases and `IDEN` | Prime, ordinary future/past operators and current live identity relation |
| Reference Signature/Field Declarations and Facts | Per-state declaration constraints; initial facts versus explicit invariants |
| Reference Temporal Connectives and pinned translator | Natural-time histories; inclusive release/triggered endpoint, weak-until expansion |

Reuse assessment: local declaration validation, integer bounds, hygienic names,
source maps, Parsec combinators and the accepted temporal oracle bridge supply
existing machinery. Runtime traversal follows the static target's instruction-list
folds, avoiding the partial recursive helpers generated by Lean's ordinary
recursive definitions and derived equality. Direct custom inductive recursors
are not supported by the pinned native compiler. The existing list-fold design supplies
total traversal without custom recursion infrastructure. The pinned upstream `Clafer.Behavioral.Lasso` carries source
identities and Mathlib/proof imports, so it cannot serve as an independent runtime
target structure. Its history distinctions inform the comparison obligations.
The pinned Haskell `AlloyLtl.hs` `initialConsts` and `appearsNow` use `before` for
birth guards; they are compatibility evidence, not target truth. The static
reconstruction grammar cannot recognize the new temporal constructors, so this
module adds grammar rules using its existing parser library. No external parser,
semantic definition or temporal checking framework is copied. New code/fixtures
are original MIT; reused Lean/Std is already pinned under Apache-2.0. The existing
external Alloy/Haskell tooling and license boundary remain unchanged.

## Proof and test boundary

`proof~compiler-alloy-temporal-laws~1`

`Lasso.index_lt`, `index_initial`, `index_loop` and `index_periodic` establish safe
indexing, the initial position, loop edge and periodic valuations after the prefix.
`prime_eval`, `prime_capture`, `static_signature_prime`, `before_initial`, `before_succ`, `birth_initial`, `birth_succ` and
`weakUntil_meaning` expose the precise operator equations. The formula laws take
`Formula.Built` evidence that operands have the shape produced by the public
builders. `Formula.Built.stack`, `fold_unary` and `fold_binary` prove compositional
stack evaluation for those operands; these are shape assumptions, not assumptions
of formula truth or source correctness. Raw malformed instruction lists are
rejected by admission. Kernel fixtures include
both a zero-prefix cycle and a nonzero-prefix lasso, a loop-edge birth and a
history predicate that changes on revisiting the same stored state.

`Text.render_roundTrip` and `render_reconstructs` prove successful reconstruction
of the exact returned/serialized text. Name injectivity reuses the existing
unconditional `Symbol.name_injective`; no finite-name test replaces that theorem.
These results do not prove source preservation, complete temporal evaluation,
range soundness for every arbitrary relational expression, or Analyzer semantics.

Covers:
- `req~compiler-alloy-temporal-target~1`
- `req~compiler-alloy-temporal-text~1`

`utest~compiler-alloy-temporal-integration~1`

[Kernel fixtures](../tests/AlloyTemporal.lean), the
[native harness](../tests/AlloyTemporalNative.lean) and
[actual Analyzer regression](../tests/test_alloy_temporal.py) cover mutable/static
fields, initial/always facts, prime/next, captured bindings, strong/weak until,
release, past endpoints, birth/history across a loop, nonzero-prefix lassos,
identity replacement at capacities one/two, mutable `univ`/`iden`, and integers.
Constructor coverage exercises every relation/integer/formula constructor with
native checked reconstruction, deterministic bytes, hostile source labels and
exact map slices. Malformed instruction lists and parser mutations, bad captures, unsafe intermediates,
invalid metadata and deep temporal nesting are explicit failures or successful
round trips as appropriate; rejected valid test inputs are never discarded.

The temporal oracle bridge applies the pinned Analyzer's different static/mutable
`one`/`lone` scope rules; replacement tests exercise both mutable multiplicities.
Every generated module is parsed and solved by the actual pinned Alloy 6.2.0
runtime with SAT4J and `noOverflow`. Python's standard `ThreadPoolExecutor`,
already used by the PR113 corpus, runs at most two independent cases at once.
Each case keeps its own fresh JVM and evidence directory, with a 120-second
deadline, 1024 MiB heap and 3072 MiB address-space limit. The heap accommodates
the parsed types of expanded full-profile expressions; the runtime receipt
records these limits. Assertions run on the main test thread. This adds no dependency or
solver protocol. Named semantic cases have independently chosen
SAT/bounded-UNSAT expectations, and selected SAT traces are inspected. The test
checks the original parsed bounds before the bridge's command override, retaining
all frames and loop indices. Native execution, the reconstruction parser's Alloy
correspondence and external solving remain tested boundaries. Full static
regressions, axiom audit, kernel replay and IntentBond checks are mandatory.
Evidence retains source hashes, inputs, maps, commands, options, outcomes and
witnesses outside source. Exit 4 leaves independent semantic review pending.

Covers:
- `req~compiler-alloy-temporal-target~1`
- `req~compiler-alloy-temporal-text~1`
