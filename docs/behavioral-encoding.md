# Behavioral encoding

`impl~compiler-behavioral-encoding~1`
`impl~compiler-trace-representation~1`
`impl~compiler-behavioral-correctness~1`
`impl~compiler-full-behavioral-correctness~1`
`impl~compiler-behavioral-property-commands~1`

The behavioral libraries connect admitted [behavioral IR](behavioral-ir.md) to
the independent [temporal target](alloy-temporal.md). They use the selected
[behavioral profile](behavioral.md), immutable [sources](sources.md#behavioral-sources)
and the selected structural core. The original first-slice API and resolved CLI
remain available. The full-profile API consumes elaborated in-memory requests;
the [source CLI](behavioral-source.md) composes that API with checked rendering.
Final qualification and independent acceptance retain their own gates.

Covers:
- `req~compiler-behavioral-encoding~1`
- `req~compiler-trace-representation~1`
- `req~compiler-behavioral-correctness~1`
- `req~compiler-full-behavioral-correctness~1`
- `req~compiler-behavioral-property-commands~1`

## Runtime representation

`Backend.Alloy.Behavioral.compile` accepts `IR.Behavioral.Admitted`, explicit
`Bounds` and a formula-size fuel witness. It returns a checked temporal module,
declaration identity/source maps and attachment IDs. Errors reuse the structural
typed outcomes for unresolved scopes, unsupported bounds and malformed internal
target syntax. Compilation neither runs Alloy nor decides source satisfaction.

The schema reuses the structural signature forest for static identity pools.
Signature zero contains the shared object inventory, including identities that
are absent in some or all stored frames. Field zero records the immutable actual
parent; field one records current presence through root-to-object rows. Each
declaration has a mutable reference field. Current heads intersect the fixed
type pool with presence. Current containment uses the same actual parent field
and live endpoints. Reference fields retain head occurrences, so bag heads can
share a referent without collapsing their identities.

`identityFacts` enforce the unique root, its lack of parent, total parenthood for
other identities, concrete direct types and typed actual parents. Abstract leaf
pools are explicitly empty. `stateFacts` enforce permanent root presence, live
parents, current reference typing/functionality and the structural backend's
generated snapshot facts. Parent typing applies to the most-specific concrete
type; inherited views preserve that identity and parent.

`formulaAt` returns raw, positive and negative translations. Core temporal
operators use explicit parent-lifetime guards, leaving ordinary Alloy temporal
meaning independent of source cancellation. `one`/`lone` use raw classical
counting. Quantifiers preserve chosen identities across time; set capture freezes
membership while navigation uses current relations. Source attachments quantify
over every live applicable instance at every natural time.

`coverPool` freezes an enumeration covering the shared inventory. Repeated
aliases pad smaller inventories without turning an upper scope into an exact
scope. Frozen-set capture enumerates membership choices over those aliases:
one capture can produce `2^objects` branches and nested captures multiply that
cost. This is an explicit finite encoding cost, not a bound on source time or
an approximation of capture meaning.

`encode` emits fixed identity tables and all mutable frames with the original
loop. `decodeRaw` extracts root, concrete types, parents and frame data;
`decode` additionally checks that re-encoding agrees extensionally with every
input table and frame. These checks concern data, not source validity or formula
truth. Malformed tables, changing static identities and unsupported extra rows
are rejected. The native witness adapter is a separately tested boundary.

## Kernel boundaries

`Correctness.Behavioral.TraceRep` contains one equivalence between the entire
source identity carrier and the target object pool. Its concrete equations
preserve root, ancestor pools, parents, live extents, dereference tuples, frame
count and loop index. There is no per-frame choice of bijection or satisfaction
field. `encode_rep` constructs the relation from unique source labels and root
data; `decode_rep` derives it from successful checked decoding.

`target_decode_exists` derives actual decoder success from target schema
well-formedness, declarations and the emitted identity facts. `encoded_decodes`
applies this to the concrete encoder using identity validity, unique labels and
duplicate-free reference rows; source snapshot or attachment truth is not needed
for that round trip. The resulting `TraceRep` retains every stored observation
and the loop under a single global correspondence, allowing tuple-list reordering.

`TraceRep.formula_raw`, `formula_positive` and `formula_negative` cover every
admitted first-slice constructor under related frozen environments. Generated
relational formulas are unconditionally defined; structural count comparisons retain finite signed
integer range obligations. `TraceRep.attached_meaning` relates the emitted
attachment to all live source owner contexts with an explicit identity-capacity
bound.

`snapshotState` is a concrete live projection of target tables.
`snapshotState_declarations`, `snapshot_facts` and `snapshotFormula_eval` cover
every declaration and fact actually generated by the existing structural
backend, including exact count evaluation. `Encoding.compiled_snapshot_facts`
derives `Structural.FactModel` for a satisfying trace of the successful temporal
compiler output.
`TraceRep.compiled_valid` then reuses `represented_sound_facts` to derive every
upstream state obligation, with reference endpoint liveness checked explicitly.
`TraceRep.compiled_attached` derives source attachment truth under the same map.

The public `compiled_sound` theorem in
[Correctness.lean](../ClaferCompiler/Correctness/Behavioral/Correctness.lean)
combines these results: successful compilation and independent satisfaction of
its actual target lasso produce a successful executable decode, a global
`TraceRep`, upstream trace validity and every source attachment. Its premises
contain no supplied source trace, assumed decoding success or preservation
adapter. The object-capacity bound is derived from the actual target scope.

The reverse snapshot transport uses `TraceRep.stateFacts_complete` and the
existing structural `source_facts`. Its range premise is
`Structural.SourceCountFits` on each raw source frame: actual finite containment
and group fibers and emitted interval endpoints must fit the selected width.
No target truth is included in that observation condition.

`compiled_complete` concludes that the actual `encode` result satisfies the
actual successfully compiled module, including declarations, all facts, command
and lasso bounds. Premises are source validity and attachments, unique labels,
duplicate-free reference rows, identity capacity, `SourceScopeFits` on the
source's fixed inherited pools, step limits and the raw-frame count condition
above. Unused but allocated source identities still count toward pool scopes;
overlapping ancestor pools do not inflate the total object count.

`constant_common_fragment` equates the actual always-lifted M1 clauses with
`Structural.target.eval` on `snapshotState` for constant target valuations.
`constant_common_satisfies` adds the existing static typing, declaration and
scope checks to obtain static `Satisfies`. `snapshot_liveness_trivial` shows that
all-live source identities preserve every static pool in that projection.
This common-fragment result concerns the generated M1 clauses; behavioral
attachments and trace identity obligations retain their separate proofs.

These statements concern admitted in-memory syntax and infinite unfolding of
finite observations. They do not prove serialized grammar recognition, native
execution, SAT solving, arbitrary infinite-trace periodicity or full behavioral
profile qualification. Independent semantic review remains an acceptance gate.

## Full-profile runtime

`Backend.Alloy.Behavioral.Full.compile` accepts `Full.Request`, explicit
identity/declaration scopes, an integer observation interval, bitwidth, trace
step limits and traversal fuel. It compiles constraints, effective inherited
modifiers and the selected run scenario or assertion into the same checked
independent target. Every source branch passes range analysis before lowering;
exhausted traversal fuel returns an unsupported diagnostic.

The full schema uses disjoint concrete direct-type pools and derives inherited
views from the validated ancestor table. Mutable object-reference rows preserve
reference heads, including bag occurrences; scalar-reference rows use a separate
integer field. Containment, effective local/group intervals, inherited reference
owners, refined containment and set keys are checked against those concrete
observations. The actual parent and allocated object inventory remain fixed over
the entire trace.

Primitive integers have the source carrier `Int`, with the full mathematical
integer extent at every time. A finite target observes bounded integer literals,
scalar fields and expression operands. `Completion` combines the finite ordinary
object carrier with all integers; it does not identify the source integer extent
with Alloy's bounded `Int`. Direct infinite primitive extents, primitive child
enumeration and primitive-owned attachments are rejected. Finite integer captures
and arithmetic remain supported, including a captured integer as `this`.

`Full.Expressions.lowerAt` translates sets, collection families, scalar integers,
predicates, grouped atoms and formulas. Guarded values preserve missing results,
strict conditional branches, singleton extraction, implicit sum coercion, empty
extrema and repeated fold occurrences. Arithmetic admission covers intermediate
values and fold prefixes. Ordered grouped tuples count the original raw body;
ordinary source negation uses the separate signed translation.

Each partial formula has a reified original domain and raw/positive/negative
truth. Parent cancellation and inactive birth/end anchors introduce no operand
domain obligation. Within the active parent interval, temporal operands retain
the original strict domain even after a truth witness. `check` negates the whole
attached property classically, so an undefined property is a counterexample;
this differs from a source negation, which also requires definedness.

## Full-profile proof components

`Full.TraceRep` relates the fixed ordinary identity labels and every stored
observation to the target. The completed source interpretation adds all primitive
integers. `ObservesCompletion.formula_transport` transports every
expression constructor between a represented source carrier and that completion,
including source definedness and both temporal signs.

`compiled_structural_sound` in the `Full` correctness namespace starts from successful full
compilation and actual target satisfaction, derives checked decoder success,
and proves upstream structural validity of the completed trace.
`encode_full_structure` proves the reverse declarations, scopes, scalar fields
and generated structural facts. `structuralFacts_defined_of_holds` supplies the
target-definedness obligations for those actual facts. Their fit assumptions
constrain data: global identity capacity and labels, source pool/fiber counts,
integer intervals and stored scalar values. They contain no expression truth or
preservation premise.

The expression proof follows the executable pass. `SyntaxBuilt.lowerAt` checks
all successful branches, including unreachable alternatives. `Ranges.inputs_of_facts`
derives primitive input bounds from target structure; `Ranges.integer_fits`
propagates them through source expression evaluation. Constructor proofs consume
the actual successful lowering results and preserve the original source options,
raw truth and both signs. Frozen environments and the finite alias cover are
explicit data invariants. The range and completion proofs remain outside the
runtime dependency graph.

`Expressions.lowerAt_preserves` proves preservation by induction over the actual
seven-part recursive pass. `lower_preserves` derives its range certificate from
successful admission. `modifiers_source` connects the actual generated list to
the upstream effective modifier contract, including vacuous primitive contexts.
`command_source` distinguishes classical failure of the whole asserted property
from strict source negation.

`Full.compiled_sound` composes these results: successful compilation and actual
target satisfaction yield checked decoding and `SourceResult` on the completed
source trace. The direct IR theorems also take the declaration ID and origin
proof for the built-in integer type; source frontend binding derives its
existence. `SourceResult` uses the existing upstream model, constraints,
counterexamples and scenario semantics; `sourceResult_request` connects these
witnesses to the existing request interpretation. `Full.compiled_complete`
proves that the concrete encoder satisfies the actual successfully compiled
module for a completed source witness satisfying data-only `Fits` conditions.
These conditions cover source identity labels/capacity, scalar observations,
structural counts, declaration scopes and lasso length. Target formula truth,
target definedness and expression agreement are conclusions, not fit premises.
`compiled_complete_observed` accepts the original source trace and integer
realization with `ObservesCompletion` data equations. The proved
`ObservesCompletion.valid` and `sourceResult` transport its structure and query
meaning to completion; neither completed validity nor formula agreement is
assumed from the caller. Unused source identities need not be enumerated.

`TargetDefined.formula_defined` and the actual lowering's `CountFree.lowerAt`
certificate derive arithmetic totality from the checked target syntax, even in
inactive alternatives. This permits an undefined source assertion to yield a
defined target counterexample. `frontend_sound` and `frontend_complete` compose
the full compiler with successful source elaboration;
`frontend_complete_observed` retains the original source carrier. `elaborate_source` retains
every authored and generated header derivation; `check_model` and `run_model`
identify the model in actual frontend requests. `check_source` preserves the
assertion index and `run_source` preserves every scenario body, span and attachment
in order through the existing list traversal. Source declaration binding
supplies the implicit primitive integer declaration even for an empty model.

The full-profile Analyzer fixtures in `BehavioralFullNative`,
`BehavioralFullExpressionsNative`, `BehavioralFullPatternsNative`,
`BehavioralFullModifiersNative`, `BehavioralFullTemporalNative`,
`BehavioralFullStructureNative` and `BehavioralFullFrontendNative` exercise
actual frontend elaboration and output.
The pattern suite covers all thirty pattern/scope cells, both signs and
satisfying/violating traces, plus missing and simultaneous boundaries, events at
boundaries, late triggers, first openers, parent death and reappearance. Modifier
fixtures distinguish inherited and direct heads, target images, replacement,
gaps and both orders of combined modifiers. The native harness rejects proof
and upstream-semantics imports. Additional authored cases distinguish inherited
birth obligations, parent-gap resets, dynamic enum literal identities, nested
universal assertion checks and declaration equations after the first live state.
The harness retains source hashes, emitted text and solver observations. These
finite witnesses do not establish periodicity of
arbitrary infinite source traces or replace kernel checking.

## Reuse assessment

Full expression values reuse finite guarded alternatives derived from the existing
freeze construction, target postfix syntax, upstream `PrimitiveExpression` and
`IntegerObservation`, frontend `Ranges`, and static scalar fallback. These APIs
do not directly express strict conditional values or ordered tuple counts.
Standard `List` folds hold guarded values; both conditional branches retain their
domains. Repeated covering aliases are deduplicated by identity, while repeated
source domains retain distinct occurrences. This adds no dependency or license
cost; finite case expansion may be exponential and needs explicit covering and
range proofs before full-profile preservation can be claimed.

The rich structural candidate uses validated ancestor and reference-owner tables
with disjoint direct-type signatures. The first-slice M1 schema and its
`SnapshotRepresentation` require a narrower inheritance shape and cannot be reused
wholesale. Fixed parents, live tables and target relational builders remain shared.
The primitive integer extent is represented separately from object identities;
full source completion requires an observation theorem, not a bijection between
an infinite integer carrier and the finite object inventory.

The full attachment builder reuses the fixed global alias cover for every
attachment. Root-owned formulas specialize their frozen context to the
represented root identity. This preserves one attachment construction and avoids
an extra proof layer solely to omit unused binders. Alloy can eliminate binders
whose aliases do not occur in a body; captures retain the same explicit finite
expansion cost.

Target arithmetic totality reuses `Integer.range`, checked interval operations
and the existing arithmetic proof helpers. The first-slice definedness theorem
requires relation-count bounds, whereas full lowering emits count literals and
no `Integer.count`. `CountFree` records that concrete syntax invariant through
the existing value and traversal operations, allowing target admission to prove
totality of every emitted alternative. This proof-only layer adds no dependency
or runtime machinery.

Partial formula lowering reuses the first-slice raw/positive/negative
`Translation`, frozen-set enumeration and explicit lifetime operators. It retains
definedness as a separate target formula over the original source tree. Reusing
`Temporal.Formula.Defined` for this purpose would be incorrect: its arithmetic
checks are target well-definedness, and its temporal checks do not stop at the
source parent's first absence. The upstream `Formula.Defined` equations supply
the source domain. Reifying that domain with the existing target constructors
also permits classical failure of an undefined assertion. No new temporal
evaluator, collection library or dependency is required.

The existing structural signature allocator, declarations, fact generator,
finite fiber proofs and scope resolver supply the structural component. A live
frame cannot reuse the static module's exact *pool* scopes, because absent
identities are not live objects. `Structural.FactModel` therefore exposes the
schema/declaration/fact premises already used by structural soundness; previous
theorems retain their signatures and delegate to it. The signature-declaration
proof is likewise factored by its actual observation premises so fixed unused
identity pools can reuse it.

Pinned upstream `Clafer.Behavioral` supplies independent signed meaning,
identity invariants and snapshot theorems. Its snapshot constructor requires
source validity, which would be circular in soundness. `liveSnapshot` constructs
the same data using only root liveness, then derives validity from transported
structural facts. `liveSnapshot_eq_upstream` identifies the constructions once
validity is established. No upstream meaning is replaced.

Lean/Std lists, vectors, finite recursion and Mathlib equivalences, finite sets
and hierarchy relations supply collection and proof machinery. The temporal
target supplies ordinary operators, checked bounds and serialization; neither it
nor upstream's noncomputable formulas provides the executable source lowering
or its global representation proof. The pinned Haskell candidate and Alloy
Analyzer supply comparison behavior, not a preservation premise. No new package,
vendored semantics or license obligation is introduced; existing MIT dependency
and tool licenses remain those in the source register.

## Absent reference observations

The adopted [absence results](sources.md#accepted-semantics-main-dependency)
apply to raw, inherited and refined reference views. In the full encoder,
`Full.head` intersects the allocated identity pool with the current live
extent. Scalar dereference restricts total value storage to that head; inherited
`deref` restricts the nearest declared reference to the current subtype head.
Object-reference facts require live endpoints and one value at each live head.
They reject tuples at absent heads rather than masking malformed source data.

[`Full.AbsentReference`](../ClaferCompiler/Correctness/Behavioral/Full/AbsentReference.lean)
connects those definitions to the accepted source lemmas:

- `completeTrace_absent_values` proves that scalar tables agreeing at live
  identities produce the same completed source trace.
- `TraceRep.absent_object_row` derives raw object-row exclusion from actual
  generated state facts.
- `TraceRep.absent_deref` proves the actual target dereference image is empty at
  an absent mapped identity, using concrete representation, the integer primitive,
  positive bitwidth at most 16, fitting scalar values and generated state facts.
- `compiled_absent_references` derives actual decoding, source model/query
  satisfaction and empty raw references from successful compilation and target
  satisfaction. It does not assume decoder success or source validity.

Captures preserve identities and consult current relations. With a surviving
parent, a disappearing child cannot meet a next-value equality. Empty relational
inequality remains defined, arithmetic coercion of empty is zero, and integer
extraction from empty is undefined. Parent cancellation follows the existing signed
and definedness lowering in both polarities. Counter persistence additionally needs
an initial value and enabled next-value transitions; an unconstrained identity may
vanish and reappear.

The scalar table stays total and is preserved by checked decoding in every frame,
including absent and never-live identities. Different hidden values can therefore
produce different target witnesses for the same source trace. These results do not
claim canonical target witnesses or remove scalar rows from replay.

## Fixtures and validation

[BehavioralEncodingNative.lean](../tests/BehavioralEncodingNative.lean) compiles
actual admitted documents and exercises executable decoding and re-encoding.
[test_behavioral_encoding.py](../tests/test_behavioral_encoding.py) runs the
emitted text through the pinned Alloy Analyzer and retains modules, tuples,
outcomes, tool metadata and source hashes externally.

The 35 cases distinguish X/F/G/U/W and both signs, next-state parent death,
context death with a surviving parent, birth/end anchors, frozen capture versus
current navigation, counting barriers, quantifiers, stable/replaced heads and bag
references. Mutation cases remove an invariant or make actual parents mutable;
the resulting witnesses expose orphaning or per-state renaming. Wrong typed
parents are rejected. An actual Alloy `check` yields a counterexample. SAT
witnesses are decoded and replayed through the native encoder.

The source comparison suite additionally fixes complete traces for absent, inherited
and captured references, parent cancellation in both signs, contradictory next
values, counter replacement, rebirth, never-live identities and differing loop
indices. It checks hidden scalar storage and invalid raw object rows separately.
Unfixed solver queries distinguish allowed disappearance from a next-value
obligation that forbids it; successful witnesses pass native decoding and the
independent finite observer. This executable observer remains outside the kernel
proof boundary.

The mandatory repository check still builds every discovered Lean module,
audits transitive axioms, replays the kernel and runs all static and behavioral
regression groups. Its retained receipt is evidence for one exact candidate;
IntentBond exit 4 leaves independent semantic review pending.

The full range bridge reuses `Expression.Ranges` derivations, the accepted
`BehavioralArithmetic` interval lemmas, upstream finite integer conversion and
aggregate APIs, and Mathlib finite-set cardinality. It supplies the missing
connection from scope and observation budgets to these semantic APIs. The bridge
has no native dependency or additional license cost; mathematical enumeration
and finite-set proofs remain outside the runtime compiler.

`Partial.knownTrue` reuses the target `Formula.fold` to recognize a conservative
subset of formulas that hold at every time and environment. `totalAlways` omits
repeated lifetime guards for those total original domains. The proof
`Partial.knownTrue_sound` is independent of source satisfaction; source range
admission still visits every operand and branch before lowering. The existing
fold and lifetime lemmas supply the implementation and proof machinery; no
optimizer package or additional runtime dependency is introduced.
