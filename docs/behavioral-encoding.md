# Behavioral first-slice encoding

`impl~compiler-behavioral-encoding~1`
`impl~compiler-trace-representation~1`
`impl~compiler-behavioral-correctness~1`

The first-slice library connects admitted [behavioral IR](behavioral-ir.md) to
the independent [temporal target](alloy-temporal.md). It uses the selected
[behavioral profile](behavioral.md), immutable [sources](sources.md#behavioral-sources)
and the guarded structural core. The full behavioral frontend, primitive
arithmetic, surface reductions, resolved CLI protocol and final qualification
retain their own completion gates.

Covers:
- `req~compiler-behavioral-encoding~1`
- `req~compiler-trace-representation~1`
- `req~compiler-behavioral-correctness~1`

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

## Reuse assessment

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

The mandatory repository check still builds every discovered Lean module,
audits transitive axioms, replays the kernel and runs all static and behavioral
regression groups. Its retained receipt is evidence for one exact candidate;
IntentBond exit 4 leaves independent semantic review pending.
