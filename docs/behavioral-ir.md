# Executable behavioral IR

The first-slice profile is `behavioral-core/1`, within the
[behavioral completion contract](behavioral.md). It selects guarded effective
structural declarations and total set observations from accepted upstream S2/S3.
Richer structural atoms, partial arithmetic, surface reductions, target compilation
and serialized CLI formats retain their separate owners. Static admission remains
unchanged.

## Reuse assessment

The implementation reuses `IR.Structural` declarations, authored metadata, ranks,
diagnostics and exact M1 admission. Lean `Std` vectors, finite indices, Boolean
membership functions and `Nat.rec` provide storage and traversal. Traversals reuse
the sufficient-budget pattern in `IR.Expr`: caller-supplied natural budgets carry
erased kernel-checked size proofs. Ordinary recursive code and recursive derived
equality/formatting would introduce generated helpers rejected by the existing
declaration audit. Proof-only constructor interpretation is noncomputable;
native fixtures inspect output constructors without custom equality machinery.
Finite sets use membership vectors/functions, avoiding duplicate-list counting.
The existing static expression IR cannot represent time-spanning captures or
signed temporal operators; its partial numeric meaning is outside this slice.
No container, graph, parser or model-checking dependency is added.

Upstream `Clafer.Behavioral` at accepted commit
`27a5bbe86657edab00980da57b2f86221f92a5f1` supplies source meaning. Its
`Formula.normalize` is noncomputable and observations use mathematical sets;
runtime modules cannot import these definitions. Executable syntax and signed
normalization therefore have a proof-only constructor interpretation and an
agreement theorem against that exact normalizer. Upstream `normalize_agrees`,
`normalize_normal` and `normalize_lower_agrees` supply semantic results. No second
temporal satisfaction definition is introduced downstream. The Haskell candidate's
`AlloyLtl.pushNegations` is a comparison guide, including the raw `one`/`lone`
counting barrier. Negation precedes parent-lifetime lowering.

The dependency update adds accepted S2/S3 and source comments: all 138 changed
pre-existing static Lean modules have identical code after comment/whitespace
removal. The toolchain, transitive packages, static Haskell/Alloy identities,
fixtures and comparison algorithms are unchanged. Oracle receipts retain their
original identities; new runs identify the updated semantics pin. Existing MIT
and Lean Apache-2.0 licenses apply. No Haskell implementation is copied.

The executable normalizer follows the constructor equations of upstream
`Clafer/Behavioral/Normalization.lean` (MIT, copyright 2026 Kacper Bak); the
independent `denote`, lifetime and lowering definitions remain upstream.
The fixture reconstructs upstream `Examples.cycling` in executable tables and
proves exact equality with it, reusing its independently checked admissibility.

## API and admission

Runtime declarations are in `ClaferCompiler.IR.Behavioral`:
[syntax](../ClaferCompiler/IR/Behavioral/Syntax.lean),
[admission](../ClaferCompiler/IR/Behavioral/Admission.lean) and
[trace observations](../ClaferCompiler/IR/Behavioral/Trace.lean).
They import only runtime structural data and `Std`.

`Document k` contains version `clafer-behavioral-ir/1`, profile
`behavioral-core/1`, the original `Structural.Core k`, its certificate and an
ordered list of `Attachment k`. `admitBehavioral` returns `Admitted k` or the
existing typed structural diagnostic. It retains the entire input document.
Names are not identities. Structural authored metadata remains opaque and is
preserved independently of effective bounds; this API does not infer defaults.

Formula declarations and lexical positions use `Fin k` and `Fin n`, respectively.
They cannot contain dangling indices. This is an in-memory resolved API, not a
JSON decoder: C9 owns serialized index validation and closed input schemas.
Attachment owners use original declaration IDs, and admission checks their
existence, occurrence-ID uniqueness and byte-span ordering. The only admitted
attachment kind is `constraint`. Assertions, scenarios and
`RequestedBody.unsupported` are recognized requests that return unsupported.
The full completion profile is also rejected. `Formula k n` includes only the
enumerated total-set constructors; partial arithmetic/static atoms cannot be
injected as arbitrary Boolean predicates.

Failure order is version, profile, structural core/ranks, structural support,
metadata, then requested bodies. Diagnostic codes are `behavioral.version`,
`behavioral.profile`, `behavioral.core`, `behavioral.structural-profile`,
`behavioral.metadata` and `behavioral.constructor`. Core and metadata failures
are malformed; unsupported versions/profiles/features remain unsupported.
Aggregate metadata failures identify the document with the empty pointer; no source location is
invented. These outcomes never imply SAT or UNSAT.

`Formula.normalize` handles every constructor and both source signs. It flips
X/F/G/U/W and anchor bodies according to T2, distributes the Boolean forms and
`all`/`some`/`no`, and preserves raw bodies beneath `one`/`lone`.
`Formula.normalize a sign fuel enough` requires `enough : sizeOf a < fuel`.
`Attachment.normalize` takes one budget and an adequacy witness for its formula
body, and changes only that body, retaining occurrence, owner, kind and source
span. `SetExpr.eval` and `Atom.eval` likewise take a budget and a strict size
witness. These are traversal budgets, separate from `ObservationBounds`; every
finite syntax tree has a sufficient natural budget. The API never returns a
default truth value or truncates a traversal. It does not compute budgets from
raw trees at runtime: callers retain them when constructing syntax, as the static
expression builders do. Native fixtures pass concrete budgets with checked proofs.
Nested equivalence/conditionals can grow exponentially; no output-size bound is
promised.

## Runtime traces and observations

`Identities k o` stores stable IDs, one root, fixed direct types and fixed parents.
`Frame k o` stores changing Boolean live membership and explicit declaration,
head and target reference tuples. Two bag heads with the same target remain two
objects. `Lasso k o steps` contains the shared inventory, a frame vector and a
`Fin steps` loop: empty traces and out-of-range loops are unconstructible in this
typed API. The first `steps` visits are the prefix; subsequent visits repeat
`loop .. steps - 1`. The original loop is retained, including a nonzero prefix.

`ObservationBounds` separates whole-pool identity capacity, positive minimum and
maximum frame counts, and per-frame reference-row capacity. `fits` contains only
those data bounds. There is no implicit integer observation/bitwidth: primitive
types are rejected by this slice. Later integer extensions must retain the
full-domain versus finite-observation distinction.

`admitTrace` checks unique stable IDs, permanent root/type/parent conventions,
concrete direct types, typed actual parents, live parents, live reference endpoints
and duplicate reference rows. Fixed parents are stored once, so a frame cannot
move an object to another parent. It rejects malformed representation with
`behavioral.trace` and insufficient capacities with
`behavioral.observation-bounds`. These are representation checks, not a temporal
or structural satisfaction checker. In particular, reference functionality/type,
set keys, multiplicities and groups still require upstream `StateValid` for every
state. `checked_valid` exposes those remaining hypotheses explicitly.

Finite sets are Boolean membership functions over `Fin o`; equality and subset
range over the entire pool. `SetExpr.eval` and `Atom.eval` retain captured sets,
live-filter standalone `this`, and navigate current frames. `thisStep parent`
starts from the retained context identity even if absent. `step parent this`
starts from the live-filtered set. Quantifier/`let` environments push sets without
changing the attachment identity. Ancestry reuses `Nat.repeat`; the proof uses
upstream's bounded first-visit theorem, including on cyclic raw inputs.

## Proof handoff

The proof-only namespace `ClaferCompiler.SemanticsBridge.Behavioral` contains
[syntax/admission](../ClaferCompiler/SemanticsBridge/Behavioral/Syntax.lean),
[trace/observations](../ClaferCompiler/SemanticsBridge/Behavioral/Trace.lean) and
[attachment](../ClaferCompiler/SemanticsBridge/Behavioral/Attachment.lean) bridges.
They import source APIs at `27a5bbe86657edab00980da57b2f86221f92a5f1`.

| Declaration | Exact conclusion and hypotheses |
| --- | --- |
| `admitted_domain`, `admit_success_iff`, `admit_preserves` | Upstream `WellFormed`/`Supported`, exact checked guards and unchanged input document; no satisfaction premise |
| `admitted_attachment`, `contexts_resolved` | Existing unique owner, constraint kind, supported formula; original IDs select the upstream live owner extent |
| `normalize_interpret`, `normalize_normal` | Actual executable output equals upstream normalization and has its normal-form property, for every constructor/depth/sign and sufficient traversal budget |
| `normalize_agrees`, `normalize_lower_agrees` | Normalized raw meaning and upstream lifetime lowering agree with independent signed `denote`, for arbitrary traces, environments and times |
| `attached_normalize_lower`, `attachment_preserved` | Every live owner starts an obligation; lowering retains that identity and occurrence metadata |
| `ancestor_agrees`, `relation_agrees`, `setExpr_agrees`, `atom_agrees` | Concrete Boolean finite observations equal the upstream observations of the unfolded lasso; set/atom evaluation requires its traversal-size witness, with no generic adapter-agreement hypothesis |
| `environment_push` | Exact preservation of time-spanning captures and context on lexical extension |
| `identityChecks_valid`, `checked_root_live`, `checked_parent_live` | Checked identity/root/parent representation invariants hold at every unfolded time |
| `checked_valid` | Source trace validity additionally requires upstream structural `StateValid` at every time |
| `observes_self`, `checked_fits`, `fixed_parent` | Canonical shared correspondence and capacities, and unchanged parent even across gaps |

`ObservesTrace l τ e` uses **one** equivalence `e : Fin o ≃ U` for the whole trace.
It gives root, direct-type, parent, live-membership and reference equations; it
contains no satisfaction assertion. Equivalence covers this finite nonprimitive
pool, including unused identities, and prevents arbitrary per-state renaming.
`FitsTrace` adds only `fits`. The canonical interpretation `trace l` discharges
this relation with the identity equivalence. A future adapter to an infinite
primitive carrier needs a separate observation extension; it cannot use this
finite equivalence as a whole-domain claim.

These results do not prove a finite temporal evaluator, a frontend, Alloy
translation, serialization, solver behavior or full-profile completion. Runtime
normalization is executable; infinite source truth and lifetime lowering remain
the pinned independent proof definitions. No `sorry`, unchecked axiom or native
decision certificate supplies a proof.

## Fixtures and validation

[Native fixtures](../tests/BehavioralNative.lean) and the
[native runner](../tests/test_behavioral_ir.py) exercise admission, unsupported
profiles/constructors/attachments, metadata, capacity and identity mutations,
orphan/dangling references, duplicate rows, nonzero loops, captures, current
navigation, repeated bag targets and signed/counting normalization.
[Kernel fixtures](../tests/Behavioral.lean) prove that the runtime lasso is exactly
upstream's admissible cycling witness. They distinguish parent cancellation from
context death, root persistence, both source signs holding after cancellation,
persistent-parent consistency, non-resumption and impossible parent movement.

The mandatory build inventories all new modules, audits their transitive axioms,
replays the kernel and runs the native harness independently of upstream proof
imports. Existing structural/native/Haskell/Alloy regressions remain required.
Native code generation and execution are tested boundaries; kernel results and
source-matched IntentBond evidence still require independent semantic review.
