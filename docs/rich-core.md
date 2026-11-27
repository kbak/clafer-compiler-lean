# Rich and core explicit models

The selected extension `behavioral-rich-core/1` preserves modeling intent alongside
resolved meaning. It uses the accepted [past semantics](https://github.com/kbak/clafer-semantics/pull/189),
[native-search correction](https://github.com/kbak/clafer-semantics/pull/191) and
[modifier core reduction](https://github.com/kbak/clafer-semantics/pull/195).
The qualified `behavioral-0.5.8/v2` profile remains available and rejects new past
syntax. The static frontend and first-slice JSON v1 retain their existing admission
boundaries.

## Interfaces and lowering

### Finality lowering

Finality erasure reuses the existing captured-set expansion, inherited modifier
collection, checked expression lowering and strict explicit decoder. The accepted
upstream `Modifiers.lowerCore_agrees` and `loweredHolds_iff` supply the independent
semantic reduction. The executable expansion remains downstream because upstream
lowering is noncomputable and runtime modules cannot import proof dependencies.
No additional package, runtime or license dependency is needed; the upstream
library and existing implementation are MIT.

The shared expansion retains each obligation's placement. Explicit core converts
all-object placement to ordinary constraints on each nonprimitive declaration;
overlapping inherited heads repeat a conjunct without changing its meaning.
Primitive completion contributes only empty, stable views at integer owners.
Head placement remains on the head, and parent placement uses the original
declared parent. This reuses the existing constraint and capture machinery rather
than adding a second attachment language or relying on rich metadata at replay.
The preservation proof discharges these placement and primitive boundaries,
in addition to the existing strict expression and modifier equivalence results.

Version 2 output erases modifier declarations after materializing their complete
obligations, including `final`'s per-head reference stability. Version 1 remains
readable with its original semantics. Rich version 2 retains authored modifiers
in its source and validates the new core projection; legacy rich replay checks
the legacy projection before migration. Parser/native execution and serialization
remain tested boundaries.

`compile-behavioral-source` accepts `--format rich`, `core`, `rich-json` and
`core-json` for `behavioral-rich-core/1`, the
[aggregate abstract multiplicity profile](abstract-multiplicity.md) and the
[initializer clock profile](behavioral-frontend.md#explicit-initializer-clocks), alongside existing
Alloy/compilation JSON outputs. The first pair
prints readable JSON; the second prints compact JSON of the same versioned
schemas. These are Lean's resolved interchange formats, not Haskell's `.cfr`
printer syntax. `compile-behavioral-explicit` reads either form with explicit
bounds and emits Alloy or the requested explicit form. Rich export describes a
model; selected assertions and scenarios use core export. Output is atomic.

`clafer-explicit-rich/2` retains the authored source with logical locations,
enumerations mapped to declaration IDs, and a resolved expression graph. Every
node retains its operation, typed value, operands, binding slots and attachment.
Patterns and transitions remain identifiable even inside conditions and binders.
The graph records empty-navigation tails as intentionally ignored. Initializers
retain `=`/`:=`, declaration ID, original RHS attachment and a separate explicit
clock (`every-live`, `instance-birth`, `parent-birth`, `global-zero`); temporal
selection is recorded separately. An authored clock also produces
`clockAnnotation` with its keyword and byte span. The `temporal` flag on each
header records whether it uses birth timing for `:=`, including an explicitly
selected clock in an otherwise non-temporal model. Effective structure is available in the
lowered model. Making bounds explicit cannot silently reclassify an omitted
abstract multiplicity.

The existing certified elaborator performs the shared lowering. Rich replay
re-elaborates its retained source and checks every annotation and its entire core
projection. Edited or stale metadata is rejected; edit the source and re-export
to change a rich model. `Driver.ExplicitRich.expression` reuses the existing
resolver for all nodes, including cursor navigation and generated binder slots.
It does not reconstruct intent heuristically from expanded formulas.

`clafer-explicit-core/2` contains checked effective declarations, group provenance,
rank certificates, resolved constraints/assertions and a
model/check/scenario command. It has no dependency on source replay. The full
seven-family decoder checks constructor arities, IDs and lexical indices before
calling the same full compiler. Source spans and warning metadata survive replay;
warning text is descriptive metadata, never a proof assumption. Unsupported
constructors, versions, profiles, stale rich data and requests to recover rich
intent from a core input fail explicitly.

Enumerations become ordinary declarations; patterns/transitions become formulas;
all initializers become guarded equations with closed original RHS values and
explicit context transport. No `:=` remains in core. The core retains strict
`initially`/`finally` guards as semantic primitives; ordinary temporal target
lowering expands their birth/death tests with previous/next. Replacing these
guards with ordinary strict source implication would change undefinedness.
All effective modifiers become ordinary constraints, including both head and
reference stability for `final`, per-head `finalref`, target-set `finaltarget`
and initial-presence obligations. The version 2 schema has no modifier table;
inserting one is rejected. The shared capture/equality expansion is also used by
source-to-Alloy compilation. Core replay compiles the materialized constraints
with an empty modifier table, so obligations are not enforced twice. The resulting
Alloy text may differ from direct source compilation because finite declaration
attachments replace all-object placement; exact candidate tests compare meanings.

## Consumers and assurance

The Alloy backend consumes the common core. A future SMV or visualization
consumer may handle a supported rich operation directly, but must establish its
agreement with that same core, including definedness and attachment. No SMV
backend is added. Sound fragment recognition and cardinality analyses remain
useful for models authored without a recognizable rich construct. Optimization
must preserve solutions independently of whether its opportunity came from
explicit intent or analysis.

`Correctness.Explicit.sound` and `complete` reuse the actual compiler's full
preservation theorems for imported core requests. `ModifierCore.upstream_agrees`
connects the shared executable expansion to upstream `Modifiers.LoweredHolds`.
`ModifierCore.result_agrees` proves that materialization and erasure preserve the
original model, assertions and scenarios; `compiled_lower_sound` and
`compiled_lower_complete` compose that result with actual target preservation.
They retain structural validity, total inherited-set observations and the existing
ordinary finite-carrier types. Soundness derives ordinary types from target facts;
bounded completeness uses `Fits`, including occurrence capacity, integer ranges,
scopes and lasso length. `ModifierLowering.lower_idempotent` proves that repeated
lowering adds no obligations.

Parser/printer round trips, rich annotation replay and native execution remain
separate tested boundaries. Tests retain legacy core/rich input, reject stale
metadata and modifier tables in version 2, and check fixed points, selected queries
and warnings. Exact source/rich/core Alloy observations cover additions, losses,
swaps, replacement, repeated bag targets, inherited owners, parent and head gaps,
shallow finality and enum literals. Mutations remove reference/target stability or
replace the attachment survival guard with root survival.
Rich replay must emit the identical source target before sharing its exact-trace
result; materialized core targets are solved independently.

The representation reuses `Frontend.Behavioral.ParsedModel`, the resolved
expression families, `BehavioralSyntax`, strict JSON parsing and the existing
checked backend. The prior inspection format was output-only and lacked complete
structural/provenance input, so the new decoder is separate. No external runtime
dependency or third-party implementation is added. MLIR provides the architectural
analogy of progressively lowered representations; this implementation uses the
repository's existing typed IR and proofs rather than introducing MLIR itself.

The [Haskell candidate profile](../scripts/oracles/rich-profile.json) pins
`gsdlab/clafer@a7c58d30a4c04c566e9a53b03d013cff19f192f0`, its source archive,
resolver, lock, Stack/GHC and reference solver settings. `scripts/oracles/rich.py`
builds and validates that candidate separately. Fresh reference tests exercise
its rich/core `.cfr` fixed points, rich-to-core lowering and JSON generation.
These establish reference interface behavior, not wire-format compatibility with
Lean JSON or proof of equivalent model meanings. Exact source/Alloy trace checks
for [past operators](past.md) cover the latter boundary on distinguishing traces.

On the release fixtures, lowering the printed rich model gives the same core
text as lowering the original source. Both printers retain written cardinality
quantifiers and source order. Top-level abstract bounds lower to a counting
constraint, while nested abstract bounds stay on their declaration. The
[0.6.0 birth guard](https://github.com/gsdlab/clafer/blob/a7c58d30a4c04c566e9a53b03d013cff19f192f0/src/Language/Clafer/Intermediate/Core.hs#L292-L308)
requires current presence and absence in the previous state for a nested context.
This excludes the second of two consecutive absent states under nested next
operators. The root specialization assumes a live root.

The shared examples also exercise Haskell output through Lean's source frontend
and independent Lean core replay. The fixture adapter recognizes the generated
`--explicit` header, `--core` on core output and optional `--tl=10`. It supplies
Lean bounds separately. Authored source directives remain outside this profile.

## Java toolchain compatibility

The [Java 0.6.0 frontend](https://github.com/gsdlab/chocosolver/blob/591cbd5963fc7ee0cb4c514ee1f6273327898798/frontend/src/main/java/org/clafer/frontend/ClaferCommand.java)
produces the same rich and core text as the pinned Haskell compiler on the
[shared fixtures](../tests/test_rich_reference.py) when compiling original source.
Lean accepts the bodies with the separately supplied bounds and can replay the
resulting core JSON.

A saved rich file has a distinct input path. For example, compile
`P ?` with a nested constraint `[X (X (initially (1 = 0)))]` to rich text, then
pass that file to `claferc -m clafer --core`. Java treats the input as already
core and rejects the rich `initially` anchor. Haskell lowers the same file to
the direct core output. The same Java diagnostic applies to several other rich
constructs, including enumerations and transitions. Use original source with
Java or the pinned Haskell compiler for rich-to-core replay.

The [solution generator](https://github.com/gsdlab/chocosolver/tree/591cbd5963fc7ee0cb4c514ee1f6273327898798)
routes static models to Choco, including decimal objectives, and temporal models
to Alloy. The [checked instance adapter](choco-adapter.md) compares the guarded
structural fragment. The [VS Code extension](https://github.com/gsdlab/clafer-vscode/blob/26045bf0870395d6f0b744966ee048169c6fd187/extension.js)
uses the Java language server, runs Haskell `clafer` for compilation and exposes
separate `claferIG` and `clafersg` generation commands.
