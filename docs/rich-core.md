# Rich and core explicit models

The selected extension `behavioral-rich-core/1` preserves modeling intent alongside
resolved meaning. Its source semantics is pinned to [clafer-semantics #189](https://github.com/kbak/clafer-semantics/pull/189);
independent acceptance of that dependency and this compiler extension remains a
review obligation. The qualified `behavioral-0.5.8/v2` profile remains available
and rejects new past syntax. The static frontend and first-slice JSON v1 retain
their existing admission boundaries.

## Interfaces and lowering

`compile-behavioral-source` accepts `--format rich`, `core`, `rich-json` and
`core-json` when the bounds select `behavioral-rich-core/1`, alongside existing
Alloy/compilation JSON outputs. The first pair
prints readable JSON; the second prints compact JSON of the same versioned
schemas. These are Lean's resolved interchange formats, not Haskell's `.cfr`
printer syntax. `compile-behavioral-explicit` reads either form with explicit
bounds and emits Alloy or the requested explicit form. Rich export describes a
model; selected assertions and scenarios use core export. Output is atomic.

`clafer-explicit-rich/1` retains the authored source with logical locations,
enumerations mapped to declaration IDs, and a resolved expression graph. Every
node retains its operation, typed value, operands, binding slots and attachment.
Patterns and transitions remain identifiable even inside conditions and binders.
The graph records empty-navigation tails as intentionally ignored. Initializers
retain `=`/`:=`, declaration ID, original RHS attachment and a separate explicit
clock (`every-live`, `instance-birth`, `parent-birth`, `global-zero`); temporal
selection is recorded separately. Effective structure is available in the
lowered model. Making bounds explicit cannot silently reclassify an omitted
abstract multiplicity.

The existing certified elaborator performs the shared lowering. Rich replay
re-elaborates its retained source and checks every annotation and its entire core
projection. Edited or stale metadata is rejected; edit the source and re-export
to change a rich model. `Driver.ExplicitRich.expression` reuses the existing
resolver for all nodes, including cursor navigation and generated binder slots.
It does not reconstruct intent heuristically from expanded formulas.

`clafer-explicit-core/1` contains checked effective declarations, group provenance,
rank certificates, declared modifiers, resolved constraints/assertions and a
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
Existing finality lowering is unchanged.

## Consumers and assurance

The Alloy backend consumes the common core. A future SMV or visualization
consumer may handle a supported rich operation directly, but must establish its
agreement with that same core, including definedness and attachment. No SMV
backend is added. Sound fragment recognition and cardinality analyses remain
useful for models authored without a recognizable rich construct. Optimization
must preserve solutions independently of whether its opportunity came from
explicit intent or analysis.

`Correctness.Explicit.sound` and `complete` reuse the actual compiler's full
preservation theorems for imported core requests. They require a distinguished
integer declaration; bounded completeness requires the existing source `Fits`
conditions, including occurrence capacity, ranges, scopes and lasso length.
Parser/printer round trips, rich annotation replay and native execution are
separate tested boundaries. Tests check rich and core fixed points, identical
Alloy output, selected queries, warning preservation, stale annotations, bad
lexical slots and negative intent-recovery requests.

The representation reuses `Frontend.Behavioral.ParsedModel`, the resolved
expression families, `BehavioralSyntax`, strict JSON parsing and the existing
checked backend. The prior inspection format was output-only and lacked complete
structural/provenance input, so the new decoder is separate. No external runtime
dependency or third-party implementation is added. MLIR provides the architectural
analogy of progressively lowered representations; this implementation uses the
repository's existing typed IR and proofs rather than introducing MLIR itself.

The [Haskell candidate profile](../scripts/oracles/rich-profile.json) pins
`gsdlab/clafer@186d8e0a350e4c8895b1c489eb587fa3a1bc2b61`, its source archive,
resolver, lock, Stack/GHC and reference solver settings. `scripts/oracles/rich.py`
builds and validates that candidate separately. Fresh reference tests exercise
its rich/core `.cfr` fixed points, rich-to-core lowering and JSON generation.
These establish reference interface behavior, not wire-format compatibility with
Lean JSON or proof of equivalent model meanings. Exact source/Alloy trace checks
for [past operators](past.md) cover the latter boundary on distinguishing traces.

The candidate's rich-to-core pattern replay prints `!(#x >= 1)` where direct
core output prints `#x = 0`. The reference test retains that exact discrepancy
and checks the narrow natural-cardinality rewrite; it does not claim byte equality
for those two routes. Each printed rich/core form separately remains a fixed point.
The shared admitted examples also exercise Haskell `.cfr` output through Lean's
source frontend and subsequent independent Lean core replay.

Haskell source option directives remain unsupported by Lean's source frontend.
The reference corpus explicitly checks that rejection, then uses a fixture adapter
that recognizes only its exact `--explicit`/`--tl=10` header and supplies independent
Lean bounds. This is a documented corpus boundary, not a general Haskell importer.
