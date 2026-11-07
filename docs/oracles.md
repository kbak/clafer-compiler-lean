# Reproducible comparison tools

The external Haskell, Lean and Alloy tools reproduce comparisons for the selected
structural contract. They reuse `scripts/verification/` from the immutable Clafer
Semantics Lake dependency. The base oracle compares Haskell-generated Alloy with
the upstream Lean checker; [three-way comparison](comparison.md) also checks
native-generated Alloy. These executions supply testing evidence, not new theorems.

## Tools and profile

The [machine-readable profile](../scripts/oracles/profile.json) and
[source register](sources.md) pin Haskell `6750e6f591b2131549122c13dee94d3d2257eaea`,
semantics `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4`, Lean 4.35.0 and Alloy 6.2.0
distribution SHA-256 `6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d`.
The Haskell library build uses Stack 3.11.1, GHC 9.6.7, `lts-22.44`, and its pinned
`json-builder` and `StringMap` Git dependencies. The upstream builder checks the
source archive/tree, original lockfile, unchanged library sources and exporter
source/binary hashes. A matching installed exporter may be reused. Build receipts
are unsigned identity records, not authentication of the producer.

Java 17 is the initial reproducible subset of the Java 17+ requirement. The
upstream adapter records the actual binary, vendor/VM build, JAR and freshly
compiled bridge hashes. It strips ambient JVM option overrides. SAT4J, one worker,
symmetry/skolem depth zero, overflow prevention, no partial-instance inference
and no decomposition are explicit; every public `A4Options` value is recorded.
The initial command profile is overall scope 5, signed bitwidth 8, 30 seconds,
512 MiB heap and 2560 MiB address space. Each fixture supplies **every** user UID's
upper bound and root 1. The importer validates bounds; the comparison adapter
validates all actual command scopes, multiplicity adjustments and an independent
conservative arithmetic range argument. Widths outside 1–16 or insufficient
widths are unsupported, never UNSAT. These are experiment bounds, not universal
completeness bounds.

Pinned `Language/Clafer.hs` can dispatch Alloy generation to a temporal backend.
The upstream exporter audits source AST/tokens before erasure, calls `generate`
once for JSON and Alloy, and retains post-analysis/post-string IR, consumed UID
map, effective options and fragments. Import requires backend `als`, the exact
options, paired bytes and state hashes. Temporal source and a mutated temporal
receipt are rejected. The real Alloy bridge also rejects temporal ASTs and
requires static trace bounds `-1`, rather than relying on the runtime instance's
`isTemporal()` flag. No ordinary separate CLI exports substitute for this receipt.

## Provision, capture, compare and replay

Prepare dependencies as described in [Contributing](../CONTRIBUTING.md), then:

```sh
python3 scripts/oracles/oracle.py prepare /tmp/clafer-oracle-tools-UNIQUE
export CLAFER_ORACLE_TOOLS=/tmp/clafer-oracle-tools-UNIQUE/tools.json
export CLAFER_ORACLE_EVIDENCE=/tmp/clafer-oracle-evidence-UNIQUE
bash scripts/check.sh
```

Provisioning is outside the [1200-second IntentBond check deadline](build.md).
Linux x86_64 supports upstream automatic Haskell/Java downloads with hash checks;
other platforms need explicit compatible tools. `CLAFER_CAPTURE`,
`CLAFER_CAPTURE_BUILD`, `CLAFER_CAPTURE_CACHE`, `CLAFER_ALLOY_JAR`,
`CLAFER_JAVA_HOME` and `CLAFER_ALLOY_CACHE` select external tools/caches during
provisioning. Invalid explicit settings fail. `tools.json` retains their resolved
paths outside source. Checks require this record, revalidate identities and
recompile the bridge; they do not silently provision missing tools or skip tests.
Fresh snapshots reuse dependency packages and external tools, rebuilding project
outputs. CI runs on pull requests, pushes to `main` and manual dispatch. It
retains setup logs, notices, tool receipts and all oracle evidence.
Preparation validates the outer and inherited manifest identities, then shares
missing nested checker dependencies through relative links to the already
prepared packages. Existing clean nested checkouts are preserved; dirty or wrong
revisions fail. The links remain inside a copied package tree, avoiding a second
Mathlib download/build without changing manifests or upstream source meanings.

The following commands take new external output directories. A bounds file is a
JSON object with `root: 1` and an explicit natural upper bound for each compiler
UID; use the [fixture inventory](../tests/fixtures/oracles/inventory.json) for
examples. Candidate JSON uses the upstream object/member/containment/reference
format, distinct from the developer IR interchange.

```sh
python3 scripts/oracles/oracle.py capture --tools "$CLAFER_ORACLE_TOOLS" \
  model.cfr --bounds bounds.json /tmp/capture-UNIQUE
python3 scripts/oracles/oracle.py compare --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/capture-UNIQUE/capture candidate.json /tmp/comparison-UNIQUE
python3 scripts/oracles/oracle.py replay --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/comparison-UNIQUE /tmp/replay-UNIQUE
```

Capture returns success only for admitted input; unsupported input retains a
non-success diagnostic and no checker/solver verdict. Comparison/replay success
requires completed agreement on the identical candidate. Bounded UNSAT here
rejects that pinned candidate; it does not establish unbounded model UNSAT.
Disagreements, malformed input, unsupported input and execution failures all
return nonzero with distinct structured outcomes. Timeouts preserve any already
observed solver verdict but cannot count as a completed comparison.

Each successful capture keeps source, JSON, Alloy, generation receipt and build
receipt with raw-byte hashes. Comparisons additionally retain candidate bytes,
source/core hashes, commands, requested/effective bounds, runtime identities,
options, solver logs, decoded witness, isomorphism and replay instructions. The
suite writes a downstream source inventory and final evidence hash index. The
upstream `52-S/v1` receipt's historical paper identity is preserved unchanged.
External trust includes Haskell, the Python adapters, Java/Alloy/SAT4J, Lean
execution and witness parsing. Tests do not extend kernel proofs to these tools.

## Fixture admission and provenance

The inventory verifies immutable bytes before execution. Fixtures stay in the
pinned semantics dependency; no Haskell or semantics fixtures are copied here.
Four small rejection sources are original compiler-repository MIT fixtures.

| Inventory IDs | Use | Finite checker boundary |
| --- | --- | --- |
| `empty`, `overlap` | Root-only structural input and overlapping extents | Admitted; overlap candidate violates declaration disjointness |
| `bag`, `set`, `upstream-set-bag` | Distinct reference heads, shared targets, uniqueness | Admitted; the same repeated-target candidate satisfies bag and violates set |
| `groups` | Group occurrence counting and numeric multiplicity bounds | Admitted effective values only |
| `inheritance` | Leaf abstracts, subtype chains and unused abstract | Admitted guarded inheritance, without inherited fields |
| `cycles` | Cyclic reference targets | Admitted; no containment/super cycle is introduced |
| `shadowing` | Repeated display names in different nesting contexts | Admitted by distinct compiler UIDs, not names |
| `inherited-field` | Abstract with an inherited child | Unsupported `abstract_fragment`; no checker verdict |
| `numeric` | Primitive integer reference | Unsupported `type_metadata`; no checker verdict |
| `expression` | Hard Boolean constraint | Rejected by the source audit before capture |
| `temporal` | Initial modifier | Rejected by the source audit before capture |

All 13 sources execute the real exporter and all nine admitted captures reach
Lean admission. Three exact-candidate comparisons and one replay exercise the
real solver. This is a reproducible smoke corpus, not exhaustive verification of
all admitted candidates or the broader M2 semantics. The full upstream search and
mutation utilities at the pinned revision support [exact candidate comparison](comparison.md).

## Inspected licenses and distribution contents

Preparation retains the Haskell source archive, MIT notice, Cabal/Stack dependency
declarations, build receipt and backend dispatch source externally. Semantics
adapters and original fixtures are MIT, copyright 2026 Kacper Bak. The reused
`set_and_bag_references.cfr` retains the GSD/ISD Labs MIT notice in the dependency's
`tests/fixtures/importer/LICENSE-upstream`. Fixture IDs record their notice path.

The exact JAR declares MIT in its manifest, but its contents also include these
separately hashed notices, all retained by preparation:

| JAR entry | Inspected notice |
| --- | --- |
| `LICENSES/Kodkod.txt`, `Gini.txt`, `MiniSat.txt` | MIT-style notices for the respective components |
| `LICENSES/SAT4J.txt` | LGPL 2.1 text |
| `LICENSES/Electrod.txt` | Mozilla Public License 2.0 text |
| `LICENSES/Glucose.txt` | Glucose/Syrup and MiniSat notices, including distinct parallel-version terms |
| `LICENSES/Lingeling.txt` | Evaluation/research permission with commercial/competition restrictions |
| `META-INF/LICENSE.txt`, `META-INF/NOTICE.txt` | Apache 2.0 text and Apache Commons IO attribution |

Only SAT4J is selected. The JAR also bundles other native solvers and libraries;
this is an inventory of supplied notices, not a complete redistribution clearance
or an assertion that each embedded class has a mapped license. The
[qualification inventory](qualification.md) distinguishes packaged runtime
dependencies from external comparison tools. Distribution requires review of all
bundled licenses. The oracle tools and their notices remain external; they are
not included in the compiler candidate.

## Discrepancy triage

Preserve both directions: Alloy accepts/Lean rejects, and Lean accepts/Alloy
rejects. Preserve pin/decode failure separately. Keep the identical candidate,
occurrence IDs, both outputs, all effective options, seed/search budget when used,
source/tool identities, failed predicates and replay command. Minimize by deleting
objects/rows while preserving the same discrepancy; retain every attempted replay
and distinguish deletion-minimal from globally minimal. Timeouts and unsupported
trials cannot establish minimality.

State expected meaning from the pinned independent semantics/published source,
then classify the evidence as a possible compiler bug, formalization defect,
language-version difference or harness error. Search existing issues with
`python3 scripts/tickets.py list` and repository search; link an existing issue or
create a scoped issue before any semantic change. Upstream owns reusable semantic
fixes. No automatic discrepancy posting or changing expected outcomes to match a
new tool is allowed. Known group-counting and empty-group differences, and the
adopted numeric-default evolution, remain in the [source register](sources.md);
effective-value admission does not
prove authored-source default agreement.

## Temporal oracle reuse and boundary

The separate `behavioral-0.5.7-candidate/v1` comparison profile uses the
[behavioral source pin](sources.md#behavioral-sources). The existing static
capture, admission, receipts and replay retain their original pins and rules.

Reuse assessment: the pinned semantics `runtime.download`, archive/tree receipts,
`alloy_runtime.prepare` and Java environment filtering already provide the tool
acquisition and identity checks. Python's standard library supplies JSON, hashing,
process deadlines and archive handling. Alloy 6.2's public `Command`, `A4Solution`
and tuple APIs supply bounded temporal solving and all lasso frames; no temporal
solver, parser or graph library is reimplemented. The static exporter audits out
temporal syntax and its bridge requires static trace bounds, so separate small
Haskell/Java adapters are necessary. The temporal exporter calls the unchanged
Haskell library once to obtain paired JSON/Alloy and effective options. The new
builder reuses the pinned Stack/GHC/dependency recipe without changing either
compiler's library sources. These are external, unproved test adapters, with no
new Lean or production runtime dependencies.

License decision: reuse upstream positive `.cfr` fixtures by immutable path/hash
inside the externally retained candidate source archive, with its MIT GSD/ISD
Labs notice. Do not copy generated `.als.reg` outputs into execution evidence as
compiler runs. Additional sources and hand-checked witnesses are original MIT
fixtures. The Haskell library remains external; new adapters use its public API.
Alloy's existing multi-license inventory and SAT4J selection apply unchanged.
No new dependency license or binary distribution is adopted.

## Temporal provisioning, execution and replay

The [temporal profile](../scripts/oracles/temporal-profile.json) pins candidate
`af858ec0fe3ce2ceacb7fd120947c058233086d6`, Stack `3.11.1`, GHC `9.6.7`,
`lts-22.44`, the unchanged lockfile and source archive/tree hashes. It shares the
static Alloy `6.2.0` JAR and Java `17` provisioning receipt. Prepare both outside
the validation deadline:

```sh
python3 scripts/oracles/temporal.py prepare \
  --static-tools "$CLAFER_ORACLE_TOOLS" \
  --build-cache /tmp/clafer-temporal-build-UNIQUE /tmp/clafer-temporal-tools-UNIQUE
export CLAFER_TEMPORAL_TOOLS=/tmp/clafer-temporal-tools-UNIQUE/tools.json
python3 scripts/oracles/temporal.py suite --tools "$CLAFER_TEMPORAL_TOOLS" \
  /tmp/clafer-temporal-suite-UNIQUE
python3 scripts/oracles/temporal.py run --tools "$CLAFER_TEMPORAL_TOOLS" \
  identity-scope-2 /tmp/clafer-temporal-run-UNIQUE
python3 scripts/oracles/temporal.py replay --tools "$CLAFER_TEMPORAL_TOOLS" \
  /tmp/clafer-temporal-run-UNIQUE /tmp/clafer-temporal-replay-UNIQUE
```

The builder can reuse an explicit external `STACK_ROOT`; otherwise it creates one
inside the build cache. It requires GMP development headers/library (`libgmp-dev`)
and retains failed build logs with an actionable diagnostic. Invalid or changed
exporter/source/build receipts require rebuilding; validation never provisions
missing tools or skips selected tests. CI prepares the profiles required by its
[validation selection](build.md#ci-profiles) and retains temporal
setup/build logs, notices, tool receipts and execution evidence.

`TemporalExport.hs` calls the unchanged library's `generate` once with JSON, Alloy
and explicit AlloyLtl modes, no scope inference, and a logical `input.cfr` filename.
The receipt retains the full effective `ClaferArgs`, post-analysis IR, original
JSON/Alloy and backend `tmp.als`. The Python capture binds their bytes, the input,
exporter and build receipt. These unsigned hashes provide content identity, not
producer authentication. Source imports and backend escapes are not exposed by
this fixture-only command interface. This is not a general behavioral compiler
admission API.

`AlloyTemporalBridge.java` parses the fresh output with the pinned Analyzer and
selects a recorded command index. It retains the original command, then constructs
a command with the same assertion/run formula and explicit budgets through Alloy's
public AST API. Assertions retain the Analyzer's classical counterexample formula.
It checks the complete signature inventory and rejects incompatible static
`one`/`lone` scopes. Mutable `one`/`lone` signatures may use larger identity
budgets because their singleton population can be replaced across time; mutable
`one` and any `some` signature still require positive capacity. The registered requests supply upper identity scopes for every
signature, including root `1`, signed bitwidth `8`, sequence scope `0`, and
`3..6 steps`. SAT4J, one worker, overflow prevention, no decomposition and every
public `A4Options` field are recorded and checked. Each query has a 30-second wall
limit, 512 MiB heap and 2560 MiB address-space limit. A timeout or incomplete
witness remains unsuccessful even when a prior SAT observation was retained.

An Alloy trace of `n` stored states has `n` transitions including its loop edge;
`steps` bounds that count. A result records all frames, `0 <= loop < n`, static
signature inventories, mutable/immutable field declarations and tuples, plus the
raw Analyzer XML. The adapter checks trace-wide capacities, immutable tuples and
loop bounds. Signature slots can include inactive objects; mutable containment
fields determine live population. Inherited signature extents can overlap, so the
inventory is their union, not the sum of their sizes. Root counts once. No auxiliary
object signatures are omitted. This fixture corpus uses object references and
small multiplicity counts, with no primitive arithmetic; its fixed bitwidth is
not a general arithmetic admission argument.

Success means the completed bounded query has the registered expected outcome.
SAT, `bounded_unsat`, malformed/unsupported capture, resource/tool failure and
timeout remain distinct. Replay validates the entire artifact index, reruns the
actual exporter, checks byte-identical generation/build receipts and reruns the
same query/bounds. It does **not** pin a previously found trace or require a solver
to choose the same witness. Exact source-candidate transport, decoding and lasso
replay belong to [C9](behavioral.md#ownership-and-interfaces). Static exact replay
retains its existing implementation and tests.

### Temporal fixture and witness inventory

The [inventory](../tests/fixtures/temporal/inventory.json) records 29 commands,
source hashes, licenses and complete budgets. Six upstream sources remain in the
external source archive; eight original sources live in
[`tests/fixtures/temporal`](../tests/fixtures/temporal). Every assertion query has
a satisfiable model run with identical budgets. Outcomes are bounded integration
results; no Lean behavioral checker or new theorem is claimed.

These witnesses are hand-checked from T1–T3/T7–T8/T11/T13 and the accepted profile.
Letters denote persistent identities, not names regenerated per frame. The tests
also inspect actual solver witnesses for these distinguishing properties, without
requiring a particular atom naming or choice of lasso presentation.

| Case | Hand-checked trace / required negative result |
| --- | --- |
| Stable triggered machine | The same machine `m` starts in `waiting`, then reaches `done` with its parent still present; a counterexample to the transition is bounded UNSAT. The trigger is mandatory, avoiding a vacuous idle witness. |
| Replaced machine | `m0.a, m1.a, m0.a`, loop to frame 1, with `go` at frame 2: the looping edge replaces the machine and cancels the old obligation. The global assertion has a counterexample at scope 2, while its identity-aware version has none; scope 1 forbids replacement. |
| Both source signs | A machine/context present at frame 0 and absent thereafter, no error, loop on an absent state: both `F error` and its source negation lapse. A persistent parent makes their conjunction impossible; context death alone cannot cancel `F error`. |
| Identity versus population | Live items `i0, i1, i0`, loop to frame 1: one item per state needs two identities. Scope 1 is bounded UNSAT at the same step budget. |
| Fixed parent through absence | `b0.item=i`, then no item, then the same `i` under `b0`, loop to the absent frame. Two boxes exist throughout; changing `i`'s parent is forbidden. |
| Inherited final reference | A fixed head points to `left` then `right` under a persistent owner. It is possible without a modifier, bounded UNSAT with inherited `final`, `finalref` or `finaltarget`; the upstream positive model remains satisfiable for all three checks. |

The inventory separately classifies the accepted response-between and
first-opener precedence-after corrections, `finaltarget` image stability versus
Haskell's stronger per-head equality, and richer structural/arithmetic gaps.
Their immutable dispositions are in the [behavioral contract](behavioral.md#pattern-and-errata-completeness).
The 29 queries do not qualify those broader domains. In particular, the one-head
finality examples do not establish agreement for multi-head image-preserving swaps.

### Comparing the final 0.5.7 release

Keep this candidate and static profile intact. Before adopting release bytes:

1. Record the final immutable commit/tag resolution, archive/tree/lockfile hashes
   and licenses. Compare it against the candidate, especially grammar, desugaring,
   `AlloyLtl.hs`, reference inheritance, errata and build dependencies.
2. Build a separate exporter/cache/profile with the same options. Recompile all
   registered sources, retain both paired receipts and compare generated commands,
   bounds and completed outcomes, inspecting full traces where behavior differs.
3. Reassess the known comparison gaps against accepted independent semantics;
   neither changed output nor test agreement silently changes source meaning.
   Retain both discrepancy directions and unresolved failures with their evidence.
4. Obtain explicit source/profile delta review before changing the pin. Rerun
   the complete static and temporal qualification after an accepted update;
   preserve historical receipts for the old candidate.

## PR113 delta qualification candidate

`behavioral-pr113-9a0f16e/v1` selects the immutable later Haskell revision in the
[source register](sources.md#pr113-delta-candidate). It is a qualification
candidate awaiting independent review. The primary behavioral pin, old temporal
profile, static profile and their capture/replay protocols remain unchanged.

Reuse assessment: `temporal.py` supplies duplicate-key JSON parsing, bridge
compilation, bounded solving and complete trace validation; `temporal_build.py`
supplies retained build diagnostics. The pinned semantics runtime supplies
verified downloads and Java provisioning. Python's standard library supplies
processes, hashes and archives. The new Haskell adapter calls `readModel`,
`generate`, `alloyNames`, `toAlloyNames`, `astrModule`, `isDynamicModule`,
`genAlloyLtlModule`, `genExplicitModule` and the scope metadata APIs. A separate
builder binds the new revision and exporter without altering historical build
identities. The declaration/field inspector reuses the pinned Analyzer's public
`CompModule`, signature, field and command APIs. The first run query also emits
that inventory from its parsed module, avoiding a separate JVM launch and
parse. The driver validates the complete layout and command inventory before
accepting the query outcomes. Each query still runs in a fresh process with
the same deadline, memory limits and solver options; inspection and query
artifacts remain in the evidence bundle. The standalone inspector remains
available for inspection-only calls. No additional packages, Lean dependencies,
solver or printer are introduced.
These external adapters are tested, unproved boundaries. Original adapters and
local fixtures are MIT; upstream fixtures stay in the external archive with its
MIT notice. Existing Alloy/SAT4J license obligations remain unchanged.

```sh
python3 scripts/oracles/pr113.py prepare --static-tools "$CLAFER_ORACLE_TOOLS" \
  --build-cache /tmp/clafer-pr113-build-UNIQUE /tmp/clafer-pr113-tools-UNIQUE
export CLAFER_PR113_TOOLS=/tmp/clafer-pr113-tools-UNIQUE/tools.json
python3 scripts/oracles/pr113.py suite --tools "$CLAFER_PR113_TOOLS" \
  --old-tools "$CLAFER_TEMPORAL_TOOLS" /tmp/clafer-pr113-suite-UNIQUE
python3 scripts/oracles/pr113.py replay --tools "$CLAFER_PR113_TOOLS" \
  --old-tools "$CLAFER_TEMPORAL_TOOLS" \
  /tmp/clafer-pr113-suite-UNIQUE/direct-swap-target /tmp/clafer-pr113-replay-UNIQUE
```

The [profile](../scripts/oracles/pr113-profile.json) pins source archive/tree,
Stack/GHC and generated dependency lock. Each capture retains the registered
source import closure, effective options, original JSON/Alloy, explicit text,
original and explicit scope files, post-analysis IR, backend input, renamed IR
and complete forward UID/name map from the same compilation. Re-emitting the
captured backend input through the library must reproduce `generate`'s complete
Alloy bytes; the explicit printer call must reproduce its explicit bytes.
Schema checks require modifier arrays, reject legacy scalar fields mixed into
this revision, and check global bindings, declaration identities and injectivity.
The Analyzer's actual signature hierarchy, field ownership, declared endpoints
and types must match the captured map. No name is reconstructed by removing a
prefix. Historical comparisons match unique authored declaration paths between
revisions, retaining that correspondence and both build receipts.

The [inventory](../tests/fixtures/pr113/inventory.json) includes all 64 temporal
upstream `tmp_` sources and the static `tmp_TrafficLight5` example, plus original
witnesses. Each source is freshly generated, its explicit text is recompiled,
and the second explicit output must be byte-identical. All run/assertion
commands are matched, including lifted nested assertions whose command order
changes. Assertions require a satisfiable paired model run at the same budgets;
the `names` fixture also demands a real counterexample to a false assertion.
The scope-identity upstream example remains bounded UNSAT at its original
inferred scope; that result is not a completeness claim.

Original and explicit queries use the **original generation's** inferred scopes
(default `1`) or the local witness's registered identity capacities. The explicit
model's `--ss=none` defaults never replace those scopes. Both use signed bitwidth
`8`, overall scope `1`, `1..trace_length` steps, the captured `--tl` value, SAT4J,
identical options and the existing 30-second/512-MiB resource limits. Source
pragmas are read by the pinned importer. Local witnesses use 3 or 4 steps;
upstream fixtures retain their effective trace lengths. All fields, frames,
loop index, commands and runtime identities are retained. Real/double explicit
output, temporal Choco solving, malformed inputs, tool failures and timeouts
remain distinct from completed SAT or bounded UNSAT.

| Distinguishing obligation | Registered evidence |
| --- | --- |
| Each reference conjunct, direct and inherited, in both orders | Two continuing heads swap targets: `finaltarget` permits it, both modifiers reject it. Replaced heads change the image: `finalref` permits it, both modifiers reject it. |
| Head identity versus image | Both modifiers permit replacing a head while retaining its target; `final` forbids replacement. |
| Target set versus bag multiplicity | Three replaced heads change target counts from `{A,A,B}` to `{A,B,B}`. Both orders preserve the image `{A,B}` and permit this; `final` forbids replacement. Tests inspect live head identities and reference tuples. |
| Response-between | `q`, then `p`, then no response, then `r` forever: the old revision permits the trace and the candidate rejects it. |
| First-opener precedence | `q,p,q,s` with the last state looping: an `initially`-attached pattern rejects the trace in the candidate and accepts it in the old revision. |
| Attachment | A response at the first opener can satisfy the `initially`-attached precedence pattern; a later opener followed by `p` without a new response violates the implicitly always-attached constraint. |
| Naming and schema | Reserved/derived-name collisions, apostrophe collisions, repeated nested names, an empty abstract extent, mapping/field mutations and missing/scalar/mixed/unknown modifier arrays. |

Old/new runs preserve discrepancy directions, including the old stronger
`finaltarget` and its missing combined image constraint. Accepted pinned
`PatternExamples` and surface obligations supply hand-checked expectations;
no unaccepted upstream adapter or witness change is consumed. The tests inspect
actual distinguishing traces without requiring a particular atom naming.

These checks establish printer fixed points, complete paired command coverage
and bounded run/check outcome agreement. They do not enumerate equal trace sets,
prove exact-lasso equivalence, or implement source-to-Alloy transport. Those
remain [C9 obligations](behavioral.md#ownership-and-interfaces) and the separate
Lean explicit-form preservation task. Hash receipts are unsigned identity
records, and replay reruns the compiler and bounded query; it may choose another
witness. Acceptance and any primary-pin amendment require independent review.

## Implementation and test links

`impl~compiler-pr113-oracle-tools~1`

The [candidate driver](../scripts/oracles/pr113.py),
[builder](../scripts/oracles/pr113_build.py),
[closed protocol](../scripts/oracles/pr113_protocol.py),
[Haskell capture](../scripts/oracles/PR113Export.hs) and
[Analyzer inspector](../scripts/oracles/AlloyPR113Inspect.java) implement the
revision-specific capture, naming, explicit-roundtrip and replay contract above.

Covers:
- `req~compiler-temporal-oracles~1`

`utest~compiler-pr113-oracle-regressions~1`

[Candidate tests](../tests/test_pr113_oracles.py) execute the complete inventory,
check independent modifier/pattern witnesses and meaningful assertions, mutate
schemas/mappings/fields and every indexed artifact, and freshly replay a paired
revision discrepancy. [Inspection orchestration tests](../tests/test_pr113_fusion.py)
reject missing or malformed shared inventories, retain timeouts and verify that
the first runs are used once while every assertion keeps its own fresh query.
CI provisions this profile for full qualification and when
[reference dependencies change](build.md#ci-profiles).

Covers:
- `req~compiler-temporal-oracles~1`

`impl~compiler-temporal-oracle-tools~1`

The [temporal driver](../scripts/oracles/temporal.py),
[builder](../scripts/oracles/temporal_build.py),
[exporter](../scripts/oracles/TemporalExport.hs),
[Analyzer adapter](../scripts/oracles/AlloyTemporalBridge.java), profile and
inventory implement the distinct bounded comparison protocol described above.

Covers:
- `req~compiler-temporal-oracles~1`

`utest~compiler-temporal-oracle-regressions~1`

[Temporal tests](../tests/test_temporal_oracles.py) execute every registered query,
inspect independent distinguishing witnesses, validate matched run/check budgets,
rerun capture/query replay, mutate receipt artifacts and traces, and test missing
or changed exporters, invalid scopes, missing output and real process deadlines.
Controlled substitutes exercise process/build failures; these are not claimed
SAT4J timeouts or semantic counterexamples. Existing static rejection/replay tests
remain mandatory alongside this suite.

Covers:
- `req~compiler-temporal-oracles~1`

`impl~compiler-oracle-tools~1`

The [wrapper](../scripts/oracles/oracle.py), profile, fixture inventory and CI
implement setup, identity checks, capture and comparison/replay boundaries.

Covers:
- `req~compiler-oracles~1`

`utest~compiler-oracle-regressions~1`

[Oracle tests](../tests/test_oracles.py) exercise actual exporter/Lean/Alloy runs,
replay, every capture artifact's hash binding, mismatched paired bytes, wrong
backend, temporal ASTs, unsupported inputs, insufficient width, missing/changed
tools and timeout outcome separation. The timeout test deliberately stalls a
substitute process to test the real process deadline; it is not an observed
SAT4J timeout. Byte-tampering tests enumerate all five receipt-bound artifacts;
that finite mutation coverage is not a proof of arbitrary protocol security.

Covers:
- `req~compiler-oracles~1`
