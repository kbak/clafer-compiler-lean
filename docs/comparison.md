# Exact three-way structural comparison

[Issue #12](https://github.com/kbak/clafer-compiler-lean/issues/12) is selected after
merged PRs #24, #27 and #29. It connects the native structural compiler, checked
serializer, actual Alloy Analyzer and executable decoder to the existing exact
candidate protocol. It adds bounded evidence, not the unfinished source-soundness
or bounded-completeness theorems listed in [structural correctness](structural-correctness.md).
Issue #11 was closed with its partial representation delivery; closure does not
establish those missing properties.

## Reuse and boundaries

The implementation reuses the immutable semantics dependency's `protocol`,
`capture`, `comparison`, `relation`, `candidates`, `mutations`, `checker_runtime`
and `alloy_runtime` adapters. These already implement strict JSON loading,
paired Haskell capture, source admission, exact pins, object isomorphism,
MT19937 generation, exhaustive enumeration, occurrence-collapse mutation and
deletion shrinking. New infrastructure is limited to the downstream interface.

The existing upstream Java bridge assumes Haskell's `run show for 1`, virtual
root and upper-scoped signatures. It cannot consume the native serializer's
explicit root and command unchanged. The new Java adapter reuses its AST audit,
command recorder and tuple reader, using the same pinned Analyzer and SAT4J
options. Lean `List`, `Except`, the existing structural decoder and checked
serializer supply the native implementation. Python standard libraries supply
process management and JSON transport; no additional package, solver, parser
library or vendored source is introduced. Reused upstream code remains in its
MIT-licensed dependency. The small new source fixture and adapters are original
project MIT code.

## Data and proved mapping

[Decode.lean](../ClaferCompiler/Backend/Alloy/Decode.lean) adds `Structural.Candidate`,
`candidate` and `decodeCandidate`. The candidate has an ordered object list,
distinguished root, declaration-ID membership rows and owner/head and head/target
rows. IDs and object labels remain independent of names. Two bag heads sharing
an owner and target remain separate rows and objects.

`proof~compiler-instance-decode~1`

`candidate_members`, `candidate_containment` and `candidate_references` prove
exact row membership against the input observation. [Kernel witnesses](../tests/Decode.lean)
check the two-head bag export and preservation of a missing-owner negative. They assume neither source
nor target satisfaction. `decodeCandidate` reuses #11's `decode` and therefore
its table-shape/root checks and existing representation results. These new
row theorems do not prove that parsing external JSON is correct. Native Lean/C,
Python, Java, Analyzer translation, SAT4J and JSON extraction remain external
trust boundaries; the raw XML is retained as additional inspection evidence.

Covers:
- `req~compiler-instance-decode~1`

The strict witness adapter requires exactly the generated signatures and fields,
duplicate-free opaque atom labels, complete object-carrier membership, binary
unique tuples and typed endpoints. It exports tables to the actual native Lean
decoder. It never splits atom names or reconstructs identity from display names.
Malformed external tables fail separately; well-formed semantic violations are
not discarded by the decoder.

## Common experiment domain

The capture must pass the original immutable receipt and M1 admission checks.
Source, post-analysis IR, effective defaults and same-generation Haskell Alloy
remain paired. The adapter maps captured UIDs to sequential numeric input IDs,
including a real synthetic root, and reuses the captured ranks/unused flags.
This adapter is test infrastructure, not the #19 production JSON/IR CLI.

Each supplied candidate is sent unchanged to the upstream verified checker and
the Haskell comparison. The native backend compiles the same imported effective
core and manual upper bounds, then the checked serializer emits its complete
command. An added exact-candidate fact fixes every object, extent and relation.
The source UID scopes and bitwidth agree across all three paths. Haskell's root
is virtual; the native target represents it explicitly. The native object budget
is the sum of all supplied upper scopes including root; it does not sum actual
inherited extents or impose extra constraints on a fitting candidate. Every native
signature has an explicit scope; its overall/sequence defaults have no unscoped
user signature or sequence expression to bound. Both actual commands and all
solver options are retained, including this layout difference.

The two independent solver processes execute concurrently after native compilation;
the shared checker is accessed sequentially. Each process retains its own timeout,
heap, options and evidence. Both source truth values are retained. A SAT result requires strict decode and
an exact object bijection with the original candidate, followed by an independent
checker verdict on the decoded candidate. Negative candidates are still solved;
no prefilter by satisfaction is permitted. A candidate outside the common receipt,
type or bound domain is malformed/unsupported, never agreement or bounded UNSAT.
The compiler itself keeps its wider admitted M1 API domain.

`agree_satisfies` and `agree_violates` require completed agreement on both solver
paths. Compiler acceptance/checker rejection and the reverse remain distinct,
as do Haskell discrepancies, pin/decode failure, unsupported input, timeout,
resource failure and operational error. UNSAT only excludes the fixed candidate
within this experiment. Even a completed exhaustive finite domain is not a
universal compiler correctness proof or unbounded source UNSAT.

## Replay, search and minimization

Prepare the tools using [the existing procedure](oracles.md). Each output directory
must be new and external. Examples use a previously captured `capture/` bundle:

```sh
python3 scripts/comparison/compare.py compare --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/capture-UNIQUE/capture candidate.json /tmp/three-way-UNIQUE
python3 scripts/comparison/compare.py replay --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/three-way-UNIQUE /tmp/three-way-replay-UNIQUE
python3 scripts/comparison/compare.py search --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/capture-UNIQUE/capture /tmp/search-UNIQUE --mode seeded --seed 120021 --count 6
python3 scripts/comparison/compare.py search --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/tiny-capture-UNIQUE/capture /tmp/enumeration-UNIQUE --mode exhaustive
python3 scripts/comparison/compare.py minimize --tools "$CLAFER_ORACLE_TOOLS" \
  /tmp/discrepancy-UNIQUE /tmp/minimized-UNIQUE
```

The committed tiny source has four candidates at upper scope one, all of which
are checked. Six bag candidates use seed 120021. Inheritance and shadowing use
width 10 to satisfy the existing conservative range argument; the small fixtures
use width 8. These test sizes do not restrict the comparison API.

The upstream labelled-table domain keeps a fresh singleton root, all membership
subsets within UID scopes, unused ambient objects and all typed relation subsets.
It performs no satisfaction filtering or symmetry reduction. Root-invalid and
malformed inputs are separate rejection tests. Seeded sampling uses the pinned
MT19937 distribution, not a claim of uniformity over candidates. Search records
requested/admitted/completed denominators and budget termination. Minimization
retains each attempted three-way replay and only claims deletion-minimality for
the upstream reduction order; an inconclusive trial prevents that claim.

Evidence retains captured sources/IR/receipts, original and pinned candidates,
native model transport, generated Alloy, exact pin, maps, raw XML/JSON, decoded
candidate, bijection, checker outputs, commands, options, source/tool hashes and
an exact replay command. Runtime builds also retain the downstream source bytes.
Replay refuses changed input/output, source or tool identities. These records are
unsigned evidence, not provenance authentication. Actual discrepancies require
the existing [triage policy](oracles.md#discrepancy-triage) and an issue before
semantic changes.

## Required validation

[Native transport](../tests/ComparisonNative.lean) invokes actual admission,
compilation, rendering and decoding. [Python regressions](../tests/test_comparison.py)
exercise real captures, all three oracles, inherited membership, reference cycles,
shadowed names, exhaustive tiny enumeration, seeded
candidates, exact replay, deletion minimization, malformed bytes, unsafe width,
strict decoder mutations and an actual process deadline with a stalled executable.
The latter tests deadline handling, not an observed SAT4J timeout.

Deliberate defects cover occurrence collapse, missing local cardinality/group
constraints, missing declaration disjointness, swapped reference endpoints and
an extra false fact. Disjointness is implemented by `extends`, so its mutation
uses subset declarations plus equivalent explicit count bounds; it does not
pretend there is a disjointness fact to remove. Mutations are opt-in comparison
experiments, never enabled in production compilation. Their original checker
candidate is unchanged. Passing finite experiments do not complete #11's missing
universal preservation obligations. Scope, coverage floors, pins and manual review
remain unchanged; IntentBond exit 4 leaves semantic review pending.
