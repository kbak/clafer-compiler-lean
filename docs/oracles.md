# Reproducible comparison tools

[Issue #6](https://github.com/kbak/clafer-compiler-lean/issues/6) supplies external
Haskell, Lean and Alloy tools for the adopted structural contract. It reuses
`scripts/verification/` from the immutable Clafer Semantics Lake dependency.
These original runs compare Haskell-generated Alloy with the upstream Lean checker.
Selected #12 adds the [three-way comparison](comparison.md) with native-generated Alloy.
There is no new theorem in this task.

## Tools and profile

The [machine-readable profile](../scripts/oracles/profile.json) and
[source register](sources.md) pin Haskell `15adb2216909421bcb5022174d2d84ef2b42307c`,
semantics `1454e3bd2ce9697923cdcef3863c816651ffc147`, Lean 4.35.0 and Alloy 6.2.0
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

Provisioning is outside the unchanged 120-second IntentBond check deadline.
Linux x86_64 supports upstream automatic Haskell/Java downloads with hash checks;
other platforms need explicit compatible tools. `CLAFER_CAPTURE`,
`CLAFER_CAPTURE_BUILD`, `CLAFER_CAPTURE_CACHE`, `CLAFER_ALLOY_JAR`,
`CLAFER_JAVA_HOME` and `CLAFER_ALLOY_CACHE` select external tools/caches during
provisioning. Invalid explicit settings fail. `tools.json` retains their resolved
paths outside source. Checks require this record, revalidate identities and
recompile the bridge; they do not silently provision missing tools or skip tests.
Fresh snapshots reuse dependency packages and external tools, rebuilding project
outputs. Manually dispatched CI retains setup logs, notices, tool receipts and all
oracle evidence; automatic hosted runs are deferred during development.
Preparation validates the outer and inherited manifest identities, then shares
missing nested checker dependencies through relative links to the already
prepared packages. Existing clean nested checkouts are preserved; dirty or wrong
revisions fail. The links remain inside a copied package tree, avoiding a second
Mathlib download/build without changing manifests or upstream source meanings.

The following commands take new external output directories. A bounds file is a
JSON object with `root: 1` and an explicit natural upper bound for each compiler
UID; use the [fixture inventory](../tests/fixtures/oracles/inventory.json) for
examples. Candidate JSON uses the upstream object/member/containment/reference
format, not the future compiler IR.

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
all admitted candidates or future M2 semantics. The full upstream search and
mutation utilities remain available at the pinned revision for #12.

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
or an assertion that each embedded class has a mapped license. #21 must reconcile
all packaged dependencies (including Haskell/JDK/native/runtime dependencies)
before any packaging decision. This task keeps tools and licenses external and
does not distribute their binaries or change repository licensing.

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
new tool is allowed. Known empty-group and keyword/numeric-default differences
remain in the [source register](sources.md); effective-value admission does not
prove authored-source default agreement.

## Implementation and test links

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
