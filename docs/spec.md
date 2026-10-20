# Repository and planning requirements

These requirements cover the current documentation and workflow. The structural
direction and upstream-core M2 scope are selected; issue #2's detailed contract
candidate still requires repository review. Future executable behavior is reserved
below, not declared implemented or proved. There is no compiler or Lean toolchain.

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent explain the selected structural Clafer-to-Alloy direction,
its relationship to Clafer Semantics and the Haskell comparison compiler, and the
absence of an implementation. Distinguish reviewed decisions, contract candidates
and future implementation/proof promises. Contract adoption precedes dependent
manual intake; planning tickets do not start implementation. Keep the repository
and Project private until the maintainer explicitly requests publication.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Contribution and validation workflow

`req~intentbond-workflow~1`

Pin IntentBond to an immutable source revision. Keep intent, requirements and
artifact links together, and run the repository check through IntentBond before
handoff. Retain evidence outside source. Exit 4 means automation passed with
semantic review pending, never approval. CI must preserve evidence and expose
that distinction. Scope changes require explicit review.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Issue tracking and manual intake

`req~github-tracking~1`

Use repository issues and a private Project with Todo, In Progress, and Done.
Tasks describe scope, acceptance criteria, sources/requirements, and dependencies.
Planning tickets do not trigger implementation. IntentMade registration uses manual
intake and draft PR publication; deployment configuration and credentials stay
outside this repository.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Feature and interface planning contract

`req~compiler-scope~1`

Maintain a reviewable three-column M1/M2/deferred feature matrix grounded in the
pinned upstream admission declarations and Haskell grammar. M1 is the exact
guarded effective core. M2 selects the upstream typed static core and inherited
realization, with every accepted constructor/surface form enumerated and owned by
an implementation/proof/test task. Explicitly classify primitives, arithmetic,
defaults, behavior and erased syntax. Specify resolved-IR before text input,
malformed/unsupported/semantic outcomes, spans, deterministic output, scopes,
bitwidth, definedness and finite quantifier domains. Retain narrow review decisions;
do not imply compatibility or implementation beyond the selected contract.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Architecture, assurance and source planning contract

`req~compiler-boundaries~1`

Document one-way compiler-to-semantics ownership and proposed module handoffs.
Keep independently defined source/target satisfaction, concrete encode/decode
relations, soundness, bounded completeness, frontend elaboration and serialized
text/runtime trust boundaries explicit. Bounds/representation assumptions must
not assume the preservation conclusion. Pin candidate semantic and Haskell
baselines, retain source locators/licenses and define reviewed upgrades. No
research tag is required. Reserve future behavioral requirement IDs without
inventing implementation/proof coverage; acceptance review precedes dependent
manual intake. This requirement currently promises a documented contract, not
an implemented dependency graph or proved compiler.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Documentation and scaffold artifacts

`impl~scaffold-boundary~1`

[README](../README.md), [intent](intent.md), [security policy](../SECURITY.md), and
[license](../LICENSE) describe the current boundary. GitHub visibility is an
external setting: verify it separately before reporting repository publication.

Covers:
- `req~scaffold-boundary~1`

`impl~intentbond-workflow~1`

[Contribution guidance](../CONTRIBUTING.md), [agent instructions](../AGENTS.md),
[pin](../requirements/intentbond.txt), [scope](../scope.json),
[check entrypoint](../scripts/check.sh), and [CI](../.github/workflows/ci.yml)
provide the scaffold validation workflow. These checks do not verify a compiler.

Covers:
- `req~intentbond-workflow~1`

`impl~github-tracking~1`

[Project configuration](../.github/project.json), [ticket helper](../scripts/tickets.py),
[task template](../.github/ISSUE_TEMPLATE/task.yml), and contribution guidance
support issue tracking. IntentMade's private deployment owns registration and
manual intake settings; repository checks cannot attest to their live state.

Covers:
- `req~github-tracking~1`

`impl~compiler-scope-contract~1`

The [feature matrix and constructor/surface inventories](architecture.md#feature-matrix),
[API contract](architecture.md#resolved-ir-api-and-cli-sequence),
[arithmetic policy](architecture.md#arithmetic-definedness-and-finite-observation),
and [intent](intent.md) are the planning deliverables. Their task ownership and
explicit deferred forms are review targets, not compiler test evidence.

Covers:
- `req~compiler-scope~1`

`impl~compiler-boundaries-contract~1`

The [ownership map](architecture.md#ownership-and-dependencies),
[assurance contract](architecture.md#independent-meanings-and-theorem-obligations),
[review handoff](architecture.md#review-handoff), [source register](sources.md)
and reservation table below implement the documentation obligation. No Lean
declaration or compiler theorem is claimed by these Markdown artifacts.

Covers:
- `req~compiler-boundaries~1`

## Reserved implementation requirements

The names below reserve future IDs of the form `req~NAME~1`; they are not active
OFT requirements or coverage declarations. Each task introduces its behavioral
promise with real source/proof/test artifacts and the required review. The two
planning requirements above are active documentation obligations; #5 must extend
or refine the boundary requirement with actual build/import evidence before
claiming implementation coverage. Do not use this table as fake proof coverage.

| Reserved name(s) | Owning roadmap issue | Future promise |
| --- | --- | --- |
| `compiler-build` | [#5](https://github.com/kbak/clafer-compiler-lean/issues/5) | Pinned Lake/native build and proof-aware CI |
| `compiler-oracles` | [#6](https://github.com/kbak/clafer-compiler-lean/issues/6) | Reproducible three-oracle profile and corpus |
| `compiler-ir` | [#7](https://github.com/kbak/clafer-compiler-lean/issues/7) | Executable admitted IR and upstream interpretation |
| `compiler-alloy-core`, `compiler-bounds` | [#8](https://github.com/kbak/clafer-compiler-lean/issues/8) | Independent bounded target semantics |
| `compiler-alloy-text` | [#9](https://github.com/kbak/clafer-compiler-lean/issues/9) | Hygienic deterministic serialization and assurance |
| `compiler-structural-encoding` | [#10](https://github.com/kbak/clafer-compiler-lean/issues/10) | Complete guarded structural translation |
| `compiler-structural-correctness` | [#11](https://github.com/kbak/clafer-compiler-lean/issues/11) | Soundness and bounded completeness |
| `compiler-differential`, `compiler-instance-decode` | [#12](https://github.com/kbak/clafer-compiler-lean/issues/12) | Exact-candidate comparisons and strict decode |
| `compiler-inherited-realization` | [#13](https://github.com/kbak/clafer-compiler-lean/issues/13) | Selected inherited-field/abstract-family extension |
| `compiler-expressions` | [#14](https://github.com/kbak/clafer-compiler-lean/issues/14) | Executable typed expressions and semantic agreement |
| `compiler-arithmetic` | [#14](https://github.com/kbak/clafer-compiler-lean/issues/14), [#15](https://github.com/kbak/clafer-compiler-lean/issues/15) | Definedness, finite observation and no-overflow correspondence |
| `compiler-expression-encoding` | [#15](https://github.com/kbak/clafer-compiler-lean/issues/15) | Static constraint preservation |
| `compiler-parser` | [#16](https://github.com/kbak/clafer-compiler-lean/issues/16) | Accepted grammar/parser correspondence |
| `compiler-diagnostics` | [#16](https://github.com/kbak/clafer-compiler-lean/issues/16), [#19](https://github.com/kbak/clafer-compiler-lean/issues/19) | Stable diagnostic categories, codes and locations |
| `compiler-resolution`, `compiler-defaults` | [#17](https://github.com/kbak/clafer-compiler-lean/issues/17) | Declarative resolution/defaulting success relation |
| `compiler-constraint-elaboration` | [#18](https://github.com/kbak/clafer-compiler-lean/issues/18) | Typed source elaboration and meaning |
| `compiler-cli` | [#19](https://github.com/kbak/clafer-compiler-lean/issues/19) | Native resolved-IR CLI and output protocol |
| `compiler-pipeline-correctness`, `compiler-telematics` | [#20](https://github.com/kbak/clafer-compiler-lean/issues/20) | Source pipeline, composed assurance and complete example |
| `compiler-qualification`, `compiler-performance` | [#21](https://github.com/kbak/clafer-compiler-lean/issues/21) | Private acceptance evidence and reproducible measurements |

The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) owns scheduling.
Upstream requirement IDs retain their upstream repository namespace; citing a
theorem or ticket does not import its coverage into this repository.
