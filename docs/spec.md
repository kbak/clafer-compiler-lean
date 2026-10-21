# Repository and planning requirements

These requirements cover the current documentation and workflow. The structural
contract was adopted by issue #2 and merged PR #22. Build, comparison and structural
IR tasks #5–#7 were accepted through PRs #23–#25; target task #8 through PR #26.
Structural backend #10 was accepted through PR #28. Selected task #11 adds the
finite representation proof layer; global preservation remains unfinished. Future
compiler behavior is reserved below, not declared implemented or proved.

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent explain the selected structural Clafer-to-Alloy direction,
its relationship to Clafer Semantics and the Haskell comparison compiler, and the
build bootstrap, admitted structural IR, independent target core and selected
structural backend. Global compiler preservation remains unproved. Distinguish
reviewed decisions, contract candidates and future implementation/proof promises. Contract adoption precedes dependent
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
semantic review pending, never approval. During development, local checks remain
mandatory and hosted CI runs only on manual dispatch. When run, CI must preserve
evidence and expose that distinction. Scope changes require explicit review.

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
manual intake. The build enforces module ownership/import boundaries and exercises
independent upstream imports. The remaining semantic/compiler contracts are
future obligations, not proved compiler properties.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible build and assurance bootstrap

`req~compiler-build~1`

Pin the Lean toolchain and Clafer Lake dependency to the source register and retain
the upstream-compatible transitive manifest. Build every owned compiler and Lean
test module, including modules unreachable from the root import. Build and run
the native `clafer-compiler --version` bootstrap; reject all other invocations
with exit 2, empty stdout and a diagnostic. Kernel-prove only the pure version
and empty-argument response equations at this stage, not IO or compiler correctness.

Every full check must replay the project/test kernel declarations and audit their
module origins, including private/generated declarations. Reject project axioms,
`sorry`/`admit`, unsafe/partial declarations, and transitive axioms other than
`propext`, `Classical.choice` and `Quot.sound`. Check the executable import closure
excludes upstream semantics and proof-only modules. Document native IO/tooling
trust. Fail on absent tools, failed gates, empty/skipped regressions and unknown
module ownership. Retain source-bound IntentBond evidence before handoff.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Reproducible comparison oracles

`req~compiler-oracles~1`

Reuse the immutable upstream capture/import/comparison adapters with the pinned
Haskell library, Stack/GHC/dependency profile, Lean semantics and Alloy 6.2.0 JAR.
Retain source and tool hashes, same-generation IR/Alloy receipts, actual Java
vendor/build, effective static SAT4J options, explicit per-UID scopes and signed
bitwidth. Run the actual tools on positive and negative candidates; preserve
reference occurrences. The initial profile uses Java 17 and upstream bitwidths
1–16 with independent range admission. Reject temporal source/backend dispatch.

Run the finite checker only after its guarded constraint-free admission. Keep
inherited fields, primitive integer references and expressions unsupported;
leaf abstract inheritance remains admitted when its guards hold. Inventory
structural, set/bag, group, inheritance, reference-cycle, shadowing and numeric
fixtures with immutable provenance and licenses. Preserve bundled distribution
notices externally; this task authorizes no packaging or publication.

Missing tools, modified inputs/tools, unsupported domains, timeouts, resource
limits, malformed input and errors must remain distinct from agreement or bounded
UNSAT. Required checks fail rather than skip. Retain exact candidates, both
outputs, options and replay instructions outside source. Discrepancies require
minimized evidence, independent expected semantics and an issue before semantic
changes. Haskell is supplementary evidence; no downstream compiler or new proof
is claimed. #12 owns adding downstream compiler Alloy to the comparison.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Executable structural IR and admission

`req~compiler-ir~1`

Provide finite executable M1 declaration tables with stable input IDs distinct from
names, resolved parent/super/reference edges, effective bounds, optional authored
metadata and original byte spans. Preserve declaration/reference-head identity;
never merge repeated names or targets. Resolve raw IDs deterministically, rejecting
duplicates, dangling edges, malformed metadata/certificate shape, invalid intervals
and cyclic parent/super graphs. Permit reference cycles. Use checked ranks and
unused-abstract certificates for exactly the upstream guarded effective domain.

Interpret all semantic fields into the pinned independent effective core. Prove
both directions of guard agreement, successful admission's actual upstream
well-formedness/support, preservation of the original typed table, and completeness
with suitable certificates. Prove finite lookup soundness/completeness under unique
IDs. Do not confuse admission with candidate satisfaction or bounded UNSAT.

Specify the closed versioned `clafer-ir/1` JSON interchange and deterministic
malformed/unsupported diagnostics, including strict types, duplicate-key rejection
and explicit effective-only provenance. Implement version/profile selection on
already decoded data; file/JSON parsing and diagnostic serialization remain #19.
Reject unknown profiles and primitives; no static expression or inherited semantics
are admitted by extension placeholders. Retain tested raw resolution/native behavior
separately from the proved typed-core boundary and from future serialization.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Independent static Alloy target

`req~compiler-alloy-core~1`

Provide resolved static unary/binary target syntax and an admission API that
rejects malformed references, bindings, arities and declaration hierarchies.
Define finite target instances and compositional relation, formula, declaration,
fact and run/check satisfaction independently of source semantics and compilation.
Preserve atom identity, parent inclusion, sibling/top-level disjointness, Alloy's
abstract-leaf behavior, owner-first field direction and fiber multiplicity.
Distinguish malformed candidates from well-formed violating candidates.
Document auxiliary/unused atom policy and the source invariants #10 must generate.

Maintain the construct correspondence and retained source identity against the
official reference. Kernel-check constructor laws and independent truth tables,
and compare representative equivalent formulas through the pinned real Analyzer.
Keep formal target properties distinct from tested Analyzer correspondence and
future serialization/source preservation proofs. See the [target contract](alloy-core.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Explicit target bounds and checked cardinalities

`req~compiler-bounds~1`

Require complete explicit exact/upper scopes and the accepted signed bitwidth
profile. Reject incompatible signature-multiplicity scopes and unsafe literal
or count ranges before evaluating a candidate. Use conservative finite column
budgets, including binary endpoint products and union inventories, independently
of facts and successful satisfaction. Check every fact/command branch and binder
body. Count distinct tuples, retain runtime representability checks and propagate
undefined integer observations distinctly from false. Scope allocation numerals
and multiplicity predicates do not themselves introduce Alloy integer expressions.

Preserve valid scopes excluding every model as unsatisfiable constraints; future
source compilation may express conflicting declaration multiplicity as a fact.
Do not infer scopes, encode infinity as an integer, silently wrap arithmetic or
add richer M2 integer operations. State the proof/test boundary of range analysis.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Guarded structural encoding

`req~compiler-structural-encoding~1`

Translate the exact admitted M1 effective IR into the independent static target
with deterministic declaration/field allocation and complete explicit ID scopes,
total object budget and signed bitwidth. Preserve declaration and reference-head
identity, inherited membership, owner-first containment/dereference, set/bag keys,
local intervals and union-of-child-head group counts. Enforce root singleton and
freshness, typed endpoints, used-object coverage, abstract cover including empty
families, and global incomparable declaration disjointness. Reject non-M1 inputs
through existing admission; do not narrow the source domain or silently drop facts.

Return checked target syntax/bounds and a source-ID/name/span map with obligation
labels. Distinguish malformed manual bounds, unsafe range profiles and internal
generation errors from contradictions: well-formed scopes excluding all models
still compile. No inferred bounds or implicit solver calls. Prove local inventory,
identity, field-direction and generated-fact lemmas; test positive/negative cases
and omission mutations against independent source meaning. Keep finite tests and
local proofs distinct from global soundness, bounded completeness, executable
encode/decode and text/CLI assurance, which remain dependent tasks. The
[encoding contract](structural-encoding.md) specifies the exact layout and handoff.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Finite structural representation

`req~compiler-structural-representation~1`

Provide an executable finite shared-object presentation and in-memory encoder and
decoder for the accepted structural target layout. Preserve declaration extents,
containment tuples and distinct reference heads. Distinguish malformed/root decode
errors from retained semantic violations. State the concrete bijection, root,
extent and active-role tuple equations, including all target atom coverage and
unused-slot policy, independently of either satisfaction relation.

Kernel-prove the encode/decode data round trip under explicit table/root hygiene,
and derive decoder success and a concrete representation from satisfaction of an
actual successful compiler output, including live-atom coverage from target
constraints. Exercise nontrivial bag witnesses, semantic violations, renamed atoms
and malformed tables. Keep these results distinct from the unfinished global
source-soundness, bounded-completeness and compiled-bank composition obligations
of #11, specified in the [correctness work](structural-correctness.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Documentation and workflow artifacts

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
provide the validation workflow, including real Lean/kernel/native gates. These
checks do not establish compiler correctness.

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
planning requirements above remain active; the boundary requirement also has
actual build/import enforcement under #5. Do not use this table as fake proof
coverage.

| Reserved name(s) | Owning roadmap issue | Future promise |
| --- | --- | --- |
| `compiler-alloy-text` | [#9](https://github.com/kbak/clafer-compiler-lean/issues/9) | Hygienic deterministic serialization and assurance |
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

The active [oracle contract and artifacts](oracles.md) cover #6; the
[IR contract and artifacts](ir.md) cover #7 above.
The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) owns scheduling.
Upstream requirement IDs retain their upstream repository namespace; citing a
theorem or ticket does not import its coverage into this repository.
