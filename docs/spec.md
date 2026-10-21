# Repository and planning requirements

These requirements cover the current documentation and workflow. The structural
contract was adopted by issue #2 and merged PR #22. Build, comparison and structural
IR tasks #5–#7 were accepted through PRs #23–#25; target #8, text #9 and structural
backend #10 through PRs #26–#28. The maintainer accepted #11's finite
representation, soundness and bounded completeness proofs through PR #33.
Selected #13 adds inherited structural realization with semantic review pending.
The authored static parser #16 is accepted through PR #30. Accepted #17 (PR #35) adds
checked declaration resolution/defaults. Selected #18 adds source constraint
elaboration with semantic review pending; source CLI integration remains separate.
Accepted #14 (PR #32) adds typed static expressions and their
independent semantic interpretation. Selected #15 extends bounded target
arithmetic and proves source range-analysis soundness; source constraint encoding
and its preservation remain unfinished.
Future compiler behavior is reserved below, not declared implemented or proved.

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent explain the selected structural Clafer-to-Alloy direction,
its relationship to Clafer Semantics and the Haskell comparison compiler, and the
build bootstrap, admitted structural IR, independent target core, structural
backend, checked serialization, authored static parser, typed expression API,
checked source declaration resolution/defaults and accepted M1 preservation
proofs under explicit finite scope and numeric-range assumptions. The selected
inherited structural extension has implementation and proofs pending semantic
acceptance. Source constraint preservation and grammar-to-parser correspondence
remain unproved.
Distinguish reviewed decisions, contract candidates and future implementation/proof
promises. Contract adoption precedes dependent
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

Before implementation, check repository code, pinned upstream sources, standard
libraries and relevant maintained libraries/tools for reusable solutions. Prefer
reuse when it meets the contract. Record candidates and concrete gaps or tradeoffs
before writing custom infrastructure, including proof/runtime boundaries and
dependency/license costs. Independence alone is not a reason to rebuild machinery.

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

## Hygienic deterministic Alloy text

`req~compiler-alloy-text~1`

Render every selected target constructor using legal identity-based names,
explicit precedence/grouping, multiplicities, declaration ownership, command
polarity and complete exact/upper scopes. Retain original source names and byte
spans in deterministic declaration maps, never executable syntax. Handle repeated,
shadowed, reserved, Unicode and internal names without capture or aliasing.

Prove name injectivity and print/parse reconstruction against an independent
parser for the emitted subset, or obtain explicit review for an alternative
assurance boundary. The [candidate boundary](alloy-text.md#proved-boundary-and-review-obligation)
proves reconstruction for successful rendering by translation validation;
unconditional successful renderability is not claimed and remains a review
consideration. Preserve whole target identity, reject malformed metadata and
failed correspondence, and keep native execution and actual Alloy parsing/solving
outside the kernel claim. Compare real pinned Analyzer ASTs and exact-candidate
meaning, including grouping/name mutations. Extend all constructor checks with M2.

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
and malformed tables. Keep these representation results distinct from the global
source-soundness, bounded-completeness and compiled-bank composition obligations
of #11, specified in the [correctness contract](structural-correctness.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Structural soundness and bounded completeness

`req~compiler-structural-correctness~1`

For the exact admitted M1 effective domain and a successful compilation, prove
that every independently satisfying target instance decodes to a concretely
represented source configuration satisfying every upstream structural clause.
Derive root, carrier coverage, typed endpoints, inheritance, abstract cover,
declaration disjointness, ownership, references, keys, local bounds and group
unions from the emitted target declarations and facts. Do not assume source truth,
successful decoding or a supplied preservation equivalence.

Conversely, construct a target representation of every finite source configuration
satisfying that independent meaning and fitting the manual scopes and signed
integer observation ranges. State scope counts and numeric definedness separately
from source and target satisfaction. Preserve every source object and reference
occurrence, including repeated bag targets. Compose with the pinned local-bank,
constraint-free erasure and arbitrary-link normalization results while retaining
their actual global hypotheses. Keep native and serialized execution outside the
kernel theorem boundary; bounded absence does not establish unrestricted UNSAT.

Kernel-check nontrivial actual compilation witnesses and mutations distinguishing
omitted upper bounds, collapsed bag heads and missing global abstract cover.
Keep semantic acceptance and dependent task intake separate from automated checks.
The [correctness contract](structural-correctness.md) records exact APIs and assumptions.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Selected inherited structural realization

`req~compiler-inherited-realization~1`

Admit the selected inherited structural domain through a separate explicit API,
retaining authored abstractness and original declaration/occurrence identity.
Check the actual upstream selection, core and primitive-origin restrictions.
Distinguish ordinary fields made effectively abstract by containment from explicit
abstract families. Compile original inherited inventories, cover/disjointness,
ownership and union-based realized groups without creating contextual copies.

Prove soundness and finite bounded completeness against the pinned independent
`Realization.Satisfies`, with numeric scopes/count definedness and finite primitive
observation limits explicit. Preserve the original M1 domain and prove compatibility
of meanings on the overlap. Prove contextual object/link restriction, discharging
live-carrier premises for decoded satisfying targets. Supply actual compilation
witnesses, the complete Appendix 6 structural skeleton and negative ownership,
inherited-group and abstract-cover mutations. Keep scalar primitive interpretation,
constraint bodies and native/serialized correspondence outside these model proofs.
The [inherited contract](inherited-realization.md) records the exact API and limits.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Strict external instance decoding

`req~compiler-instance-decode~1`

Decode actual native-generated Alloy instances into the shared source candidate
protocol, preserving declaration identity, all objects, containment endpoints
and distinct reference heads even when owner/target pairs coincide. Reject
unknown/missing tables, duplicate identities/tuples, invalid arities/endpoints
and malformed roots. Keep well-formed semantic violations distinct from malformed
input. Prove exact row correspondence for the executable export from the existing
structural observation; identify JSON/Analyzer parsing and native execution as
unproved external boundaries. See the [comparison contract](comparison.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Exact three-way candidate comparison

`req~compiler-differential~1`

Within the common admitted capture domain, compare the identical candidate with
the upstream verified checker, same-generation Haskell Alloy and actual native
Lean compilation/serialization/Alloy. Retain equivalent explicit source scopes,
bitwidth and solver options, documenting the virtual versus explicit root layout.
Require exact decoded-candidate isomorphism for SAT, preserve negative candidates
and both discrepancy directions, and never treat raw text equality as the oracle.

Exercise complete tiny enumerations and reproducible seeded generation without
satisfaction filtering. Retain sources, IR, raw candidate/output, maps, tool/source
identities, commands, options, seeds and replay evidence outside source. Verify
replay identities; minimize completed discrepancies with retained attempts and
honest deletion-minimality bounds. Detect injected occurrence collapse, omitted
cardinality/group/disjointness enforcement and swapped endpoints. Keep malformed,
unsupported, timeout/resource and tool failure outcomes separate from completed
agreement. Finite comparisons do not replace the independent backend preservation proofs.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Authored static source parsing

`req~compiler-parser~1`

Parse the adopted static surface whitelist into authored syntax independently of
name resolution, defaulting, typing and generation. Implement layout and explicit
braces, declarations/use shorthand, direct references and inheritance, keyword and
numeric groups/cardinalities, and every selected hard-constraint expression with
the pinned precedence/associativity. Preserve original source, spelling, UTF-8
spans, omitted versus authored values, group keyword provenance, set/bag arrows,
binders and constraint attachment occurrences. Match the pinned Latin-1 lexer
character class without normalization or silently narrowing it to ASCII.

Reject malformed layout/intervals and recognize excluded primitives, operators,
initializers, escapes, directives and all temporal forms without erasing them.
Describe the grammar independently in the [parser contract](parser.md). Exercise
native examples, malformed mutations, finite generated properties and live pinned
Haskell syntax comparisons, retaining differences and tool failures separately.
Reuse the pinned Lean parser primitives and existing oracle tooling. Keep the
unproved grammar/parser/native boundary explicit; successful parsing does not
establish resolution, type correctness, admission or satisfaction.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Source declaration resolution

`req~compiler-resolution~1`

Resolve the accepted authored declaration tree deterministically into finite
identity-based structural tables. Preserve every declaration, its source path and
span, repeated names in distinct contexts, parent/super/reference edges, set/bag
head identity, original constraints and their owner occurrences. Resolve forward
and cyclic references without following target edges recursively. Require unique
nearest lexical lookup or unique global lookup, with explicit parentless abstract
types for supers. Reject missing/ambiguous names, duplicate siblings, reserved
user names, inheritance cycles and excluded inheritance forms with stable source
diagnostics. Integer aliases refer to one explicitly classified canonical primitive.

Define independent source coverage, lookup and elaboration rules and kernel-prove
that successful elaboration satisfies them and yields the upstream well-formed
structural core and selected realization domain. Well-formed output alone is
insufficient. Retain ordinary inherited fields and explicit abstract families;
keep constraints available for #18. The explicit M1 conversion must reject richer
features and constraints, and pass the existing exact M1 admission. Compare
resolved fields with the pinned importer on its common domain, retaining expected
identity/provenance differences. See the [resolution contract](resolution.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Authored and effective defaults

`req~compiler-defaults~1`

Retain omitted versus authored multiplicity, group keyword versus numeric
provenance, explicit abstractness and effective inherited abstractness. An omitted
group inherits the superclass's complete effective group, otherwise unrestricted.
An omitted parented local bound is optional under a keyword group and one under
a numeric group; authored bounds override it. Effective abstractness is the
explicit flag or the parent's effective flag. Kernel-prove agreement with pinned
`Clafer.Defaults`; keep the documented numeric-group and `opt` differences from
Haskell. Do not fabricate parent fibers for parentless abstracts. An explicit
M1 projection may normalize that unused local slot to unrestricted while retaining
authored metadata; it must preserve every other declaration field.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Source frontend diagnostics

`req~compiler-diagnostics~1`

Return a deterministic version-1 source diagnostic with stable code, phase,
malformed/unsupported category, message, logical filename, primary zero-based
half-open UTF-8 byte span, one-based line/scalar column and related locations.
Retain original CRLF/Unicode byte offsets and use zero-width EOF locations.
Fail without a partial successful document. Distinguish recognized excluded
features from missing/malformed syntax. The resolver supplies name/default
diagnostics. Selected #18 adds typed-expression diagnostics with phase `type`;
its source constraint contract specifies the accepted inference rules. Exact
English wording is not stable. The parser returns the first
lexical error, otherwise the first grammatical error. Diagnostic serialization,
IR-only locations and process exit integration remain #19/#20 obligations. The
resolver prioritizes declaration/name checks, edge resolution, inheritance and
realization ranks, then independent source correspondence validation.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Executable typed static expressions

`req~compiler-expressions~1`

Provide executable finite support and annotated syntax for every adopted M2 typed
core constructor, with checked sorts, lexical positions, fresh nested binders,
explicit identity/inclusion widening and original byte spans. Preserve `this`,
global extents, repeated map occurrences and operand order. Reject malformed
annotations and direct observations of the complete primitive integer extent.
Return the original tree with checked typing and observation evidence.

Interpret successful typed trees into the pinned independent typed core, using
its existing partial denotation. Prove exact admission, footprint preservation
and admissible environment interpretation. Undefined remains distinct from false;
reference-head and target-set counts remain distinct. Permit map-free literals
through direct denotation without changing upstream Compile support. This API
neither extends M1 admission nor implements a parser, general finite evaluator,
Alloy constraint encoding or production CLI. See the [expression contract](expressions.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Static arithmetic and finite observation

`req~compiler-arithmetic~1`

Retain mathematical Int meaning with explicit width, finite observation budgets,
value intervals and separate definedness obligations. Conservatively check every
literal, integer extraction and arithmetic intermediate, including all Boolean
branches and binder bodies, for signed representability at widths 1–16. Reject
unsafe profiles as unsupported, without wrapping or asserting UNSAT. Check
candidate observations and external environments against their recorded budgets
and intervals independently of constraint truth.

Prove exact finite singleton extraction, interval transfer/representability,
and construction of full-integer bindings retaining nonprimitive objects and
original links under explicit independent model obligations. Prove admitted
expression denotation invariant across such extensions and finite meaning for
admitted collections, including integer navigation and quantifier domains.
Keep primitive/root structural composition explicit; do not claim whole-domain
finite equivalence. Prove the executable range analyzer sound against that
independent denotation: every defined number lies in its returned representable
interval and every collection's distinct cardinality meets its returned budget.
Derive finite recorded membership through navigation, widening and lexical binding
from checked observations. Include every numeric intermediate and actual quantified
body, without assuming final constraint truth or successful singleton extraction.
Compose the finite-observation bridge for arbitrary full-integer extensions and
show scalar compatibility with target bounded-integer admission. Source-to-target
expression/attachment preservation and structural pipeline composition remain
obligations of #15/#20. See [source range proofs](expression-encoding.md#source-range-analysis-proofs).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Source constraint elaboration

`req~compiler-constraint-elaboration~1`

Elaborate the accepted static source expressions over checked declaration tables.
Resolve lexical positions, this, parent, contextual/inherited fields, global
extents and explicit/implicit dereferencing with deterministic missing/ambiguous
name and type diagnostics. Preserve original declaration/map identities, attachment
owner, body position and UTF-8 spans. Use actual inclusion paths for common-type
widening; keep reference-head counts distinct from dereferenced target counts.

Expand exactly the adopted connectives, comparisons, presence/cardinality tests,
finite single-object quantifiers and integer operations. Quantifier domains use
the outer environment; fresh identities permit shadowing without capture.
Successful output carries an independently defined declarative elaboration
relation, checked typing and finite-observation admission. Interpret its typed
syntax through the pinned partial denotation, retaining undefined as distinct
from false. Type checking must not assert singleton extraction, numeric bounds,
source satisfaction, or backend preservation. Literal-only bodies need no maps.

Enumerate every original body and prove source occurrence/order preservation;
retain empty bracket groups in the source document without inventing bodies.
Compare all Appendix 6 c01–c12 elaborations with the existing pinned manual
inventory, including parent/server paths, repeated names and display-head counts.
Exercise negative variants, ambiguity, invalid joins and generated nested scopes.
Keep native/parser tests distinct from kernel proofs and semantic acceptance.
See the [source constraint contract](constraints.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Bounded target arithmetic

`req~compiler-target-arithmetic~1`

Extend the independent Alloy target with ordered integer addition and subtraction
over literals, finite distinct-tuple cardinalities and nested integer expressions.
Use mathematical intermediate values with explicit signed representability at
widths 1–16; propagate undefined operands and overflow rather than wrapping or
converting them to false. Conservatively admit every intermediate using explicit
scope-derived count inventories, including branches under negation, implication
and quantifiers. Reject malformed integer stack programs and invalid relation
operands through target admission.

Prove constructor definedness/value equations and checked-interval agreement with
mathematical arithmetic under explicit leaf count-capacity premises. Those
premises must state actual tuple bounds, never final truth or preservation.
Retain the remaining general relation-inventory and source-denotation obligations.
Extend checked serialization and independent parsing for all integer constructors;
exercise the actual pinned Analyzer with independent ASTs, boundary cases and
operand, grouping and lexical-binding mutations. This target layer does not
claim source expression or attachment preservation. See [encoding work](expression-encoding.md).

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
| `compiler-expression-encoding` | [#15](https://github.com/kbak/clafer-compiler-lean/issues/15) | Static constraint preservation |
| `compiler-cli` | [#19](https://github.com/kbak/clafer-compiler-lean/issues/19) | Native resolved-IR CLI and output protocol |
| `compiler-pipeline-correctness`, `compiler-telematics` | [#20](https://github.com/kbak/clafer-compiler-lean/issues/20) | Source pipeline, composed assurance and complete example |
| `compiler-qualification`, `compiler-performance` | [#21](https://github.com/kbak/clafer-compiler-lean/issues/21) | Private acceptance evidence and reproducible measurements |

The active [oracle contract and artifacts](oracles.md) cover #6; the
[IR contract and artifacts](ir.md) cover #7 above.
The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) owns scheduling.
Upstream requirement IDs retain their upstream repository namespace; citing a
theorem or ticket does not import its coverage into this repository.
