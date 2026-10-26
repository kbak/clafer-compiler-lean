# Compiler and repository requirements

These requirements cover the compiler, its assurance boundaries and the repository
workflow. The [architecture](architecture.md) defines the selected structural
fragment. Component contracts in the [documentation map](intent.md#documentation-map)
record exact delivered APIs, proof assumptions and testing limits; the
[roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) retains task dependencies
and acceptance history.

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent explain the selected structural Clafer-to-Alloy language,
its relationship to Clafer Semantics and the Haskell comparison compiler, and
its supported interfaces. Describe the implemented frontend, structural and
expression encodings, checked serialization and preservation proofs with their
explicit scope, numeric-range and representation assumptions. The
[constraint-preservation review](https://github.com/kbak/clafer-compiler-lean/pull/41)
records the finite-observation conditions; the
[source-pipeline review](https://github.com/kbak/clafer-compiler-lean/pull/44)
records their composition into full source-model assurance. The current theorem
contracts are in [constraint encoding](expression-encoding.md) and
[source pipeline assurance](pipeline.md#composed-assurance).
Grammar-to-parser correspondence and native/serialized execution remain tested,
unproved boundaries. Distinguish delivered guarantees from future work. Contract
adoption precedes dependent manual intake; planning tickets do not start
implementation. Publish the compiler source under MIT and provide public issue
and pull-request workflows that do not require access to the maintainer Project.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Contribution and validation workflow

`req~intentbond-workflow~1`

Pin IntentBond to an immutable source revision. Keep intent, requirements and
artifact links together, and run the repository check through IntentBond before
handoff. Retain evidence outside source. Exit 4 means automation passed with
semantic review pending, never approval. The full local check remains mandatory.
On pull requests and pushes to `main`, hosted CI builds every Lean module, audits
axioms, replays the kernel, checks scope identity and tests the native source/IR
CLI. Manual dispatch runs the full IntentBond check, including external comparison
tools and all regressions. Both retain evidence; routine CI does not establish
full qualification or semantic acceptance. Public CI artifacts retain logs,
notices, source identities and replay inputs without compiled test binaries.
Scope changes require explicit review.
CI checks scope identity against the baseline, permitting only exact reviewed
migrations without replacing the Git comparison baseline.

Before implementation, check repository code, pinned upstream sources, standard
libraries and relevant maintained libraries/tools for reusable solutions. Prefer
reuse when it meets the contract. Record candidates and concrete gaps or tradeoffs
before writing custom infrastructure, including proof/runtime boundaries and
dependency/license costs. Independence alone is not a reason to rebuild machinery.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Issue tracking and manual intake

`req~github-tracking~1`

Use public repository issues for contribution and acceptance records. Maintainers
track Todo, In Progress and Done in the Project; contributors do not need Project
access. Tasks describe scope, acceptance criteria, sources/requirements and dependencies.
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

Document one-way compiler-to-semantics ownership and module handoffs.
Keep independently defined source/target satisfaction, concrete encode/decode
relations, soundness, bounded completeness, frontend elaboration and serialized
text/runtime trust boundaries explicit. Bounds/representation assumptions must
not assume the preservation conclusion. Pin semantic and Haskell
baselines, retain source locators/licenses and define reviewed upgrades. No
research tag is required. Reserve future behavioral requirement IDs without
inventing implementation/proof coverage; acceptance review precedes dependent
manual intake. The build enforces module ownership/import boundaries and exercises
independent upstream imports. Keep required theorem shapes distinct from actual
proved declarations and their explicit assumptions.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible build and assurance bootstrap

`req~compiler-build~1`

Pin the Lean toolchain and Clafer Lake dependency to the source register and retain
the upstream-compatible transitive manifest. Build every owned compiler and Lean
test module, including modules unreachable from the root import. Build and run
the native executable, including its version and argument rejection protocol.
Exercise the source and resolved-IR commands specified below.
Retain the pure version and empty-argument response equations; those equations
prove neither IO nor compiler correctness.

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
notices externally and preserve applicable licenses when packaging tools.

Missing tools, modified inputs/tools, unsupported domains, timeouts, resource
limits, malformed input and errors must remain distinct from agreement or bounded
UNSAT. Required checks fail rather than skip. Retain exact candidates, both
outputs, options and replay instructions outside source. Discrepancies require
minimized evidence, independent expected semantics and an issue before semantic
changes. Haskell is supplementary evidence. This base oracle establishes neither
compiler correctness nor a new proof; the [three-way comparison](comparison.md)
adds downstream compiler Alloy to the comparison.

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
already decoded data; the [native driver](cli.md) supplies strict file/JSON
parsing and diagnostic serialization.
Reject unknown profiles and primitives; no static expression or inherited semantics
are admitted by extension placeholders. Retain tested raw resolution/native behavior
separately from the proved typed-core boundary and serialized execution.

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
Document auxiliary/unused atom policy and the source invariants the
[structural encoder](structural-encoding.md) must generate.

Maintain the construct correspondence and retained source identity against the
official reference. Kernel-check constructor laws and independent truth tables,
and compare representative equivalent formulas through the pinned real Analyzer.
Keep formal target properties distinct from tested Analyzer correspondence and
serialization/source preservation proofs. See the [target contract](alloy-core.md).

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

Preserve valid scopes excluding every model as unsatisfiable constraints; source
compilation may express conflicting declaration multiplicity as a fact.
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
specified in the [correctness contract](structural-correctness.md).

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
keep constraints available for [expression elaboration](constraints.md). The
explicit M1 conversion must reject richer features and constraints, and pass the existing exact M1 admission. Compare
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
`Clafer.Defaults`; retain the documented numeric-group difference from Haskell
and check agreement on keyword defaults, including `opt`, against Haskell 0.5.4.
Do not fabricate parent fibers for parentless abstracts. An explicit M1 projection
may normalize that unused local slot to unrestricted while retaining authored metadata; it must preserve every other declaration field.

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
diagnostics. The constraint elaborator supplies typed-expression diagnostics with
phase `type`; its source constraint contract specifies the accepted inference rules. Exact
English wording is not stable. The parser returns the first lexical error,
otherwise the first grammatical error.
The [native driver](cli.md) serializes source diagnostics and supplies IR-only
locations and process exits for both commands. No source coordinates are invented
for developer IR. The resolver prioritizes declaration/name checks, edge resolution, inheritance and
realization ranks, then independent source correspondence validation.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Native resolved-IR command

`req~compiler-cli~1`

Provide the standalone `compile-ir INPUT --bounds BOUNDS --output OUTPUT` command
for the exact guarded `clafer-ir/1` M1 profile. Decode strict UTF-8/JSON without
losing duplicate keys, numeric token forms, unknown semantic fields or identities;
compose existing admission, structural compilation and checked serialization.
Require complete declaration-ID scopes, a distinct-object budget and explicit
bitwidth, with documented overrides. Report the compiler version and exact
semantic/reference pins; source-text compilation remains explicitly unsupported.

Document deterministic input/output, diagnostics and exit behavior. Read stdin or
files and emit complete Alloy to stdout or replace a file only after successful
rendering. Malformed inputs exit 2, unsupported features/ranges exit 3, operational
failures exit 1, compilation exit 0. Preserve existing file output on failure before
rename. Never infer SAT/UNSAT or invoke a solver implicitly. Retain declaration
identity and generated source maps in the pure API for dependent integration.

Run the native binary with only its documented runtime libraries visible, without
a Lean development toolchain, Haskell, Java or Alloy. Exercise real Analyzer loading
and solving as external validation. Keep tested JSON/CLI/native behavior distinct
from existing in-memory proofs. The
[CLI contract](cli.md) supplies examples, platform limits and review boundaries.

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
expression/attachment preservation is specified below; structural source pipeline
composition is specified by the
[pipeline requirement](#integrated-source-pipeline-and-composed-correctness).
See [source range proofs](expression-encoding.md#source-range-analysis-proofs).

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

## Static constraint encoding and preservation

`req~compiler-expression-encoding~1`

Translate every admitted typed static expression constructor into the independent
Alloy target. Preserve lexical positions, owner `this`, original map roles,
ordered operands, explicit identity/inclusion widening and finite primitive
observations. Generate separate definedness and value/truth; undefined extraction
must remain distinguishable from false under negation and quantification.
Conservatively reject all unsafe numeric intermediates, including vacuous bodies.

Represent observed integer objects with typed, total scalar fields and emit
interval and injectivity facts. Prove the corresponding enforcement from target
field admission and the generated facts. For checked observations within explicit
budgets/intervals and concrete object/map/scalar representation equations, prove
constructor definedness, value and truth correspondence to the independent pinned
source denotation. Derive numeric representability from source admission; do not
assume successful source extraction, final constraint truth or desired equality.
Retain the finite-observation bridge to arbitrary full mathematical integer extensions.

Compile every attached body in order, retaining original identity, owner and span,
including repeats and inherited owners. Prove exact occurrence preservation and
all-body satisfaction equivalence under the stated representation conditions;
derive source truth from satisfaction of the generated module. Keep full structural
source-pipeline composition and source CLI integration in the
[pipeline requirement](#integrated-source-pipeline-and-composed-correctness).

Extend checked serialization/reconstruction for the emitted scalar and identity
forms. Run native and actual pinned Analyzer checks covering all constructors,
empty/nonempty domains, scalar range/identity, inherited contexts, lexical capture,
ordered operands, parent/dereference confusion, undefinedness and overflow. Keep
these tests distinct from kernel proofs and semantic acceptance.
See the [encoding contract](expression-encoding.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Integrated source pipeline and composed correctness

`req~compiler-pipeline-correctness~1`

Compose the accepted parser, resolution/defaults, constraint elaboration, inherited
backend, expression translation and checked serializer in a native source command.
Retain original IDs, owner/body occurrences, spans and diagnostics; keep M1 IR
compilation available. Require explicit closed version-2 bounds, nonprimitive
object budgets, original declaration scopes, signed width and primitive intervals.
The standalone runtime must not require Lean tooling, Haskell or a solver.

Derive target-to-source representation and satisfaction from the actual successful
compilation and target instance. Construct one rooted selected source model with
all mathematical integers and every original constraint on its full owner domain.
Preserve primitive parent queries, reference occurrences, inherited groups,
undefinedness and all admitted source expression denotations. For full source
models with the concrete finite observation relation and data-only Fits, construct
the target and prove bounded completeness. Fits must not assume target truth,
finite source satisfaction or preservation. State the canonical carrier and
parser/native/text/solver boundaries explicitly; do not present candidate-level
conditional equivalence as composed soundness or completeness.

The implicit primitive uses unrestricted multiplicity and is also inserted for
constraint-bearing source without integer references. This supplies the full
carrier required by the pinned semantics; authored IDs remain stable. The
[full integer carrier](pipeline.md#full-integer-carrier) explains
why both conditions are necessary. Upstream meanings and public M1 guards remain
unchanged.
See the [pipeline proof and reuse inventory](pipeline.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, proof, utest

## Complete telematics integration

`req~compiler-telematics~1`

Compile the complete supported Appendix 6 source, including all twelve constraints
and final selections, with explicit bounds. Exercise distinct observed integer
values and exact candidate comparison against the pinned Analyzer. Justify the
extended inherited/source observation evaluator separately from the guarded M1
checker. Detect wrong version order, display count, parent navigation, omitted
constraint and missing inherited-group mutations; retain bounded minimized replay
witnesses and state their reduction order. Preserve complete source/candidate,
original maps, scalar rows, commands, tool/source identities and external outcomes.
These finite tests complement the composed proofs, not certify the external tools.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

<a id="private-candidate-qualification"></a>

## Candidate qualification

`req~compiler-qualification~1`

Prepare a local candidate with a closed accounting of the adopted feature
matrix: implementation, promised proofs, positive/negative tests and explicit
rejection of excluded forms. Preserve all existing scope and assurance boundaries;
material defects prevent acceptance. Retain the exact clean candidate commit,
source-matched passing IntentBond evidence, complete test/kernel logs, independent
review disposition, immutable tool identities, license attribution and replayable
discrepancies. Bind clean-built standalone artifacts and their isolated runtime
smoke results to that candidate. Reject stale or modified evidence and mismatched
measurements. A pending review remains pending in the package manifest.

Document reproducible usage, supported platforms, trust boundaries and the existing
dependency-upgrade policy. Preserve the upstream SoSyM snapshot independently;
neither a semantics branch nor a research tag gates compiler qualification.
See [qualification](qualification.md).

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

## Reproducible compiler measurements

`req~compiler-performance~1`

Measure parsing, declaration/default resolution, constraint elaboration, backend
encoding, checked rendering, process memory and output size independently of Alloy
solving. Retain raw samples, warmup policy, commands, inputs, explicit bounds,
machine/tool identities and failure outcomes. Use tiny, representative and larger
generated inputs plus the complete supported telematics source. Compare the pinned
Haskell compiler on identical common-domain input bytes and equivalent explicit
scopes/bitwidth/options, accounting for its virtual root and different pipelines.
Force lazy output before stopping whole-process measurement. Do not compare
instrumented stage times as equivalent work or claim blanket Haskell compatibility.

Measure clean-project and warm Lean build/proof elaboration separately from native
compiler runtime and kernel replay; state reused dependency/cache boundaries.
Check the measurement probe against production output. Preserve timeouts/errors as
failures, never silently omit required cases. No speedup threshold or optimization
is promised; any subsequent optimization needs profiling and semantic preservation.

Covers:
- `intent~compiler-foundation~1`

Needs: impl, utest

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
and requirement reservation policy below implement the documentation obligation.
No Lean declaration or compiler theorem is claimed by these Markdown artifacts.

Covers:
- `req~compiler-boundaries~1`

## Reserved implementation requirements

`compiler-qualification` and `compiler-performance` are active requirements above.
There are no remaining reserved implementation IDs in the selected roadmap. New
scope needs its own reviewed requirements and manual intake; this does not imply acceptance
of the qualification candidate.

The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) owns scheduling.
Upstream requirement IDs retain their upstream repository namespace; citing a
theorem or ticket does not import its coverage into this repository.
