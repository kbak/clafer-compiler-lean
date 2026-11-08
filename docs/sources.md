# Source register and dependency policy

Use both Clafer Semantics and the Haskell Clafer compiler to guide this project.
They have different roles: independent source meanings and reusable proofs upstream;
syntax, examples and compatibility evidence in Haskell. Haskell behavior does not
automatically overrule the published language or an accepted semantic correction.
The [architecture contract](architecture.md) specifies the selected common fragment
and deliberate differences. The build bootstrap adapts upstream validation helpers
under their MIT license;
see the attribution and exact paths in [the build contract](build.md). Semantic
definitions and Haskell source/fixtures are not copied. The [IR bridge](ir.md)
uses S1 directly: its executable guards are proved equivalent to the pinned
`coreChecks`/`supportChecks`, not a second semantic authority. S5
`ReferenceEmpty`, `ReferenceSet`, `ReferenceBag`, `SuperSome`, `Card*` and `GCard*`
were inspected for the representation boundary: M1 imports resolved effective
values and direct IDs, without reconstructing Haskell defaulting or accepting
arbitrary target expressions. The new runtime/table/fixture code is original;
no Haskell code or fixtures are redistributed.

## Immutable baselines

| Source | Revision/profile | Role and license |
| --- | --- | --- |
| [Clafer Semantics](https://github.com/kbak/clafer-semantics/tree/f00e5dacb07eed51026f69fcf699683210d394d3) | `f00e5dacb07eed51026f69fcf699683210d394d3` | Installed Lake dependency; [MIT, Kacper Bak](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/LICENSE). The manifest retains this commit and its inherited dependencies. |
| [Haskell Clafer](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea) | `6750e6f591b2131549122c13dee94d3d2257eaea` | Comparison/compiler/grammar baseline; [MIT, GSD Lab and ISD Lab](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/LICENSE). External tool, not production runtime dependency. |
| Lean and Mathlib | Upstream [toolchain](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/lean-toolchain): `leanprover/lean4:v4.35.0`; [Mathlib revision](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/lakefile.toml): `56a005855ea17e0b0958f73ec801ae140b0a1679` | Selected toolchain and inherited Mathlib pin for the [build](build.md) |
| Alloy | 6.2.0, source `794226dd07b536fe35c5ca44b529417183cd629b`, Java 17+, SAT4J | Initial external validation profile; upstream [runtime/hash/options](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/scripts/verification/alloy_runtime.py) and [bridge](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/scripts/verification/AlloyBridge.java) |
| IntentBond | `f9b4f9e40722dc6a83067ac9e62480159322dd09` | [Requirements pin](../requirements/intentbond.txt), including native Lean comment annotations |

The [oracle tooling](oracles.md) checks the Alloy distribution SHA-256
`6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d`.
Retain actual JAR/tool hashes, Java vendor/build, solver and all effective options,
scopes, bitwidth, source/IR/output/candidate identities and exact replay commands
outside source. The version label alone does not reproduce a comparison.
Before copying code or fixtures, inspect the pinned file's notices and retain
required attribution. The [oracle inventory](oracles.md#inspected-licenses-and-distribution-contents)
records inspected source/distribution notices; [qualification](qualification.md)
records the packaged runtime dependency inventory and remaining distribution gates.
A source citation is not a redistribution license.

## Current comparison dependency

The behavioral planning sources are registered [separately below](#behavioral-sources).
The installed semantics pin supplies both the static and behavioral libraries.
The Haskell 0.5.4 and Alloy static comparison identities remain unchanged; see
[the dependency delta](#behavioral-dependency-delta).

The pinned Haskell reference is 0.5.4. Its apostrophe UID escaping and `opt`
default fix are adopted through the upstream capture adapter, whose strict
position/option schemas remain outside the proof boundary. The single-file
capture API emits spans without filenames; raw CLI exports are not substituted
for paired receipts. Upstream's
[compatibility assessment](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/resolved-ir-comparison.md#compiler-054-compatibility)
records the exact changes and immutable source evidence.

This compiler's `Defaults` makes `opt` children optional; its oracle regression
requires agreement at `0..1`. Numeric groups follow the explicitly adopted
upstream child-default policy described below.
Haskell rejects unreachable concrete groups, while the independent source meaning
can admit an empty context; this remains a difference in the accepted source domain.
The inspected grammar, lexer and parser boundary hashes are recorded in
[parser sources](parser.md#sources-and-comparison).
Historical evidence remains tied to its original adapters and source identities.

## Adopted child-default policy

The selected [upstream policy](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/sources.md#current-child-default-policy)
makes unannotated children optional (`0..1`) under all keyword groups and numeric
groups except exactly `0..*`. Numeric `0..*` and absent unrestricted groups give
`1..1`; explicit child bounds override defaults, and inherited group provenance
is preserved. The concrete implementation evidence is
[`ResolverInheritance.analyzeCard`, lines 221–230](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/ResolverInheritance.hs#L221-L230).
This selected agreement does not adopt Haskell's other abstractness, relocation,
empty-group or counting behavior.

This is an authorized language evolution from SoSyM Appendix 3/Figure 27
(PDF pp.31–32), not a paper erratum. The
[historical checkpoint](https://github.com/kbak/clafer-semantics/tree/sosym)
at `8a300bff11af2f458af70d56394f1899815455e9` preserves the paper-era numeric
`1..1` default with the accepted paper corrections. The coordinated decisions
are [upstream default evolution](https://github.com/kbak/clafer-semantics/issues/118)
and [compiler adoption](https://github.com/kbak/clafer-compiler-lean/issues/61).

## Resolved structural normalization

The [resolved normalizer](ir.md#resolved-structural-normalization) reuses the
existing source-to-M1 projection. At the installed semantics pin,
[`Configuration.Multiplicities` and `StructuralSatisfies`](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/Clafer/Semantics/Structural.lean)
justify leaving parentless abstract local slots unrestricted: local multiplicity
constrains only actual parent fibers. The compiler proves equivalence for the
same configuration, retaining independent upstream meaning and all identities.
The accepted c7 comparison's
[`Explicit.exClafer`](https://github.com/gsdlab/clafer/blob/c7a2fb7d0ba601f52efeac459d12f859a40580fe/src/Language/Clafer/Generator/Explicit.hs#L66-L77)
prints `0..*` for abstract cards. The Lean pass retains its existing narrower
parentless condition; it does not adopt that printer's full transformation.
Haskell explicit-output qualification remains separate finite evidence; this pass
does not print source text or adopt a new comparison profile. No semantic pin,
source fixture, license or dependency changes are required.

## Constraint name lookup policy

The [constraint frontend](constraints.md#api-and-lookup) adopts ancestor-before-target
precedence for bare names. SoSyM Appendix 4, Name resolution rules (legacy D.2,
e-offprint PDF pp.32–33), instead lists Descendants, Targets, then Ancestors.
This is a deliberate compiler-language choice, not a claim that the published
order is erroneous. The decision is tracked in
[compiler lookup alignment](https://github.com/kbak/clafer-compiler-lean/issues/67),
following the [source-policy discussion](https://github.com/kbak/clafer-semantics/issues/121).
The upstream `sosym` checkpoint remains frozen. Both that checkpoint and the
current upstream semantics consume resolved expressions and implement neither
textual name-resolution order; no semantics dependency update is needed here.

The pinned Haskell `6750e6f591b2131549122c13dee94d3d2257eaea`
[`ResolverName.resolveName`](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/ResolverName.hs)
tries `resolveDescendants`, `resolveAncestor`, `resolveTargetChild`, then
`resolveTopLevel`. `resolveImmName` handles qualified navigation separately.
The later [S9 discussion](https://github.com/gsdlab/clafer/blob/2d857da/doc/static-semantics-errata.md#s9-name-resolution-beyond-the-papers-rules-clarification)
is supplementary context, not a new runtime/compiler pin.

The adopted bare target fallback starts only from the original context's target
and retains inherited fields and finite reference chains. Targets of enclosing
scopes or descendant references do not start additional searches. The pinned
Haskell `Common.findHierarchy`/`getSuperAndReference` traverses reference chains;
a direct `r1 -> r2`, `r2 -> Target` lookup confirms two dereference steps before
`Target.leaf`. Qualified navigation retains its existing reference-chain behavior.
Immediate-field lookup, nearest inherited-field shadowing and unique global lookup remain this compiler's selected
policy; no complete correspondence with Haskell's broader descendant or ambiguity
rules is asserted. Reuse of `Field`, `HasField`, `Navigate` and `ScopePath` keeps
the change in the frontend and its independent source judgments. No backend or
upstream semantic definitions, new library, or third-party code are needed.

## Empty collection extension

The [upstream empty-set decision](https://github.com/kbak/clafer-semantics/issues/134)
and [compiler adoption](https://github.com/kbak/clafer-compiler-lean/issues/81)
add `noclafer` to the selected language. This extends SoSyM Appendix 4/Figure 28;
it is not a correction to a published constructor. The
[Alloy specification](https://alloytools.org/spec.html), Subtypes and Relational
Expressions, and [Edwards, Jackson and Torlak (2004), §4](https://groups.csail.mit.edu/sdg/pubs/2004/typeSystem.pdf)
motivate bottom element typing with fixed arity: Alloy unary `none` and binary
`none -> none`. Collection operations follow the existing set meanings.
The source spelling `noclafer` preserves existing user names such as `none`.
The generated Alloy retains its own reserved spelling. In both layers,
Clafer's partial integer extraction and strict definedness remain in force.
The compiler reuses upstream typed emptiness, existing target `Rel.empty`,
serialization and constructor preservation proofs. No third-party source or
new library is copied or introduced. The selected source inference boundary is
documented in [constraint elaboration](constraints.md#empty-collection-literal).

## Behavioral empty navigation and warnings

The scoped source amendment `literal-empty-navigation/1`, selected in
[the navigation and diagnostics task](https://github.com/kbak/clafer-compiler-lean/issues/85),
adopts literal-rooted name-chain erasure from
[`412f610981724bd6a53451189eb8cb98b466a6da`](https://github.com/gsdlab/clafer/commit/412f610981724bd6a53451189eb8cb98b466a6da).
Its `Intermediate/ResolverName.hs` (`resolveNav`, `fromNoClafer`) removes the
literal-rooted tail before lookup. `Intermediate/ResolverType.hs`
(`resolveTPExp'`, `redundantExps`), `Language/Clafer.hs` and
`test/Suite/TypeSystem.hs` change the four self-expression errors to positioned
warnings. The exact [frontend policy](behavioral-frontend.md#literal-empty-navigation-and-successful-warnings)
is narrower than arbitrary tail erasure; ordinary arithmetic, Boolean, temporal
and primitive-extent checks remain authoritative. Self-expression warnings are
syntactic, nonfatal reports, with no simplification or claim of definedness.
The CLI uses a separate successful warning protocol instead of Haskell statistics.

This is a compiler source-elaboration convention. Alloy still resolves names in
`none.unknown`; resolved `none.r` has empty relational meaning, while `A.none`
is an invalid unary/unary join. The compiler emits its existing unary empty or
strict cursor intersection instead of either unresolved Alloy syntax or an
invalid join. Division and remainder still exclude possible zero divisors during
range admission, including self-expressions. No upstream empty law, partial
operation, temporal meaning or static-policy rule changes.

The complete inspected `ResolverName.hs` and `ResolverType.hs` files are
byte-identical at the qualified comparison revision
`c7a2fb7d0ba601f52efeac459d12f859a40580fe`. The source comparison regressions use
that pinned exporter and Alloy 6.2.0; the task retains the exact file comparison
and direct Alloy probes as external evidence. Native/parser/warning behavior
and bounded solver results remain tests. Source derivations and interpretation
reuse existing kernel-checked terms and proofs. Independent candidate review is
still required. The primary `behavioral-0.5.7-candidate/v1` reference remains
`af858ec0fe3ce2ceacb7fd120947c058233086d6` with D1–D5; this amendment does not
adopt the intervening release or replace any historical Haskell/oracle pin.

## Published source and locators

Primary language reference: Bąk et al., *Clafer: unifying class and feature
modeling*, Software & Systems Modeling 15, 811–845 (2016), online 2014,
[DOI 10.1007/s10270-014-0441-1](https://doi.org/10.1007/s10270-014-0441-1).
The upstream [source map](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/sources.md)
records the inspected 37-page publisher e-offprint, SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`.
Its one-based PDF positions include two cover sheets. The paper is not
redistributed here. The source register follows upstream's recorded paper
locators and checked source declarations; it is not a new independent paper audit.

| Topic | Published locator / e-offprint PDF page |
| --- | --- |
| Structural declarations, references, abstractness, inheritance | §5.2–5.5, Table 4, pp.14–17 |
| Shapes, MCS, structural Compile/gluing | §6.2.2–6.2.5, Figure 23, pp.21–23; Tables 5–8 on pp.22–23 and Appendix 5 p.34 |
| Identity-preserving spans and set/bag maps | Appendix 2, mappings pp.28–30; Table 3 p.13 |
| Source syntax and defaults | Appendix 3/Figure 27, pp.31–32 |
| Constraints, resolution, typing, denotation | Appendix 4/Figure 28, pp.32–34 |
| Complete telematics | Appendix 6, p.34 |

Legacy upstream aliases A–F correspond to published Appendices 1–6; dotted D.2,
D.3 and D.4 denote named Appendix 4 headings, not numbered published subsections.
The older 34-page author preprint has SHA-256
`56b1c18e74807fb7646c0e89cb2fc306f4178affb41fee52fcebde09b031b2fb`.
The upstream `52-S/v1` replay format retains that older identity; do not rewrite
it to the preferred citation and invalidate historical receipts.

## Source locators

All GitHub locators below use the immutable revisions above. S labels are local
source-register references, not imported requirement IDs.

| ID | Inspected source / declarations | Use and limit |
| --- | --- | --- |
| S1 | [EffectiveCore](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Semantics/EffectiveCore.lean): `WellFormed`, `Supported`; [Admission](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Verification/Admission.lean): `coreChecks`, `supportChecks`, `certificate_exists`; [comparison audit](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/resolved-ir-comparison.md) | Exact M1 domain. [Bridge](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Semantics/Bridge.lean) and [Representation](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Verification/Representation.lean) supply selected structural results; no Alloy or frontend theorem. |
| S2 | [Syntax](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Syntax.lean): `Defaults`, `GroupCard.childDefault`, `AST.WellFormed`; [Compile contract](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/compile.md) | Resolved/defaulted input, distinct IDs/names, role and attachment identity. Positive-map support is an additional Compile precondition, not a universal source-language restriction. |
| S3 | [Inherited realization](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/inherited-realization.md), [Realization core](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Semantics/Realization.lean): `Core.Selected`, `View`, `Satisfies` | Selected explicit abstracts, ordinary fields, realization ranks, original links and Appendix 6 d01–d26/c01–c12; does not expand M1's finite checker. |
| S4 | [Typed core](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Constraints/Typing.lean): every `Expr`, `Arithmetic`, `SetOp` constructor; [denotation](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/constraint-denotation.md), [preservation](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/constraint-preservation.md) | Independent partial meanings, finite cardinality operands and exact integer singleton extraction. Mathematical integer realization is not Alloy's bounded Int. |
| S5 | Haskell [grammar](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/clafer.cf), [desugarer](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/Desugarer.hs), [inheritance resolver](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/ResolverInheritance.hs) | Constructor/surface inventory and compatibility guide. The architecture's whitelist excludes behavior and wider static extensions. Defaults are selected from S2, with discrepancies retained. |
| S6 | Haskell [IR](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Intermediate/Intclafer.hs), [static Alloy generator](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Language/Clafer/Generator/Alloy.hs), [positive fixtures](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea/test/positive), [regressions](https://github.com/gsdlab/clafer/tree/6750e6f591b2131549122c13dee94d3d2257eaea/test/regression) | Comparison evidence for the [oracle tooling](oracles.md) and [candidate comparisons](comparison.md). Same-generation JSON/Alloy receipt required by the upstream [import contract](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/resolved-import.md); equal filenames/hashes of source alone do not pair outputs. |
| S7 | [Official Alloy reference](https://alloytools.org/spec.html), especially Commands, Integer Expressions and signature/field semantics; [pinned A4Options](https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/A4Options.java) | Independent target guide. Finite scopes, signed bitwidth and overflow behavior must be modeled explicitly. The live reference is not immutable; the [target contract](alloy-core.md) records construct-by-construct correspondence and retained source identity against the pinned distribution. |
| S8 | [Bounded comparison](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/bounded-comparison.md), [complete telematics](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/telematics.md) | Exact-candidate/mutation policy and complete model inventory. Haskell Telematics fixtures differ from the printed model and cannot replace its twelve-body/final-selection inventory. |

## Discrepancies and reviewed upgrades

Keep accepted upstream corrections visible: link-preserving span composition;
common-target disjointness; parentless abstract heads without fabricated parents;
ordinary inherited fields versus explicit abstract types; and ordinary set
intersection. Preserve the documented empty-group and group-counting
mismatches with Haskell; current keyword and numeric child defaults agree with
the 0.5.4 reference on the tested common domain.
A discrepancy may be a compiler bug, a semantic defect,
a language-version difference or a harness error. Minimize it, retain both
outputs/options and the expected independent meaning, search existing issues,
and link a reviewed issue/PR before changing semantics. New reusable semantic
fixes belong upstream; Alloy-specific implementation remains downstream.

For any dependency upgrade, propose an immutable commit and explain API, meaning,
feature-guard, toolchain/Mathlib and license changes against the current pin.
Re-run admission fixtures and negative mutations, the complete applicable kernel/
axiom/native tests, paired Haskell/Alloy comparisons and source-matched IntentBond
checks. Review changed theorem assumptions and fixture expectations explicitly;
never bless an output merely because the reference changed. Keep previous receipts
and replayability. Update the source register, dependency manifest, requirements
and affected tests/links together in a reviewed PR. The build bootstrap supplies
those dependency files. Admission fixtures and
compiler/Haskell comparisons remain required for the delivered features.
The [target core correspondence](alloy-core.md#source-correspondence-and-external-boundary)
records the reference snapshot identity, exact constructor mapping and independent
Lean/Analyzer observations. Its fixtures and Java adapter are original MIT-licensed
project code; no reference specification text or Haskell code is redistributed.
The target core's general range analysis is tested, not claimed as a proved no-overflow theorem.

The current oracle check executes paired Haskell captures, upstream admission and
exact-candidate Lean/Alloy comparisons, alongside build/import/native/kernel/axiom
checks. The [three-way comparison](comparison.md) additionally checks
compiler-generated Alloy.

No branch name, floating latest release, SoSyM research tag or upstream maintenance
branch is a substitute for the commit pin or a prerequisite for compiler intake.
Dependency changes require manual intake and review.

The [Alloy text contract](alloy-text.md) maps the emitted grammar to S7's lexical,
namespace, precedence, declaration and command rules. It also uses S6's field
naming/ownership examples and S8's exact-candidate profile. Its grammar, printer,
native tests, reference text and AST adapter are original project code. The
retained reference snapshot identity is unchanged; no upstream definitions or
Haskell source were copied. Parser reconstruction is a successful-render theorem;
Analyzer correspondence and total successful renderability are not kernel proofs.
The [parser reuse assessment](alloy-text.md#parser-reuse-assessment) selects the
pinned Lean standard-library Parsec implementation for this candidate and inspects Haskell's
[grammar build rules](https://github.com/gsdlab/clafer/blob/6750e6f591b2131549122c13dee94d3d2257eaea/src/Makefile).
The Haskell main frontend uses BNFC/Happy and Alex; its Parsec dependency alone
does not identify the main parser's implementation. `Std.Internal.Parsec` is
imported from the pinned toolchain under its Apache-2.0 license; no library source
is copied and no package pin changes. Its opaque repetition helpers leave kernel
computation/termination distinct from the conditional reconstruction theorem.

The [structural encoding](structural-encoding.md) uses S1's
`Configuration.Typed`, `Rooted`, `Inherits`, `Abstracts`, `Parents`, `References`,
`Keys`, `Multiplicities`, `Groups`, `DeclarationDisjoint` and `StructuralSatisfies`
in `Clafer/Semantics/Structural.lean` at the pinned semantics revision. S3's group
union/direct-child bridge explains why childless abstract ancestors need no copied
fields in M1. S6's `genParentConst`, `genSetUniquenessConstraint`, `genGroupConst`
and `mkCard` in the pinned Haskell `Generator/Alloy.hs` were inspected as supplementary
context. The backend retains the adopted empty-group meaning and effective
bounds; frontend default agreement does not establish general group equivalence. All new runtime, proof and test
code is original project code under MIT; no upstream meanings or Haskell code are
copied. Local source/target finite tests do not replace the [generated-text oracle](comparison.md).

The [M1 preservation layer](structural-correctness.md) uses the same S1
`Configuration` directly, together with pinned `Semantics/Renaming.lean`,
`Semantics/Bridge.lean` and `Semantics/Normalization.lean`. It composes
`Configuration.structural_model_iff`, `erasure_correspondence` (including its
compiled-bank bridge) and `SpanModel.normalize_satisfies`, retaining their actual
global hypotheses. DPGraph's `Predicates.inRange_card` connects finite fiber counts
to its independent multiplicity meaning. Existing Mathlib finite-carrier and
right-unique reachability lemmas support the concrete representation; no package
or pin changes. The runtime uses the [structural encoding](structural-encoding.md)
guided by S6; the existing Haskell/Lean/Alloy oracle corpus remains required. New proofs and
fixtures are original project code; no upstream meanings or Haskell implementation
are copied or changed.

The [three-way comparison](comparison.md) reuses S8's pinned exact-candidate
protocol, generators, isomorphism, mutation and shrinking algorithms and S6's
paired Haskell capture. The downstream adapter invokes the existing M1 compiler,
S7-pinned Analyzer and native decoder; all new adapter/test code is original MIT.
S6's `genParentConst`, `genGroupConst`, `mkCard` and signature `extends` emission
were inspected to retain the virtual-root, multiplicity and hierarchy differences.
No source meaning, upstream tool, fixture identity or dependency pin is changed.
The four-byte `A ?` source in `tests/fixtures/comparison` is original project code.

The [authored parser correspondence](parser.md#sources-and-comparison) records the
exact grammar, generated Alex character classes and public Haskell parse checks.
It reuses Lean 4.35.0's Apache-2.0 `Std.Internal.Parsec` and UTF-8 cursor rather than
copying parser infrastructure. New Clafer-specific code and fixtures are original
MIT project code. Native properties and the existing hash-checked Haskell capture
adapter test syntax only. M1 capture rejection after parsing is not an M2 semantic
oracle; reference EOF crashes remain tool failures, and adopted profile exclusions
remain visible. No upstream meaning, dependency revision or language scope changes.

The [inherited structural extension](inherited-realization.md) uses S3's exact
`Realization.Core.Selected`, `Satisfies`, context views and injective link maps,
and `RealizationCompatibility.guarded_compatibility`. S3's `Compile.GroupSemantics`
supplies `Ancestor` and `ChildObjects`; S8 fixes the complete d01–d26 structural
inventory and distinguishes it from mathematical primitive interpretation and
c01–c12 constraints. S6's `genGroupConst` hierarchy traversal and parent constraints
were inspected as supplementary generator evidence. Existing [structural](structural-correctness.md) allocation,
representation and preservation machinery is reused through a checked layout.
The finite fixture and extension are original MIT code. No upstream semantics,
Haskell source, dependency pin, language whitelist or scope policy changes.

The selected [expression API](expressions.md) maps S4's complete typed constructor
inventory directly into the pinned upstream denotation. `DenotationSupport` and
`DenotationInvariance` supply observation invariance and original-link equivalence;
`Integer` and `CollectionMeaning` supply partial extraction and typed collection
meaning. S5's static `clafer.cf` productions and S6's `genPExp'`, `genIFunExp` and
`genOp` were inspected for constructor shape and operand order. The downstream
checker, observation extension and tests are original MIT code. No upstream
semantics, primitive domains, positive-map support or dependency pins changed.

The [target arithmetic stage](expression-encoding.md) uses S7's Integer
Expressions and Commands sections for `plus`/`minus`, signed intermediate bounds
and tuple cardinality. S6's active `genOp` branches provide the corresponding
operand-order guide. It reuses the existing target folds, Parsec grammar and
actual Analyzer adapter; its original implementation and tests retain MIT
licensing. The retained reference identity and pinned tools are unchanged. The
width-16 Analyzer translation-capacity failure is retained as an operational
result, not agreement or bounded UNSAT. The [source encoder](expression-encoding.md#source-constraint-translation)
composes the arithmetic and source range results.

The [source range proofs](expression-encoding.md#source-range-analysis-proofs)
connect the existing runtime analyzer to S4's unchanged partial `Expr.denote`.
They reuse `CollectionMeaning`, the downstream finite-observation bridge and
Mathlib's finite-set cardinality/image/product lemmas. Full primitive membership
does not establish finite observation membership; the latter is derived from the
executable observation check, original inclusion links and recorded lexical
bindings. S6's arithmetic operand-order guide remains supplementary; no Haskell
meaning is substituted. The proof and test code is original MIT code, with no
dependency, license, scope or upstream semantic changes. Scalar representability
in S7's bounded target is distinct from source-to-target expression preservation.

The [constraint translation](expression-encoding.md#source-constraint-translation)
uses S4's unchanged partial denotation and extension invariance for every
constructor and attachment. S7's field declarations, integer `sum`, conditional
expressions and restricted `iden` supply the independent target meaning. S6's
`genPExp'`/`genOp` and resolved navigation were inspected for role/operand order;
no Haskell execution or definitions enter the production compiler. Scalar fields
represent only observed integer objects, with generated range/injectivity facts;
the full mathematical primitive domain remains in the independent source model.
Existing target algebras, Std `mapM`/`flatMapM`, Parsec and the Analyzer adapter are
reused. Small traversal-success lemmas retain occurrence evidence; Mathlib
finite-set images/cardinality and list uniqueness supply the proof machinery.
New code is original MIT with no new dependency or license cost. Native tests,
Analyzer results and conditional kernel theorems retain distinct assurance boundaries.

The [source resolution/defaulting contract](resolution.md) maps S2's `Defaults`,
`GroupCard`, `AST.WellFormed` and Compile naming obligations, plus S3's
`Realization.Core.Selected`, to source occurrence paths and finite checked tables.
The downstream success, coverage, upstream default agreement, well-formedness and
selected-realization theorems have no satisfaction premise. Inspected pinned S5
`ResolverInheritance.hs` (`resolveNSuper`, `analyzeGCard`, `analyzeCard`),
`ResolverName.hs` (`resolveName`, `findUnique`), `Desugarer.hs` and S6 `Intclafer.hs`.
The exact direct-type lookup policy and common-domain importer comparisons are in
that contract; broader Haskell navigation/relocation is not silently admitted.
Standard-library finite traversal/decisions are reused, with no new dependencies,
semantic changes, copied upstream definitions or Haskell source. All new code and
fixtures are original MIT project code. The in-memory source profile retains
integer/inherited forms without extending the M1 interchange/backend contract.

The [source constraint elaborator](constraints.md) uses S4's `Support.MapResolved`,
`Typing.Expr` and partial `DenotationLaws`, S3's original owner/field identity, and
S8's exact c01–c12 manual `Examples/Telematics/Expressions.lean` inventory.
Pinned S5 `ResolverName.hs` and `Desugarer.hs` were inspected for binding priority,
head/target navigation and connective shape; broader Haskell features are not
adopted. Existing source/typed representations, Std traversal and native harnesses
are reused. The independent compiler inference rules, proofs and reconstructed
fixture are original MIT project code. No upstream definition, dependency pin,
license, runtime primitive domain or scope policy changed. The manual-inventory
comparison is distinct from grammar correspondence and backend preservation.

The [native resolved-IR driver](cli.md) composes the unchanged S1/S6-guided
admission/backend/text APIs. S6 `Generator/Alloy.hs` (`genModule`, `header`) and
`ClaferArgs.hs` were inspected: Haskell's inferred scopes, optional validation and
multiple output modes do not replace the adopted explicit-bound, compiler-only
command. The pinned upstream `Verification/ImportMain.lean` documents its external
strict-decoding boundary. Lean 4.35.0 `Lean/Data/Json/Parser.lean` and
`Std/Internal/Parsec` supply reusable parser primitives; `Init/System/IO.lean`
supplies strict UTF-8, streams, exclusive creation and rename. The driver adds
strict duplicate-key/surrogate/natural-token checks instead of using the generic
parser's information-losing behavior. JSON output uses the existing Lean library.
The [reuse assessment](cli.md#reuse-assessment) records CLI-library alternatives,
runtime/proof limits and licenses. New code/fixtures remain original MIT; imported
Lean library code remains Apache-2.0. No semantic definition, Haskell code,
dependency pin or trusted scope policy changes.

## Source pipeline composition

The pinned S3 `Realization.Satisfies` and S4 `IntegerBinding` jointly require an
infinite rooted primitive domain. The complete S8 telematics `Input`,
`Configuration`, `Satisfaction` and `Compiled` modules supply the independent
full-domain inventory. Local `PipelineLimits` counterexamples establish why
[unrestricted primitive multiplicity and a full integer carrier](pipeline.md#full-integer-carrier)
are necessary for constraint-bearing source. `PipelineCompletion`, `PipelineRestriction`
and query agreement discharge the compiler-specific finite observation bridge.
Mathlib countable equivalences and finite permutation extension supply allocation
existence; no new runtime library or semantic definition is vendored.

S5/S6 remain syntax and compatibility guides. The full source comparison extends
the inherited/source observation boundary with its own proved checker; it does
not run the guarded Haskell/M1 comparison outside its accepted domain. See the
[pipeline inventory](pipeline.md) for exact theorem and external replay limits.

<a id="private-qualification"></a>

## Qualification

Runtime optimization reuses the pinned Lean `Vector.ofFn`, array access/equality,
list folds and `Nat.repeat`, plus its `@[csimp]` equality-rewrite mechanism.
Existing backend allocation and printer chunks supply the domain-specific work;
the [backend](structural-encoding.md), [renderer](alloy-text.md) and
[resolver](resolution.md) contracts state the exact equality boundaries. Standard
containers suffice for these finite tables; adding a graph or indexing package
would introduce a dependency without removing the Clafer-specific proof work.
The existing qualification harness and pinned Haskell adapter supply measurements.
No source pin, library dependency or license changes; the added code is original
MIT project code and reused Lean facilities retain their Apache-2.0 license.

The [qualification adapters](qualification.md) reuse the full accepted corpus,
S5/S6's public `Language.Clafer` pipeline and `Generator.Alloy.genModule`, the
existing verified external build recipe, and S7's actual parser for independent
scope/bitwidth auditing. They never widen the M1 semantic comparison guard.
Lean 4.35.0 `Init/System/IO.lean` supplies monotonic stage timestamps; Lake's actual
linker response supplies the native object closure. Python's standard libraries
and GNU time supply process measurement, source export and receipts. These tools
run externally; their source is not copied. The adapters and generated inputs are
original MIT code. No source meaning, dependency pin or theorem premise changes.

The local candidate includes the project MIT notice, Lean Apache-2.0 license and
its bundled third-party `LICENSES`, plus semantics MIT and Mathlib Apache-2.0
notices for source/dependency attribution. The inspected Linux link command uses
static GMP (the Lean distribution identifies LGPL-3.0), libc++/libc++abi/unwind
(LLVM notices), and the Lean runtime; shared glibc libraries are recorded and
remain host prerequisites. Retain the full link response, static archive hashes
and `ldd` output with each candidate. Haskell/Stack/GHC, Java and the multi-license
Alloy JAR are comparison/build tools and are not packaged. This prepares a local
review artifact; redistribution obligations for linked components must be resolved
before distributing a binary.

## CI policy selection

The deadline selector adapts `scripts/ci_scope.py` from the pinned S1 repository
(MIT, copyright 2026 Kacper Bak). Python's standard JSON and SHA-256 libraries
preserve the exact reviewed policy transition; IntentBond consumes the external
selected policy. The [build contract](build.md) records the reuse assessment and
tests. The same pinned source's CI, native Lake cache, `runtime.cached_runtime`
and timing wrapper supply the [cache/replay design](build.md#build-implementation).
Lake 4.35's own `Lake/Config/PackageConfig.lean` documents artifact reuse and local
restoration; no custom build-cache protocol is introduced. This adds no compiler
meaning, proof assumption or runtime dependency.

Dependency-based reference qualification reuses Git's path diff, Python's standard
library, and GitHub Actions' `workflow_call`, job dependencies and always-running
aggregate gate. The [profile contract](build.md#ci-profiles) records the conservative
input classification, fresh evidence boundaries and tests. Whole-workflow path
filters cannot express that policy and can leave required checks pending. The
selector adds no compiler meaning, proof assumption, runtime dependency or license.

## Behavioral sources

The executable [first-slice IR](behavioral-ir.md) uses accepted S2/S3 commit
`27a5bbe86657edab00980da57b2f86221f92a5f1` as its original source baseline.
The installed main pin above retains these definitions.
Its inspected `Trace`, `Environment`, `Formula`, `Normalization`, `Denotation`
and `Lowering` modules supply shared identities, current set observations,
signed truth and lifetime lowering. `Examples.cycling` supplies the independent
admissible trace reconstructed by compiler fixtures. Relative to the preceding
static pin `26f884d3f630bd74a88cfe43d6f31118e9025bbf`, all 138 changed pre-existing
static Lean modules differ only in comments/whitespace; toolchain, transitive
dependencies, static checker algorithms and fixture bytes are unchanged.
The executable normalizer adapts the MIT upstream constructor equations with
their source meaning retained only upstream. Its
[reuse and proof boundaries](behavioral-ir.md#reuse-assessment) distinguish
native algorithms and interpretation proofs from the full-profile components.

The [behavioral compiler contract](behavioral.md) uses the accepted
[main dependency](#accepted-semantics-main-dependency). The stable source
locators below were inspected at `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4`, the
[accepted surface integration](https://github.com/kbak/clafer-semantics/pull/147).
The original [profile adoption](https://github.com/kbak/clafer-semantics/pull/131)
was accepted at `a260e69e0ce44d47220dc629f5526ab8bce28d8a`. The newer contract
revision contains the accepted trace, signed-formula, structural/partial-atom,
surface and finite-verification work. S7 retains those meanings and adds generic
qualification APIs; compiler qualification retains its own acceptance gate.

| Accepted upstream interface at the installed pin | Downstream use and limit |
| --- | --- |
| [Profile and B01–B32](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-profile.md) | Completion inventory, source locators, D1–D5 and two-repository gates |
| [Trace/snapshot foundation](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-traces.md) | Shared identities, fixed parents, live projection and actual common-fragment assumptions |
| [Signed formulas/environments](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-formulas.md) | Parent cancellation, capture/current navigation, normalization/lowering; mathematical translations are not a production executable normalizer |
| [Structural/partial atoms](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-structure.md) | Richer inheritance/references, groups, integer observations, strict temporal definedness and initializer disposition |
| [Surface reductions](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-surface.md) | Modifiers, transitions, thirty pattern cells, assertions/scenarios; parsing and target preservation remain downstream |
| [Finite verification](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-verification.md) | Lasso unfolding, history and exact checking; generic observation agreement still requires concrete adapter proofs |

Behavioral primary reference: Juodisius et al., *Clafer: Lightweight Modeling of
Structure, Behaviour, and Variability*, Programming 3(1), article 2 (2019),
[arXiv v1](https://arxiv.org/abs/1807.08576v1),
[DOI](https://doi.org/10.22152/programming-journal.org/2019/3/2).
The accepted upstream ledger records PDF SHA-256
`b5c03f295e490e7c97878cdb3b9f2ec6aa3f6b667de19988a48c59faba76bb06`
and CC BY 4.0. This downstream contract follows that source audit, not a new
independent PDF audit. Locators use printed pages: §5 Definitions 1–5 and expression
equations pp. 2:23–28; §6.1 defaults/sugar pp. 2:29–32; §6.2 implementation p. 2:32.
Sections 8–9 provide context. The historical Alloy 4.2 encoding is not the selected
Alloy 6 meaning; the structural SoSyM baseline remains separate.

The behavioral Haskell candidate is
[`af858ec0fe3ce2ceacb7fd120947c058233086d6`](https://github.com/gsdlab/clafer/tree/af858ec0fe3ce2ceacb7fd120947c058233086d6),
from [release review](https://github.com/gsdlab/clafer/pull/113). Adoption of later
release bytes requires a recorded delta review. All paths and hashes below refer
to exact Git-blob bytes at this SHA, independently checked against its clean
checkout; acquisition copies with added newlines are not substitutes.

| Source path at the candidate | SHA-256 | Use |
| --- | --- | --- |
| `doc/temporal-semantics-errata.md` | `d42a6f72ddfc70e3ef628e7d7ad2c3ae99e468185fdb5a7056fe80d38e861d4d` | T1–T13, including deliberate departures |
| `doc/static-semantics-errata.md` | `0e3aa5c138c70773709fd13f210301100d7116f091482518ab2f5fe0a4080d8c` | S1–S12 and structural prerequisites |
| `doc/CheatSheet.md` | `d8de22fc45850ca87dc080121fcf1a1421db86c4951ea9f56ec5e9ba6f14ee5e` | Temporal modifiers, operators, transitions, patterns and aliases |
| `src/clafer.cf` | `14176e1c241d7d44d368535ff1664b75da39a054ee32f880456a4b7291921a2f` | Grammar inventory and source precedence for the frontend handoff |
| `src/Language/Clafer/Generator/AlloyLtl.hs` | `68423e38d8002f6875bc72ebe267959cc5f44b2d0a5077446e304ae6e1a5057a` | Signed translation, current navigation, finality and comparison gaps |
| `src/Language/Clafer/Intermediate/Desugarer.hs` | `8fbe866a70521a25dfe75ad191dc0737887376877ccfb37921c26a4901e68ad7` | Transition chains, pattern expansions and initializers |
| `LICENSE` | `c630ca360518868845360498ff7b2ba02c6bd39cc718ff403e5eef4d875667be` | MIT; retain notices if copying source/material |

The accepted profile's decision register links the public D1–D5 dispositions.
The [temporal oracle](oracles.md#temporal-provisioning-execution-and-replay)
reproduces the Haskell candidate separately from the static profile. Its source
archive SHA-256 is `07eb00dfa1fd13bf2ff4f546b83ae2df6714e1a5fa9f2ae45964f6f746a19899`;
the canonical file/digest inventory hash is
`2b6306253edcbd6c39021c8aacf760f8bf501294619f1434e477bfd7d51420f0`.
The unchanged `stack.yaml.lock` is 1410 bytes with SHA-256
`2bed95387bc9ad79df4f70de77a9c7e468125c10a09a68a42da233434b59acff`.
The [profile](../scripts/oracles/temporal-profile.json) and
[fixture inventory](../tests/fixtures/temporal/inventory.json) retain exact build,
query and source identities. Six upstream MIT fixtures are read from the external
archive with its `LICENSE`; eight additional fixtures and adapters are original MIT
code. The [reuse assessment](oracles.md#temporal-oracle-reuse-and-boundary) records
tool/library choices and the [release comparison process](oracles.md#comparing-the-final-057-release)
requires explicit review of any later source bytes. The source register does not
claim all behavioral rows or known comparison gaps are qualified by this corpus.

For the historical `af858ec` comparison, notable gaps are corrected response-between and first-opener
precedence-after, the distinction between per-head `finalref` and target-image
`finaltarget`, shared inherited-reference assignments, concrete supers, and
mathematical arithmetic/definedness versus bounded backend behavior. C2/C9 must
retain them in the comparison domain; no blanket 0.5.7 equivalence is asserted.

### PR113 delta candidate

The separate qualification profile pins
[`9a0f16ed18bdfb5277bedcc6577731f4b422be77`](https://github.com/gsdlab/clafer/tree/9a0f16ed18bdfb5277bedcc6577731f4b422be77).
It does not replace `af858ec` as the primary behavioral source or change the
static comparison pin. Its accepted comparison role does not adopt it as the
primary source profile.
The [delta inventory](../tests/fixtures/pr113/delta.json) records both endpoints,
all ten intervening commits and exact old/new hashes for all 40 changed source,
build, documentation and test files outside generated regressions. The full
951-file delta also includes 911 generated regression outputs; their aggregate
inventory hash is retained, and those outputs are not fresh execution evidence.

| Changed area | Qualification consequence |
| --- | --- |
| `UIDs`, `QNameUID`, `AlloyNames`, resolver and generator consumers (`b6c3861`) | Least-partially-qualified UIDs, apostrophe/copy suffixes and separate Alloy reserved/derived names require the captured forward map and renamed IR. HTML/graph names and Choco variables change too. |
| `ResolverName`, `ResolverRoot`, `ResolverType`, `TypeSystem`, `Common`, optimizer | Explicit names still resolve/type-check; hierarchy traversal stops cycles; intersection/difference navigation and `noclafer` support expand. Redundant comparisons/navigation warn. Static `clafer` values remain outside the selected temporal domain. |
| `ClaferArgs`, `Import`, `Clafer`, `ChocoModel`, `Explicit`, `Choco` | `--explicit` selects `-f -k -l --ss=none`; shared explicit printing lifts assertions and records scopes. Temporal explicit output carries `--tl`; temporal Choco solving and real/double explicit output remain unsupported. |
| `Intclafer`, `Desugarer`, `AlloyLtl` (`b2875f3`, `8a12ae7`, `9a0f16e`) | Corrected response-between/first-opener formulas, parent-scoped target images and modifier arrays require independent distinguishing runs; both modifier orders are retained. |
| Grammar/build/license | `src/clafer.cf`, `stack.yaml` and MIT license are unchanged. `clafer.cabal` exposes the new modules without adding dependencies. Stack generates the same dependency lock; it is not a tracked archive file. |
| Test harness/docs/fixtures | Explicit outputs join regression checks; tests adopt new names and modifier expectations. The inherited-final fixture adds both orders; `noclafer` adds static laws; escapes adopt new names and an obsolete generated source is removed. These changes do not authorize broader native language support. |

Archive SHA-256:
`f401c77bd6ee17ed77483cfa8d2e89bb57913e99de46272de217694dda17c7b4`.
Canonical source file/digest inventory SHA-256:
`a847d0581c323889535eef91a262154128ddb69af6bb8bdc1e72a979a1b2b871`.
Generated `stack.yaml.lock`: 1410 bytes, SHA-256
`2bed95387bc9ad79df4f70de77a9c7e468125c10a09a68a42da233434b59acff`.
The [candidate profile](../scripts/oracles/pr113-profile.json) and
[oracle contract](oracles.md#pr113-delta-qualification-candidate) bind tools,
licenses, fresh execution and proof boundaries.

| Contract surface | Historical `af858ec` | Candidate `9a0f16e` | Remaining boundary |
| --- | --- | --- | --- |
| Static regression/capture | Original structural pin and receipts | Unchanged | No native source expansion |
| UID and reference schema | `cN_` UIDs, scalar modifiers | LPQ UIDs, explicit Alloy map, modifier arrays | Candidate importer only; no shared schema weakening |
| Response-between / precedence-after | Discrepancy witnesses reproduced | Selected corrected witnesses agree | No full pattern equivalence claim |
| `finaltarget` / combined modifiers | Per-head equality / missing image conjunct | Image-preserving swap and both-conjunct witnesses agree | No general inherited-reference preservation theorem |
| Temporal explicit output | No qualified explicit output | 64 temporal sources plus one static example, fresh fixed points and bounded queries | Exact lassos and Lean explicit-form proofs remain separate |
| Primary source adoption | Retained | Pending independent delta review | No implicit release/main acceptance |

### PR113 union and root-binding delta

The successor candidate pins
[`c7a2fb7d0ba601f52efeac459d12f859a40580fe`](https://github.com/gsdlab/clafer/tree/c7a2fb7d0ba601f52efeac459d12f859a40580fe)
without replacing either prior profile. Its [delta inventory](../tests/fixtures/pr113/c7-delta.json)
records all four commits and all 240 changed files: 11 source, fixture, build and
documentation files, and 229 generated regressions (164 explicit, 63 Alloy,
one HTML and one graph). Generated outputs are source inventory, not fresh
execution evidence. `src/clafer.cf`, `clafer.cabal`, `stack.yaml` and the MIT
license are unchanged; Stack generates the same pinned lockfile.

| Commit | Inspected boundary and disposition |
| --- | --- |
| `2c8022631fa5f214df32b40e28af5d642ba87212` | Static `Alloy.getTarget` and temporal `AlloyLtl.refType` emit signature unions for nested reference targets. The updated inherited fixture adds `garage.spare ++ gas`; explicit source retains target membership. |
| `8298fbd8a7701351268615824d10140f02205299` | `Clafer.runValidate` propagates tool failures, `validateClafer` recompiles explicit output, and help/docs describe the CLI effect. Counterexamples remain completed results; the library exporter does not call this CLI validation path. |
| `67324c57e7ccf3ac95b41c0607b865d845c33e48` | `Explicit.exExp` prints compact dot navigation, `diff-regressions.sh` uses exact comparison, and the positive runner parallelizes models. Its invalid-worker false-success remains a known infrastructure gap; this repository supervises its own complete runs. |
| `c7a2fb7d0ba601f52efeac459d12f859a40580fe` | `AlloyLtl.forEveryInstance` binds root directly while retaining `always`; `bindTo` preserves token boundaries and `Concat` traces. Nested live guards are retained. Warnings are measured through Analyzer callbacks rather than inferred from the changelog. |

Archive SHA-256:
`8308153e08ea84828766bfb2b23851dfa01d362665c3fee3a739950412a99b63`.
Canonical source inventory SHA-256:
`82ec8f4eea219a567dd36b13eaede0223240fa73438bb46a18ce89b281df0bcf`.
The [profile](../scripts/oracles/pr113-c7-profile.json) binds these identities,
Stack/GHC, Alloy 6.2.0 and the unchanged lock hash. The
[oracle contract](oracles.md#pr113-union-and-root-binding-candidate) records reuse,
closed union correspondence, exact output, warning evidence, static/backend
separation, the retained top-level `this.item` parser failure and the live-union-target
soundness discrepancy (original SAT versus explicit bounded UNSAT). No native Lean
expression-valued reference support or upstream resolved-import change is adopted.
The [accepted comparison review](https://github.com/kbak/clafer-compiler-lean/issues/95)
retains those limits; any later release delta still requires separate review.

The [official Alloy 6 reference](https://alloytools.org/alloy6.html) supplies the
independent temporal construct guide: mutable signatures/fields, ordinary temporal
operators, lasso instances and explicit `steps`. Reuse the existing Alloy 6.2.0
source/JAR identities above. C2/C3 must retain source-matched runtime options,
temporal reference correspondence and actual Analyzer evidence; visiting the live
reference is not a new immutable source pin or solver proof.

The [temporal target correspondence](alloy-temporal.md#source-correspondence-and-reuse)
uses the same immutable Alloy source revision. Inspected
[`ScopeComputer`](https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/ScopeComputer.java),
[`BoundsComputer`](https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/BoundsComputer.java)
and [`TranslateAlloyToKodkod`](https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/TranslateAlloyToKodkod.java)
for trace-wide identity capacity/disjointness, mutable multiplicities, temporal
operators and current `iden`. The live reference is explanatory; source locators
and actual pinned runtime observations retain the correspondence boundary.
Upstream `Behavioral/Lasso.lean` supplies the source-side history distinction,
and candidate `AlloyLtl.hs` `initialConsts`/`appearsNow` supplies birth-guard context.
No source truth is imported into target truth. Existing standard-library instruction-list folds, Parsec, bounds, names,
source-map and oracle machinery are reused; no dependency or license pin changes.

The [first-slice encoding](behavioral-encoding.md#reuse-assessment) uses the same
accepted source meaning and temporal target. Its explicit lifetime guards follow
the pinned upstream signed denotation; Haskell `AlloyLtl.hs` remains comparison
context for birth, cancellation and temporal syntax. Concrete global trace and
live-snapshot transport are compiler proofs, not facts assumed from Haskell
output. The [native/Analyzer corpus](behavioral-encoding.md#fixtures-and-validation)
records emitted modules, complete witnesses and source/tool hashes independently
of those kernel statements. No source or tool pin changes accompany this slice.

The [full-profile encoder](behavioral-encoding.md#full-profile-runtime) reuses
that target and the accepted upstream `PartialObservation`, `PrimitiveExpression`,
`IntegerObservation`, aggregate, lifetime and structural definitions. The
behavioral paper's builtin integer domain is the mathematical integers; the
full completion preserves it while bounding only target observations. The pinned
Haskell `AlloyLtl.hs` integer import, strict arithmetic lowering, pattern expansions
and inherited modifier combinations supply comparison context. The behavioral
frontend provisions the implicit integer declaration before separately adding a
numeric scenario. This repairs the compiler's separate-scenario admission path;
it changes neither the paper nor the upstream/Haskell integer meaning.

No new semantic dependency or tool pin is introduced. Mathlib's existing finite
sets, indexed occurrences, cardinality, equivalences and relation libraries
supply proof machinery; Lean/Std supplies executable list/vector traversals.
The full proof modules and infinite source completion are absent from native
compiler imports. Exact source and tool hashes accompany the expanded native
and Analyzer fixtures.

Workflow changes reuse the accepted upstream MIT `scripts/tickets.py` Ready mapping
and live Project-ID test pattern, Python's standard library and existing Actions
conditions. The [reuse assessment](behavioral.md#static-separation-and-reuse)
records remaining compiler/proof gaps. The planning tooling introduces no runtime
or license dependency. The structural library repin is recorded below; no upstream
semantic definitions or Haskell code are vendored.

## Exact temporal runtime sources

The [resolved temporal runtime](temporal-comparison.md) uses the unchanged APIs
inspected at `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4`. Its executable adapter
uses and proves agreement with
[`Clafer/Behavioral/Lowering.lean`](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Behavioral/Lowering.lean),
[`Verification.lean`](https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/Clafer/Behavioral/Verification.lean)
and their imported finite set adapter. The lowering equations are adapted from
that MIT source; source meanings and finite evaluation remain upstream imports.
The pinned MIT `scripts/verification/relation.py` supplies whole-graph
isomorphism. Its static `candidates.shrink` requires a static candidate protocol;
the temporal harness uses the same greedy deletion strategy with complete
frame-indexed trials and fixed bounds instead of altering that upstream API.

The Haskell adapter is specifically for
[`af858ec0fe3ce2ceacb7fd120947c058233086d6`](https://github.com/gsdlab/clafer/tree/af858ec0fe3ce2ceacb7fd120947c058233086d6),
profile `behavioral-0.5.7-candidate/v1`, with paired JSON/`tmp.als` receipts and
the retained effective options. The temporal errata T1–T2, T7 and T13 inform the
identity/lifetime witnesses. The existing Alloy 6.2 bridge exports each frame and
the loop; the harness adds a private phase clock using the registered Alloy 6
temporal operators. No Haskell source, tool revision, semantic pin or dependency
license changes. The newer PR113 profile and original-versus-explicit models are
not admitted by this adapter; their qualification remains separate.

## Behavioral dependency delta

The earlier accepted revision `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4`
adds the structural/partial-atom APIs needed by the
[behavioral structural handoff](behavioral-structure.md). The static regression
baseline is `26f884d3f630bd74a88cfe43d6f31118e9025bbf`. Across that delta, the
existing static structural, constraint, verification, `FormalCD` and `DPGraph`
definitions retain their meanings; the changes add trace annotations, lemmas and
new behavioral/group modules. `Clafer/Semantics/Groups.lean` supplies the effective
head-union meaning used by the new bridge: `Ancestor`, `ChildObjects` and `Holds`
move out of `Compile/GroupSupport.lean` and are re-exported there with unchanged
bodies (the ambient universe is generalized). Other pre-existing nonbehavioral
Lean changes are comment-only. No moving branch is a dependency.

The toolchain, manifest transitive revisions, static verification adapters,
Haskell 0.5.4 capture pin and Alloy distribution/bridge bytes are unchanged. The
oracle profile and fixture inventory identify the installed semantics revision;
fixture contents and expected static outcomes are retained. External tool receipts
must be prepared for that revision rather than relabeling older evidence. The
mandatory full check replays static kernel declarations and comparisons along
with the new bridge; independent review still decides acceptance of the repin.

The behavioral source implementation reuses the existing resolver/default and
expression structures, Lean/Std collection operations and existing Mathlib
proofs. The [component reuse assessment](behavioral-structure.md#reuse-and-evidence)
records the richer-domain gaps, native/proof separation and unchanged dependency
and license costs. Haskell `af858ec0fe3ce2ceacb7fd120947c058233086d6` supplies
behavioral syntax evidence; it does not replace the static comparison compiler.

## Behavioral frontend sources

The [behavioral frontend](behavioral-frontend.md) retains the meanings inspected at
semantics `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4` and Haskell
`af858ec0fe3ce2ceacb7fd120947c058233086d6` pins. Inspected `src/clafer.cf`
(`Exp` and `Exp1`–`Exp27`, modifier lists, arrows, scopes, enum/initializer/assertion forms),
`Desugarer.hs` (`desugarRefModifier`, `desugarTrans`, `desugarSequence`,
`translateTmpPatterns`, binder and initializer cases), `AlloyLtl.hs`
(`genQuant`, `genDecl`) and CheatSheet temporal sections. The registered source
hashes remain unchanged. Haskell list-to-first-modifier truncation and its two
pattern discrepancies are not adopted. The native comparison retains its `LetExp`
desugaring crash distinctly from parsed/compiled outcomes.

Executable reduction equations adapt upstream MIT `Patterns.expand`,
`Transitions.Chain.sequence`/`expand`/`declaration` and `Modifiers.expand`.
Proof-only interpretation establishes equality with these pinned transformations
and reuses their independent interval/sequence/modifier agreement results.
Modifier binding uses the accepted ancestor analysis and `Modifiers.Effective`.
`PrimitiveExpression` supplies the partial syntax, `PartialObservation` and
`PartialCompatibility` supply strict-domain composition, and `Properties` supplies
model/assertion/scenario meaning. Grouped counting instantiates `Quantifier.eval`
with complete ordered assignments behind the original raw-body barrier. This
compiler composition does not change the pinned unary definitions. The compiler
`ExpressionBinders` bridge proves the grouped composition used by the independent
authored source judgment.
`Initializers.constant` supplies the resolved presence-guarded equation and its
strict-definedness premise. Lexical plans reuse the existing reserved-name policy;
group lowering uses the upstream captured `letSet` and singleton-pushing quantifier
constructors, with native set difference for disjoint choices. The generic
observation pullback proves that keeping atom syntax fixed across model traces
preserves strict definedness and signed truth. No source/target agreement premise
is added by that representation change.
No upstream meanings or Haskell code are vendored. Existing Lean/Std parser and
collection machinery is reused; the component contract records runtime/proof
boundaries and the composed elaboration proof. New code is MIT,
Lean libraries remain Apache-2.0; no dependency or license cost is added.

Grouped quantifiers follow complete ordered assignments, as specified in the
[Alloy quantified-formula reference](https://alloytools.org/spec.html#expressions)
and the [older reference, p.293](https://alloytools.org/download/alloy-language-reference.pdf#page=35).
Pinned Haskell `desugarDecl` retains all local IDs in one declaration, and
`AlloyLtl.genQuant`/`genDecl` emits one quantifier over the complete list.
The static paper's [public author preprint, Appendix D, pp.31–32](https://gsd.uwaterloo.ca/sites/default/files/2014-Bak-Clafer-Unifying-Class-Feature-Modeling%28SOSYM%29.pdf#page=31)
and the [behavioral paper, pp.2:27–28 and 2:30](https://arxiv.org/pdf/1807.08576v1#page=27)
give unary core quantification and attribute the constraint language to Alloy;
neither equates grouped uniqueness with nested uniqueness. This supplementary
static-paper inspection used the public preprint, not the publisher offprint.
The pinned upstream unary `Quantifier.eval` is consistent with these sources.
Its guide's general nesting suggestion must be qualified for grouped `no`,
`one` and `lone`; it supplies no grouped-counting preservation theorem.
Finite probes (15 direct Alloy cases and four Haskell-generated cases) corroborate
this distinction without establishing general elaboration correctness.

Value elaboration additionally follows pinned `Intermediate/ResolverType.hs`
(`resolveTPExp`, `addSome`) and `Intermediate/TypeSystem.hs`
(`getIfThenElseType`) for Boolean presence coercion and conditional typing.
`Generator/AlloyLtl.hs` preserves non-Boolean conditionals inside value expressions;
its negation pushdown stops at that boundary. The
[Alloy expression specification](https://alloytools.org/spec.html#expressions)
supplies heterogeneous union typing and domain/range restrictions; both restrictions
on unary relations reduce to intersection. These comparisons do not override the
adopted strict branch-definedness and D3 integer semantics. Fresh generated-output
regressions retain conditional denominators inside division. `PrimitiveExpression`
has no value-conditional or partial-navigation constructor, so compiler observations
compose the pinned primitives with `Step.image` and strict conditional selection.
The source pin and the separate PR113 comparison role remain unchanged.

The same fresh captures preserve two Haskell semantic failures: a collection-valued
conditional followed by `.parent` is prematurely classified as Boolean, and
`noclafer.A` fails name lookup. These failures do not narrow the selected collection
conditional and polymorphic-empty contract or establish Haskell agreement for those
cases. Native compiler regressions and the independent source/partial-expression
rules cover their accepted meanings separately.

## Accepted semantic qualification dependency

The source integration was qualified against accepted S7 commit
`5182c8f5884eddfd8bff8a26b493a8550f0162b6`, accepted through
[upstream qualification](https://github.com/kbak/clafer-semantics/issues/129).
The delta from `6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4` adds
`Composition`, `PartialLowering`, `FinitePartial`, `FiniteComposition` and
`QualificationExamples`, with their documentation and test inventory. Existing
structural and behavioral meanings, static adapters, fixture bytes, Lean and
transitive dependency revisions are unchanged. Earlier source locators above
remain citations at their inspected revisions. The
[installed main dependency](#accepted-semantics-main-dependency) retains these
meanings; historical receipts keep their original identities.

S7 explicitly accepts `behavioral-0.5.7-candidate/v1` with Haskell
`af858ec0fe3ce2ceacb7fd120947c058233086d6` and D1–D5. This source integration
retains that immutable prerelease disposition. It does not adopt a moving
release or relabel the separately qualified PR113 comparison candidates.
The static Haskell 0.5.4 and Alloy 6.2.0 pins and their expected corpus outcomes
are unchanged; fresh tool receipts bind their reuse to the installed semantics source.


### Full source observation adapter

The [source workflow](behavioral-source.md#exact-comparison-and-replay) reuses the
accepted full encoder, strict Analyzer table reader, phase clock and global graph
comparison. Its executable Python reference reads the exported source expression
constructors, not target formulas. Equations follow accepted S7
[`Denotation`](https://github.com/kbak/clafer-semantics/blob/5182c8f5884eddfd8bff8a26b493a8550f0162b6/Clafer/Behavioral/Denotation.lean),
[`PartialObservation`](https://github.com/kbak/clafer-semantics/blob/5182c8f5884eddfd8bff8a26b493a8550f0162b6/Clafer/Behavioral/PartialObservation.lean),
[`Lifetime`](https://github.com/kbak/clafer-semantics/blob/5182c8f5884eddfd8bff8a26b493a8550f0162b6/Clafer/Behavioral/Lifetime.lean),
[`Modifiers`](https://github.com/kbak/clafer-semantics/blob/5182c8f5884eddfd8bff8a26b493a8550f0162b6/Clafer/Behavioral/Modifiers.lean)
and [`Structural.Keys`](https://github.com/kbak/clafer-semantics/blob/5182c8f5884eddfd8bff8a26b493a8550f0162b6/Clafer/Behavioral/Structural.lean).
This reference is tested, not kernel proved or a certified S7 adapter. Its review
boundary remains explicit alongside the separate compiler proofs.

The revision-qualified c7 exact comparison retains the inherited set-key
counterexample described in the source workflow. Source `Keys` already covers
inherited reference kinds in each concrete containment fiber; the Haskell output
omits this obligation. Its SAT result is a discrepancy, not a new accepted source
meaning. The [accepted C10 review](https://github.com/kbak/clafer-compiler-lean/issues/79)
retains this limitation without changing source semantics.

## Accepted semantics-main dependency

The installed dependency is immutable upstream main
`f00e5dacb07eed51026f69fcf699683210d394d3`, accepted through
[semantic main integration](https://github.com/kbak/clafer-semantics/issues/130).
Against the qualified S7 pin above, existing source definitions and theorem
statements used by the compiler are unchanged. `Formula.domainFormula_agrees`
combines identical quantifier and capture proof branches. Added modifier and
root-attachment witnesses, source-import checks, trace tags and current source
contracts strengthen upstream qualification. The static `DPGraph` edits and
verification-adapter changes are comments only. Lake, Lean, Mathlib, licenses,
static fixture bytes and Haskell/Alloy pins are unchanged.

The optional `Clafer.Behavioral` source entrypoint remains separate from
`Clafer.Behavioral.FiniteComposition`. Full preservation continues to require
richer structural admission, effective modifiers, exact context selection,
history-aware observations, finite identity/range capacity and the documented
static correspondence premises. The Python full-source observer remains a tested
adapter, not a kernel-certified finite evaluator. The
[upstream qualification inventory](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/docs/behavioral-qualification.md)
records the exact APIs and assumptions. Earlier locators remain at their inspected
revisions; new tool receipts must match this installed pin.

The primary source remains `behavioral-0.5.7-candidate/v1` at `af858ec0fe3ce2ceacb7fd120947c058233086d6`,
with D1–D5. The accepted c7 comparison retains inherited-set duplicate targets,
live-union-target disagreement and root-navigation rejection. The upstream
[source ledger](https://github.com/kbak/clafer-semantics/blob/f00e5dacb07eed51026f69fcf699683210d394d3/docs/sources.md)
classifies subsequent `eb2f653a02979d0db35451ed6abf131eaf7c355a` and
`8cfa0f3740f1cfb515f9862bc8993b826fa08a67` as build, documentation and negative-fixture
changes. No runtime qualification or final-release adoption of those bytes is claimed.
