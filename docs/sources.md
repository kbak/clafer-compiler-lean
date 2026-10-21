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
| Compiler scaffold | `36ef6100a17c7d8d312a9df2916dc3fababe19e0` | Starting documentation/check baseline; repository MIT license |
| [Clafer Semantics](https://github.com/kbak/clafer-semantics/tree/1454e3bd2ce9697923cdcef3863c816651ffc147) | `1454e3bd2ce9697923cdcef3863c816651ffc147` | Installed Lake dependency; [MIT, Kacper Bak](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/LICENSE). The manifest retains this commit and its inherited dependencies. |
| [Haskell Clafer](https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c) | `15adb2216909421bcb5022174d2d84ef2b42307c` | Comparison/compiler/grammar baseline; [MIT, GSD Lab and ISD Lab](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/LICENSE). External tool, not production runtime dependency. |
| Lean and Mathlib | Upstream [toolchain](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/lean-toolchain): `leanprover/lean4:v4.35.0`; [Mathlib revision](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/lakefile.toml): `56a005855ea17e0b0958f73ec801ae140b0a1679` | Selected toolchain and inherited Mathlib pin for build task #5 |
| Alloy | 6.2.0, source `794226dd07b536fe35c5ca44b529417183cd629b`, Java 17+, SAT4J | Initial external validation profile; upstream [runtime/hash/options](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/scripts/verification/alloy_runtime.py) and [bridge](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/scripts/verification/AlloyBridge.java) |
| IntentBond | `a430efa8d82e2a88ed2607bfe838066bb9d73f3c` | Existing [requirements pin](../requirements/intentbond.txt), unchanged by contract adoption |

The Alloy distribution identity reproduced by #6 is SHA-256
`6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d`.
Retain actual JAR/tool hashes, Java vendor/build, solver and all effective options,
scopes, bitwidth, source/IR/output/candidate identities and exact replay commands
outside source. The version label alone does not reproduce a comparison.
Before copying code or fixtures, inspect the pinned file's notices and retain
required attribution. The [oracle inventory](oracles.md#inspected-licenses-and-distribution-contents)
records #6's inspected source/distribution notices; #21 must reconcile packaged
dependencies before packaging. A source citation is not a redistribution license.

## Published source and locators

Primary language reference: Bąk et al., *Clafer: unifying class and feature
modeling*, Software & Systems Modeling 15, 811–845 (2016), online 2014,
[DOI 10.1007/s10270-014-0441-1](https://doi.org/10.1007/s10270-014-0441-1).
The upstream [source map](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/sources.md)
records the inspected 37-page publisher e-offprint, SHA-256
`653fc7868637680c44b6176d8ff643ec20149534fe1681ea4fc4ce636db76f2d`.
Its one-based PDF positions include two cover sheets. The private paper copy is
not redistributed here. This planning audit follows upstream's recorded paper
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
| S1 | [EffectiveCore](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Semantics/EffectiveCore.lean): `WellFormed`, `Supported`; [Admission](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Verification/Admission.lean): `coreChecks`, `supportChecks`, `certificate_exists`; [comparison audit](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/resolved-ir-comparison.md) | Exact M1 domain. [Bridge](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Semantics/Bridge.lean) and [Representation](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Verification/Representation.lean) supply selected structural results; no Alloy or frontend theorem. |
| S2 | [Syntax](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Syntax.lean): `Defaults`, `GroupCard.childDefault`, `AST.WellFormed`; [Compile contract](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/compile.md) | Resolved/defaulted input, distinct IDs/names, role and attachment identity. Positive-map support is an additional Compile precondition, not a universal source-language restriction. |
| S3 | [Inherited realization](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/inherited-realization.md), [Realization core](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Semantics/Realization.lean): `Core.Selected`, `View`, `Satisfies` | Selected explicit abstracts, ordinary fields, realization ranks, original links and Appendix 6 d01–d26/c01–c12; does not expand M1's finite checker. |
| S4 | [Typed core](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/Clafer/Constraints/Typing.lean): every `Expr`, `Arithmetic`, `SetOp` constructor; [denotation](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/constraint-denotation.md), [preservation](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/constraint-preservation.md) | Independent partial meanings, finite cardinality operands and exact integer singleton extraction. Mathematical integer realization is not Alloy's bounded Int. |
| S5 | Haskell [grammar](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/clafer.cf), [desugarer](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Desugarer.hs), [inheritance resolver](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/ResolverInheritance.hs) | Constructor/surface inventory and compatibility guide. The architecture's whitelist excludes behavior and wider static extensions. Defaults are selected from S2, with discrepancies retained. |
| S6 | Haskell [IR](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Intermediate/Intclafer.hs), [static Alloy generator](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Language/Clafer/Generator/Alloy.hs), [positive fixtures](https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c/test/positive), [regressions](https://github.com/gsdlab/clafer/tree/15adb2216909421bcb5022174d2d84ef2b42307c/test/regression) | Comparison evidence to reproduce in #6/#12. Same-generation JSON/Alloy receipt required by the upstream [import contract](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/resolved-import.md); equal filenames/hashes of source alone do not pair outputs. |
| S7 | [Official Alloy reference](https://alloytools.org/spec.html), especially Commands, Integer Expressions and signature/field semantics; [pinned A4Options](https://github.com/AlloyTools/org.alloytools.alloy/blob/794226dd07b536fe35c5ca44b529417183cd629b/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/translator/A4Options.java) | Independent target guide. Finite scopes, signed bitwidth and overflow behavior must be modeled explicitly. The live reference is not immutable; #8 records construct-by-construct correspondence and retained source identity against the pinned distribution. |
| S8 | [Bounded comparison](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/bounded-comparison.md), [complete telematics](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/telematics.md) | Exact-candidate/mutation policy and complete model inventory. Haskell Telematics fixtures differ from the printed model and cannot replace its twelve-body/final-selection inventory. |

## Discrepancies and reviewed upgrades

Keep accepted upstream corrections visible: link-preserving span composition;
common-target disjointness; parentless abstract heads without fabricated parents;
ordinary inherited fields versus explicit abstract types; and ordinary set
intersection. Preserve the documented empty-group and keyword/numeric-default
mismatches with Haskell. A discrepancy may be a compiler bug, a semantic defect,
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
compiler/Haskell comparisons become required when their owning tasks deliver them.
The [target core correspondence](alloy-core.md#source-correspondence-and-external-boundary)
records #8's reference snapshot identity, exact constructor mapping and independent
Lean/Analyzer observations. Its fixtures and Java adapter are original MIT-licensed
project code; no reference specification text or Haskell code is redistributed.
The general range analysis is tested, not claimed as a proved no-overflow theorem.

The current oracle check executes paired Haskell captures, upstream admission and
exact-candidate Lean/Alloy comparisons, alongside build/import/native/kernel/axiom
checks. Downstream compiler-generated Alloy remains owned by #12.

No branch name, floating latest release, SoSyM research tag or upstream maintenance
branch is a substitute for the commit pin or a prerequisite for compiler intake.
Repository/Project privacy, manual intake and publication approval remain unchanged.

The [Alloy text contract](alloy-text.md) maps #9's emitted grammar to S7's lexical,
namespace, precedence, declaration and command rules. It also uses S6's field
naming/ownership examples and S8's exact-candidate profile. Its parser, printer,
native tests, reference text and AST adapter are original project code. The
retained reference snapshot identity is unchanged; no upstream definitions or
Haskell source were copied. Parser reconstruction is a successful-render theorem;
Analyzer correspondence and total successful renderability are not kernel proofs.
