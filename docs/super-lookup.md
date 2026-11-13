# Behavioral super-name lookup

The [accepted lookup disposition](https://github.com/kbak/clafer-compiler-lean/pull/131)
defines the implemented plain/inherited/qualified rules below. The
[static resolution contract](resolution.md#declarative-lookup-and-defaults)
remains separate from the richer
[behavioral structural contract](behavioral-structure.md#source-identity-and-defaults).

The affected promises are resolution (`req~compiler-resolution~1`),
behavioral structure (`req~compiler-behavioral-structural-bridge~1`) and
behavioral syntax (`req~compiler-behavioral-frontend~1`). The contract extends behavioral super
syntax and lookup, preserving the static promise and the richer resolved domain.
It does not extend reference-type syntax or expression navigation.

## Evidence and observation boundary

The [small models](../tests/fixtures/super-lookup),
[native observer](../tests/SuperLookupNative.lean) and
[regression](../tests/test_super_lookup.py) exercise the actual static parser and
resolver and behavioral parser plus `bindDeclarations`. Successful rows identify
both ends of each super edge by their **authored declaration paths**. Rejected
models have no accepted declaration table. `058.json` records the selected outcomes, diagnostic categories and byte spans.
`current.json` retains the historical direct-name characterization; it is not
relabeled as a result of the new resolver. Its static lookup outcomes are unchanged.

The reference is Haskell
[`fca0deb9c766261f5c0d2ae57af4ba9b07e1279a`](https://github.com/gsdlab/clafer/tree/fca0deb9c766261f5c0d2ae57af4ba9b07e1279a),
using the qualified Stack/GHC build. The
[reference observer](../scripts/oracles/SuperLookup.hs) calls its unchanged
`parse`, `desugar`, `compile` and `getIr` APIs; optional generation forces the actual
output bytes. It does not invoke a solver. Fresh observations retain source,
build, observer and input identities externally. `reference.json` records the
reviewed frontend outcomes and authored super edges, separately from native
expectations. These are finite observations, not a proof of Haskell equivalence
or universal source/target equivalence.

The existing structural capture adapter rejects dotted type expressions in its
source audit. Its `unsupported` result is **adapter admission**, not Haskell
lookup failure. The direct observer is needed for this review. Generated Alloy
does not establish valid target syntax or satisfiability; the cyclic case below
demonstrates that distinction.

## Case and disposition matrix

Each row names a `.cfr` fixture. The fixture itself is the complete model; names
such as `P.Head` below identify authored declarations, independent of Haskell UIDs
or Lean numeric IDs. `Dotted` means historical behavioral parsing rejected the first
dot with unsupported `behavioral.type-expression`. Static parsing uses unsupported
`parser.type-expression` for the same forms. Static nested explicit abstracts
are unsupported even when behavioral lookup succeeds.

| Case | Historical behavioral result | Haskell reference result | Selected disposition |
| --- | --- | --- | --- |
| `forward` | `h → Head` | Same | Reuse forward lookup. |
| `plain-enclosing` | `Head.Inner.h → Head` | Same | Retain enclosing lexical visibility. |
| `plain-global` | `p.h → P.Head` | Same | Retain unique global fallback and refined-parent admission. |
| `plain-sibling` | `Bob.h → Bob.Head` | Same | Reuse own sibling precedence. |
| `redefinition` | Inheritance-cycle error: `Bob.Head` selects itself | `Bob.Head → Person.Head`; `Bob.h → Bob.Head` | Exclude the declaration being defined; find the inherited original, then let siblings see the new declaration. |
| `plain-inherited` | Ambiguous between `Person.Head` and `Dog.Head` | `Bob.h → Person.Head` | Search the parent's nearest inherited child before global fallback. |
| `plain-inherited-before-global` | `p.h → Head` (top-level) | `p.h → P.Head` | Inherited child precedes outer lexical candidates, including top-level names. This changes a successful current binding. |
| `plain-lexical` | `P.Inner.h → P.Head` | Same, through `Inner : P` | Preserve this valid composition. |
| `plain-outer-lexical` | Lookup selects `P.Head`, then structural admission fails | Ambiguous names | Preserve refined-parent rejection; lookup alone cannot authorize this table. |
| `plain-top-preference` | `h → Head` (top-level) | Ambiguous with `P.Head` | Preserve remaining lexical fallback; retain this explicit comparison boundary. |
| `plain-concrete-shadow` | `Owner.h → Owner.Head` | `Owner.h → Head` (top-level abstract) | Preserve concrete sibling lookup; do not filter candidates by Haskell abstractness. |
| `concrete` | `h → Base` | No abstract super found | Preserve concrete supers. Static resolution still rejects this model. |
| `concrete-child` | `p.h → P.Head` (ordinary child) | No abstract super found | Preserve ordinary nested supers and refined-parent admission. |
| `qualified-own` | Dotted | `Bob.h → Person.Head` | Admit the behavioral path. |
| `qualified-inherited`, `qualified-forward` | Dotted | `Bob.h → Person.Head` via `Bob.Head`, including forward declaration order | Admit inherited path steps without cloning `Head`. |
| `qualified-shadow` | Dotted | `Bob.Head → Person.Head`; `Bob.h → Bob.Head` | Own child wins over inherited child. |
| `qualified-nearest` | Dotted | `C.h → B.Head`, rather than `A.Head` | Choose the nearest super's child. |
| `qualified-long` | Dotted | `a.b → A.B`; `a.b.c → A.B.C` | Traverse every segment. |
| `qualified-enclosing` | Dotted | `Outer.P.h → Outer.P.Head`, despite top-level `P` | First segment prefers the nearest enclosing declaration. |
| `qualified-global` | Dotted | `o.p.h → Outer.P.Head` | Otherwise permit a unique global first segment. |
| `qualified-top-preference` | Dotted | `Bob.h → P.Head`, despite `Other.P` | Prefer a unique top-level first segment among multiple global matches. |
| `qualified-sibling-start` | Dotted | Ambiguous `Global.P` / `Owner.P` | Preserve the qualified rule: a sibling is not an enclosing declaration. |
| `qualified-chain`, `plain-after-qualified` | Dotted at `Family.Person` | `family.person → Family.Person`; its `h → Family.Person.Head` | Compose resolved inheritance with qualified and plain lookup. |
| `qualified-concrete` | Dotted | Final `P.Head` is not abstract | Admit the path in the richer behavioral domain, subject to structural admission. |
| `plain-parentless`, `qualified-parentless` | Structural admission failure / Dotted | `H → P.Head`, **moving `H` under `P`** | Preserve authored parent identity; reject an invalid parent relationship. Do not import relocation. |
| `plain-ambiguous` | Ambiguous-name error | Ambiguous `P.Head` / `Q.Head` | Reject tied candidates; retain all relevant declaration spans. |
| `plain-missing` | Missing-name error | Missing super | Preserve malformed missing-name failure. |
| `qualified-first-ambiguous` | Dotted | Ambiguous `A.P` / `B.P` | Reject the ambiguous first segment. |
| `qualified-first-missing`, `qualified-child-missing` | Dotted | Missing first declaration / missing child | Report the failing segment as malformed after path support is selected. |
| `duplicate`, `qualified-duplicate-child` | Duplicate-name error / Dotted | Duplicate declarations rejected | Reject duplicate authored siblings before choosing an edge. |
| `self`, `cycle` | Inheritance-cycle error | Rejected | Preserve cycle rejection. |
| `qualified-self` | Dotted | Self-inheritance rejected | Preserve self rejection for qualified syntax. |
| `qualified-cycle` | Dotted | Analyzed edges `P.A → P.B → P.A`; generation emits mutually extending signatures | Reject by the existing rank/admission obligation. Reference output is not an accepted cycle. |
| `primitive` | Unsupported primitive super | `h : integer` becomes an integer **reference**, with no super edge | Preserve the primitive-super exclusion; do not adopt this desugaring. |
| `expression-super` | Unsupported type expression | Parse error | Keep set/arithmetic expressions outside super syntax. |
| `qualified-reference` | Unsupported type expression | Reference path accepted | Keep qualified reference types outside this super-only amendment. |

## Lookup rules

These source rules preserve the accepted upstream resolved structural meaning.

1. **Plain behavioral super:** exclude the declaration being defined. Search its
   parent's own children, then children of the parent's supers from nearest to
   farthest, then the remaining authored lexical scopes from inner to outer,
   then unique global candidates. Choose one identity at the first nonempty
   priority; ties fail. Candidate eligibility includes concrete declarations.
   Keep primitive/reserved-name rejection. A self-only declaration fails, and
   mutually recursive choices fail the checked inheritance ranks.
2. **Qualified behavioral super:** accept only a nonempty dot-separated sequence
   of names. For its first segment choose the nearest enclosing declaration with
   that name; otherwise choose the sole global match, or the unique top-level
   match if several global declarations share it. Remaining ambiguity fails.
   For each later segment choose an own child, otherwise a child of the nearest
   super that declares that name. Do not search reference targets, descendants,
   arbitrary expressions or outer scopes for later segments.
3. **Identity and admission:** the result is the original declaration, not an
   inherited clone. Qualified self targets fail. Every edge still passes richer
   structural admission, including parent refinement, acyclicity, inherited
   reference compatibility and group/default provenance. No abstract-only target
   filter or authored-parent relocation is added. A spelling must not be silently
   dropped when a path fails.
4. **Static separation:** keep direct-name supers restricted to explicit
   parentless abstracts. Do not add path supers, nested explicit abstracts,
   concrete supers or reference-type paths to the static profile. Preserve its
   existing diagnostic categories and byte spans.

The intended change in `plain-inherited-before-global` is deliberate: an inherited
member of the containing type must win over an unrelated outer name, while an
own redefinition wins over that inherited member. Preserving lexical fallback
after this local/inherited search avoids removing already accepted behavioral
lookup where Haskell has a broader ambiguity check. Qualified first segments
have their own explicit rule; plain and qualified names are not interchangeable
search procedures.

## Source correspondence and proof boundary

`Header.super` retains plain names; `Header.superPath` retains qualified
`SuperPath` values with every segment token and the entire span. Exactly one
form is present. The behavioral parser alone constructs qualified paths;
references remain single-name. `Projects`, `BoundDeclarations`, `SourceRow` and
coverage retain this representation through declaration elaboration.

[`BehavioralLookup`](../ClaferCompiler/Frontend/BehavioralLookup.lean) uses a bounded
dependency traversal over inventoried authored paths. A parent super must be
resolved before inherited-child lookup; an unresolved dependency is never treated
as an absent edge. Active requests diagnose cycles, and exhausted traversal
reports `resolve.lookup-budget`. Successful results still pass the ordinary
rank, parent-refinement, reference and default checks.

[`BehavioralLookupRules`](../ClaferCompiler/Frontend/BehavioralLookupRules.lean)
defines `Plain`, `First`, `Child`, `Steps` and `Qualified` against the completed
table, independently of that traversal and its fuel. `Child` minimizes inherited
distance; `Plain` requires no local candidate before lexical fallback. `SuperRule`
checks those relations for each authored row. Successful `elaborate` returns
`Elaboration`; `sourceRow_of_user` and the existing resolution bridge expose
coverage and source correspondence alongside upstream structural validity.
`plain_unique` (assuming unique authored paths), `child_unique`, `steps_unique`
and `qualified_unique` prove target uniqueness within that table;
`plain_excludes_self` proves self exclusion. They do not prove Haskell equivalence,
parser correctness, universal termination or uniqueness between different tables.

The native matrix, declaration-order variants, CRLF/Unicode/comment variants and
segment/related spans exercise execution. Wrong-target mutations replace
`Bob.Head` with `Person.Head`, or a concrete sibling with an outer abstract;
structural checks still succeed while independent source correspondence fails.
Dropping an authored super also fails. Concrete-super successes remain beside
negative missing/ambiguous/path/cycle controls. Declaration coverage retains both
own and inherited declarations, their properties, ownership and defaults.

The accepted upstream
[initializer inheritance contract](https://github.com/kbak/clafer-semantics/blob/85875084ebc7b405bb57f0c4a4ee4f9042e5c758/docs/behavioral-initializers.md#production-transport-and-proof-domain)
consumes resolved declarations. Its `Structure`/`Bundle` obligations conjoin
while preserving each original environment, clock and complete declaration
scope. A redefinition must not replace the inherited obligation, recapture its
RHS under the new `Head`, or reclassify its clock. These are handoff obligations
for initializer adoption, not initializer execution evidence from these
declaration-only fixtures. The upstream contract explicitly delegates named
super lookup to this compiler review; no missing upstream semantic definition
has been identified that requires a separate semantic decision.

## Reuse assessment

The implementation reuses the current inventory, source paths, duplicate checks, finite rank checks,
behavioral admission and independent source/table validation. Existing
`BehavioralStructural.Analysis`, ancestor/owner proofs and behavioral expression
field lookup provide related machinery, but are consumers of already resolved
supers; they cannot be assumed to solve the bootstrap dependency. Lean/Std lists,
arrays and finite folds suffice for the selected traversal. Lean namespace
resolution and general graph packages do not supply Clafer's lookup policy. The
new bounded traversal fills that bootstrap gap; the independent table predicates
reuse `Fin`, `Nat.repeat`, lists and decidable finite quantification. Runtime
checks and proof-only upstream interpretation stay in their existing import layers.

The pinned upstream structural and initializer relations already provide the
resolved meaning. The Haskell resolver and its positive path fixture provide
comparison examples, not production code or semantic authority. The existing
native harness is reused. The small reference observer is required because the
maintained structural exporter intentionally excludes dotted types; it reuses
the qualified Haskell library without changing that admission gate. No production
runtime, library dependency, license pin or upstream semantic code is added.
