# Super-name lookup review candidate

This is the candidate disposition for the
[lookup review](https://github.com/kbak/clafer-compiler-lean/issues/129).
Independent acceptance is pending. The
[compatibility task](https://github.com/kbak/clafer-compiler-lean/issues/128)
owns production changes after acceptance and selection. Current behavior remains
the [static resolution contract](resolution.md#declarative-lookup-and-defaults)
and [behavioral structural contract](behavioral-structure.md#source-identity-and-defaults).
No parser, resolver, semantic dependency or comparison-tool pin changes here.

The affected promises are resolution (`req~compiler-resolution~1`),
behavioral structure (`req~compiler-behavioral-structural-bridge~1`) and
behavioral syntax (`req~compiler-behavioral-frontend~1`). The candidate extends behavioral super
syntax and lookup, preserving the static promise and the richer resolved domain.
It does not extend reference-type syntax or expression navigation.

## Evidence and observation boundary

The [small models](../tests/fixtures/super-lookup),
[native observer](../tests/SuperLookupNative.lean) and
[regression](../tests/test_super_lookup.py) exercise the actual static parser and
resolver and behavioral parser plus `bindDeclarations`. Successful rows identify
both ends of each super edge by their **authored declaration paths**. Rejected
models have no accepted declaration table. `current.json` records current outcomes,
including diagnostic categories and byte spans; its refusals are characterization
tests, not the desired outcomes of the compatibility change.

The reference is Haskell
[`fca0deb9c766261f5c0d2ae57af4ba9b07e1279a`](https://github.com/gsdlab/clafer/tree/fca0deb9c766261f5c0d2ae57af4ba9b07e1279a),
using the qualified Stack/GHC build. The
[reference observer](../scripts/oracles/SuperLookup.hs) calls its unchanged
`parse`, `desugar`, `compile` and `getIr` APIs; optional generation forces the actual
output bytes. It does not invoke a solver. Fresh observations retain source,
build, observer and input identities externally. `reference.json` records the
reviewed frontend outcomes and authored super edges, separately from native
expectations. These are finite observations, not a proof of Haskell equivalence
or a newly adopted oracle profile.

The existing structural capture adapter rejects dotted type expressions in its
source audit. Its `unsupported` result is **adapter admission**, not Haskell
lookup failure. The direct observer is needed for this review. Generated Alloy
does not establish valid target syntax or satisfiability; the cyclic case below
demonstrates that distinction.

## Case and disposition matrix

Each row names a `.cfr` fixture. The fixture itself is the complete model; names
such as `P.Head` below identify authored declarations, independent of Haskell UIDs
or Lean numeric IDs. `Dotted` means current behavioral parsing rejects the first
dot with unsupported `behavioral.type-expression`. Static parsing uses unsupported
`parser.type-expression` for the same forms. Static nested explicit abstracts
are unsupported even when behavioral lookup succeeds.

| Case | Current behavioral result | Haskell reference result | Candidate disposition |
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

## Candidate lookup rules

These rules require review before adoption. They do not redefine upstream
structural meaning.

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

## Correspondence and implementation obligations

`Header.super` currently stores `Option Name`, and both parsers share the
single-name `typeName` helper. Add a behavioral representation that retains each
segment and the whole authored span without broadening reference positions or
the static grammar. Projection through `Projects`, `BoundDeclarations` and
declaration coverage must preserve that path instead of flattening it into an
opaque name or silently truncating it. Name canonicalization must not change
source identity or diagnostic offsets.

`lookupName` and `Resolves` currently implement the same finite lexical/global
ranking, and behavioral `SuperRule` invokes `Resolves` with the broader user
domain. Their existing proofs therefore do **not** establish the candidate
inherited/path policy. State independent declarative plain lookup and path-step
relations, uniqueness, exclusion of self and priority rules. Prove successful
resolution corresponds to those relations, then carry them through `SourceRow`,
`Elaboration`, source coverage and the behavioral semantics bridge. Reuse the
static relation and proofs unchanged where applicable.

Inherited lookup depends on super edges while those edges are being resolved.
Use checked resolution state or a bounded dependency traversal that reports
cycles, ambiguity, missing names and exhaustion separately. Never treat an
unresolved parent super as an absent edge. Establish order-independent resolved
identities for the admitted domain, including forward declarations and inherited
paths after qualified supers. A termination bound or successful structural
admission alone is not a name-correspondence proof.

Distinguishing correspondence witnesses must show that replacing `Bob.Head`
with `Person.Head` can preserve structural well-formedness while violating
the selected lookup, and that binding a concrete sibling to an outer abstract
violates the richer source rule. Retain both own and inherited declarations,
their distinct properties, original attachment owners, references and defaults.
Test wrong-target and dropped-path mutations against the independent relation;
preserve successful concrete-super controls alongside negative cases.

Malformed paths need stable segment-level spans, ambiguity-related locations,
self/cycle diagnostics and no successful partial table. Unsupported reference
paths, primitive supers and general type expressions remain distinguishable from
missing names. Repeat whitespace/comment, Unicode/CRLF and declaration-order
tests, then the existing static and behavioral regressions. Grammar recognition
and native execution remain tested boundaries, distinct from kernel proofs.

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

Reuse the current inventory, source paths, duplicate checks, finite rank checks,
behavioral admission and independent source/table validation. Existing
`BehavioralStructural.Analysis`, ancestor/owner proofs and behavioral expression
field lookup provide related machinery, but are consumers of already resolved
supers; they cannot be assumed to solve the bootstrap dependency. Lean/Std lists,
arrays and finite folds suffice for the selected traversal. Lean namespace
resolution and general graph packages do not supply Clafer's lookup policy.

The pinned upstream structural and initializer relations already provide the
resolved meaning. The Haskell resolver and its positive path fixture provide
comparison examples, not production code or semantic authority. The existing
native harness is reused. The small reference observer is required because the
maintained structural exporter intentionally excludes dotted types; it reuses
the qualified Haskell library without changing that admission gate. No production
runtime, library dependency, license pin or upstream semantic code is added.
