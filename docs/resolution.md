# Structural source resolution and defaults

Selected [issue #17](https://github.com/kbak/clafer-compiler-lean/issues/17) follows
accepted parser #16 (PR #30) and IR #7 (PR #25). The frontend resolves authored
structural declarations; source expression elaboration remains #18. The source
and its constraint occurrences must survive unchanged. Semantic acceptance of
this implementation remains pending.

## Reuse assessment and implementation plan

Before implementation, inspected the existing authored `Surface`/`Parser`,
`IR.Structural` lookup, checked finite edges, certificates and admission, and its
`SemanticsBridge.Structural` interpretation. Reuse those representations and the
native test/oracle harness. The pinned upstream `Clafer.Syntax.Defaults`,
`GroupCard.childDefault`, `AST.WellFormed`, `Compile` input contract and
`Realization.Core.Selected` supply independent meanings, but consume already
resolved data and provide no executable source resolver. Their noncomputable
traversals also do not meet the production import boundary.

Inspected pinned Haskell `ResolverInheritance.hs`, `ResolverName.hs`,
`Desugarer.hs` and `Intclafer.hs`. They supply comparison behavior, not a production
runtime or authority for changing the adopted default rules. In particular numeric
groups and `opt` have documented default differences. General Haskell expression
navigation, nested explicit abstracts and relocation exceed this source profile.

Lean 4.35.0 `List`, `Array`, `Vector`, `Option`, `Except`, finite decisions and
`Nat.repeat` provide traversal, lookup and iteration. Existing Std/Lean name
resolution is for Lean namespaces/macros, not Clafer's declaration scopes and
primitive origins; it cannot supply these language rules. No graph, parser or
symbol-table library is needed for the finite tables here. Reuse standard folds
and finite rank relaxation, avoiding custom general infrastructure. Existing MIT
project code and Apache-2.0 Lean dependencies suffice; no new package, license cost,
vendored meaning or Haskell source copy is introduced.

Implementation proceeds from source occurrence inventory, through identity/name
resolution, then defaults/ranks, a declarative translation validator and upstream
proof bridge. Native positive/negative and pinned importer comparisons accompany
it. Successful validation must prove source correspondence, not merely output
well-formedness. No total-success or runtime correctness theorem is implied.

## API and identity

`ClaferCompiler.Frontend.Resolution.elaborate` takes a `Document` and returns
`Except Diagnostic (Elaborated doc)`. `Elaborated` carries a finite `Candidate`
and a proof of `Elaboration doc candidate`. The candidate contains the existing
`Core`/`Certificate`, source paths, full effective `Group` values and realization
ranks. Runtime imports remain Std/project-only. The source document stays an
explicit argument; `constraints doc candidate owner` returns its original ordered
constraint occurrences and spans. It does not duplicate inherited constraints or
claim their bodies are resolved/typed. No source JSON or CLI interface is added.

Root ID/index 0 is `Sing`. User declarations receive IDs 1 onward in source
preorder. Paths are lists of zero-based *element* indices, so constraint positions
are retained. Optional canonical `int` is last and exists only when referenced;
`int` and `integer` resolve to the same primitive origin. IDs are stable for the
same syntax tree, including comments/CRLF variants, not persistent across edits.
Names and byte positions do not define identity. Reference cycles are allowed;
parent/super/realization ranks are independently checked.

The reserved user spellings are `Sing`, `root`, `this`, `parent`, `dref`, `int`,
`integer`, `string`, `real`, `double`, `bool` and `boolean`. Parser exclusions may
reject an excluded primitive earlier. User spelling never supplies primitive
origin. Ordinary fields under abstracts retain authored `false`, effective `true`,
the original parent and their own source identity; no fields are cloned.

## Declarative lookup and defaults

`Resolves` chooses a unique candidate of maximum lexical proximity. For reference
types, declarations in the reference declaration's body are nearest, followed by
the surrounding bodies from inner to outer; declarations outside those scopes
have global priority zero. More than one best candidate is ambiguous. For super
names and use shorthand, candidates are explicit parentless abstract declarations;
a local use cannot capture its own type name. Missing eligible candidates fail.
Duplicate names in one authored body fail even when never referenced. Repeated
names in different bodies retain distinct identities. This is the declared direct
`Name` type-position policy; expression navigation and inherited contextual name
lookup belong to #18. Haskell's general path-valued resolution and nested abstract
relocation do not expand the selected profile.

`SourceRow` equates resolved edges with these lookup rules and the original source
parent path. Top-level explicit abstracts are parentless; concrete top-levels
belong to `Sing`. Nested explicit abstract types, reference inheritance and
recursive realization dependencies are unsupported. `CoversChildren`, path
uniqueness and source preorder prevent dropping, inventing or merging declarations.
The independent inductive `Declared` relation and `source_coverage` theorem cover
every declaration at arbitrary finite nesting depth.

Groups preserve `bounds`, `xor`, `or`, `mux` and `opt`. Omitted groups inherit the
super's complete effective value, else numeric `0..*`. Omitted local bounds use
the parent's keyword/numeric default, else `1..1`. Explicit bounds override these.
Effective abstractness is authored abstractness or the parent's effective flag.
Parentless abstract local slots are recorded as specified by `Clafer.Defaults`,
without inventing any containment predicate.

`toM1` refuses every constraint occurrence, including empty brackets, and uses
existing exact M1 admission. Integer primitives and inherited ordinary fields are
therefore rejected by that conversion. It normalizes only parentless abstract
local slots to `0..*`, since there is no parent fiber; source effective/authored
records remain available in the original candidate. The admitted result preserves
all other fields and metadata. No v1 schema or backend guard changes.

## Proof and runtime boundary

The implementation constructs a candidate using standard worklist iteration and
finite rank/default relaxation, then decides the independently stated `Elaboration`
relation. This is translation validation. Successful return supplies source
correspondence; theorems do not assume successful name lookup, correct defaults,
source satisfaction or backend preservation as extra premises. Total successful
elaboration of every valid input, sufficient traversal fuel for manually built
ASTs, and native execution are not kernel-proved. Internal correspondence failure
is a failed compilation, never agreement or UNSAT.

`SemanticsBridge.Resolution` proves:

- `elaborate_correspondence`: successful results satisfy the independent relation.
- `sourceRow_of_path`, `sourceRow_of_user`, `source_coverage`: every source
  declaration is represented and follows the source rules.
- `resolves_unique`: the declared lookup rules cannot bind one occurrence to two identities.
- `group_range`, `group_default`, `defaults`: exact interpretation of provenance
  and the pinned `Clafer.Defaults` relation for every user declaration.
- `wellFormed`: actual upstream `EffectiveCore.WellFormed`, including primitive,
  inherited abstractness, hierarchy, identity and bounds obligations.
- `selected`: actual `Realization.Core.Selected`, using authored explicit flags
  and checked realization ranks.
- `m1_preserves`: successful conversion returns exactly the stated M1 projection.
- `m1_admitted`: explicit M1 projection success supplies the existing upstream
  well-formedness/support guarantees.

No whole `AST.WellFormed` theorem with typed constraint bodies, expression
elaboration, candidate satisfaction, backend preservation or grammar/parser
correspondence is claimed. #18/#20 own the remaining composed boundary. The
MCS `Compile.Input` positive-map-support requirement is not imposed on unresolved
literal-only source constraints.

## Diagnostics and validation

Resolver diagnostics use phase `resolve` and existing source schema/categories.
Declaration reserved-name/nested-abstract/duplicate checks precede edge lookup;
lookup runs in source order, super before reference. Then inheritance/rank/domain
checks and the independent source validator run. Missing/ambiguous names,
duplicates and inheritance cycles are malformed. Recognized excluded primitive
supers, references with inheritance, parentless abstract references, nested
abstracts and recursive realizations are unsupported. Ambiguity/duplicates include
related declaration spans in deterministic source order. Messages are not stable;
codes, original-byte locations and categories are.

Native tests cover the keyword/numeric default matrix, overrides and inherited
provenance; independent source mutations; references, shadowing, shorthand,
primitive aliases and constraints; deterministic byte diagnostics; and generated
containment/super chains of lengths 1–16. These finite properties use the existing
unittest/standard-library generation workflow and are not completeness proofs.
Wrong-target mutation remains structurally well-formed but fails source
correspondence, demonstrating why well-formedness alone is insufficient.

Pinned importer comparisons use original fixtures and same-generation captures.
Normalize preorder IDs, synthetic root representation and parentless abstract
local slots; compare names, parent/super/target identities, set/bag mode,
abstractness and effective bounds field by field. The importer admits only its
constraint-free M1 domain. Integer/inherited source tests are independent native
checks, not M2 importer agreement. Numeric-group and `opt` child-default
differences remain adopted semantic distinctions, not reference-driven changes.
Evidence and tool/source hashes remain outside the repository.

## Trace links

`impl~compiler-source-resolution~1`

[Defaults/relations](../ClaferCompiler/Frontend/Defaults.lean) and
[resolver](../ClaferCompiler/Frontend/Resolve.lean) implement source inventory,
lookup, structural admission, provenance and defaulting.

Covers:
- `req~compiler-resolution~1`
- `req~compiler-defaults~1`
- `req~compiler-diagnostics~1`

`proof~compiler-source-elaboration~1`

[Proof bridge](../ClaferCompiler/SemanticsBridge/Resolution.lean) establishes the
success/coverage, upstream defaults, well-formedness and selected-domain statements
listed above. [Native tests](../tests/ResolveNative.lean) and
[regressions](../tests/test_resolution.py) exercise the tested boundaries separately.

Covers:
- `req~compiler-resolution~1`
- `req~compiler-defaults~1`
