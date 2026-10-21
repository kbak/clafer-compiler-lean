# Independent static Alloy core

[Issue #8](https://github.com/kbak/clafer-compiler-lean/issues/8) supplies the target
API for #9 and #10 after accepted oracle task #6. This implementation was accepted
through PR #26. The selected [text task #9](alloy-text.md) now supplies a serializer
and independent parser; there is no source encoder, decoder or compiler preservation
theorem. The existing native CLI still only supports `--version`.

## API and supported fragment

`impl~compiler-alloy-target~1`

All declarations below live in `ClaferCompiler.Backend.Alloy`:

- [Syntax](../ClaferCompiler/Backend/Alloy/Syntax.lean): `Schema`, `Signature`,
  `Field`, `Rel`, `Integer`, `Formula`, `Scope`, `Command`, `Module` and their checks.
- [Bounds](../ClaferCompiler/Backend/Alloy/Bounds.lean): `check`, `CheckedModule`,
  `Module.safeBounds`, `Rel.columns`, `fitsInt` and `boundedInt`.
- [Semantics](../ClaferCompiler/Backend/Alloy/Semantics.lean): `Instance`,
  `Rel.eval`, `Integer.eval`, `Formula.eval`, `Module.eval`, `Satisfies`, `evaluate`.

The syntax is **extrinsically typed**. Raw constructors are untrusted; `check`
returns a module carrying proofs that its arity/binding and bound checks passed.
`Rel.typeOf` checks unary/binary shape and signature/field IDs. All binders are
unary object binders, with de Bruijn index zero denoting the nearest binder.
Domains are checked in the outer context, bodies in a context extended by one.
There are no names or implicit receiver bindings in the core.
The [text API](alloy-text.md) supplies names and surface syntax.

`Rel` and `Formula` store finite postfix instruction lists, with public builders
such as `Rel.join left right` and `Formula.all domain body`. The first operand is
emitted before the second; stack operations pop right then left. Each fold must
finish with exactly one value, rejecting operand underflow and surplus results.
Formula folds build functions of the lexical environment, so a quantifier binds
its body when that function is applied, not while the instruction list is scanned.
This representation uses standard-library folds and avoids generated recursive
project helpers prohibited by the build contract. It has no fuel cutoff.

The signature and field tables establish separate positional namespaces.
Signature parents must precede their children, providing a terminating forest
without a cycle certificate. No subset signatures are admitted. Fields have an
explicit owner, target and range multiplicity; signatures also have explicit
multiplicity. Facts and command bodies are closed formulas. The supported terms
are unary/binary empty relations, signature/field/variable references, union,
intersection, difference, unary product, unary/binary join and transpose; bounded
integer literals and relation counts; relational equality/inclusion, multiplicity,
integer equality/order, Boolean connectives and singleton `all`/`exists`.

Unary-unary join, nonbinary transpose, mixed-arity operations, dangling IDs,
unbound variables and invalid field endpoints are rejected. This check does not
implement the Analyzer's additional disjoint-type/redundancy diagnostics or its
name resolver. #9 must establish printable forms and exercise the actual parser;
arity-correct raw terms alone do not promise acceptance of every surface form.
No temporal operators, general integer arithmetic, higher-arity relations,
closure, comprehension, subset signatures, modules, functions or predicate calls
are part of this target fragment. M1 obligations can use quantifiers and facts;
richer integer operations remain with #15.

Covers:
- `req~compiler-alloy-core~1`
- `req~compiler-bounds~1`

## Finite instances and representation obligations

An instance supplies one finite extent per signature and one tuple set per field.
Natural numbers identify user atoms only. Their numeric values have no arithmetic
meaning, need not be consecutive and never determine an integer value. Reusing
an ID means the same atom, including in ancestor and descendant extents. The
validator rejects duplicate entries, duplicate tuples, malformed tuple lengths
and missing/extra tables. Set operations and joins deduplicate their outputs.

There is no explicit allocation pool. IDs absent from every extent and field are
unobservable spare slots. A field containing an atom outside its declared endpoints
is a well-formed negative candidate, rejected by declaration satisfaction.
Signatures must obey parent inclusion, top-level/sibling disjointness,
multiplicity and abstract coverage. Abstract coverage is imposed only when there
is at least one extending signature. An unextended Alloy abstract signature can
be nonempty; #10 must emit an explicit emptiness fact when Clafer demands it.

A binary field tuple is **owner first, target second**. Field multiplicity is
checked separately for each owner, including owners with no tuples. `set` places
no lower or upper fiber restriction; `lone`, `one` and `some` do. In particular,
`one` does not imply injectivity across owners. Two reference-head atoms can
therefore point to one target without losing occurrence identity. Counts of
heads, field tuples and dereferenced targets remain different expressions.

Built-in integer atoms are outside the user carrier. Conceptually the full
Analyzer universe also includes the signed integer range, tagged separately from
user atoms; this fragment cannot navigate or quantify over it. `univ`, `iden`,
integer-valued fields and primitive extents are deliberately unavailable. There
are no string literals or sequence constructs; the external test profile uses
empty `String` and `seq/Int`. Solver Skolem relations witness quantifiers and
introduce no new user objects. Any future user auxiliary signature must be an
ordinary declared/scoped signature, with its role specified by #10 and decoder #12.

The target enforces only its declared constraints. Root uniqueness, total
ownership, reference functionality, set-reference uniqueness, empty abstract
cover, local intervals and child-union group intervals must be represented by
the declarations/facts generated in #10. This API neither assumes nor proves
those source representation obligations. #11 must derive them from target
satisfaction and give concrete encode/decode relations.

## Bounds, integers and outcomes

Commands contain one explicit exact or upper scope per signature and a signed
bitwidth in 1–16, matching the accepted oracle profile. No bound is inferred.
The signature-multiplicity restrictions of pinned Alloy also apply: `one`
requires scope 1, `lone` permits at most 1 and `some` requires at least 1.
To express a source-requested bound conflicting with a declaration keyword,
#10/#9 can use a `set` signature plus an explicit multiplicity fact. For example,
exact scope zero plus `one A` as a fact is a valid unsatisfiable target; it must
not turn a valid source request into an unsupported source model. There is no
silent scope adjustment here. Incompatible parent/child sizes that are otherwise
valid scopes are left to satisfaction, not rejected as syntax.

For width `b`, integers fit `[-2^(b-1), 2^(b-1)-1]`. `boundedInt` returns `none`
outside that interval. Cardinality counts distinct tuples and goes through this
check; it never exposes unrestricted natural cardinality as an Alloy integer.
Multiplicity predicates use tuple existence/uniqueness directly and do not
introduce an Alloy `#` operation. Command scope numerals are allocation budgets,
not integer expressions. Infinity is represented by omitting an upper-bound fact,
not by an integer literal.

`Rel.columns` conservatively bounds each output column using explicit endpoint
budgets: signatures use their scope, fields their owner/target scopes, variables
one, unions sum, intersections take the minimum, differences retain the left
budget, products concatenate, joins remove matching columns and transpose
reverses columns. The product of the resulting budgets bounds tuple count.
`Formula.safe` checks every literal and counted operand in all facts and the
command, including both branches, negation and bodies of empty-domain quantifiers.
The analysis does not use facts or successful candidate satisfaction to narrow a
range. It can reject a safe individual instance; e.g. a possible unary count of
8 needs width 5 even if a fact restricts that particular set to fewer elements.
Repeated unions can overestimate and require a larger width. Increasing the
width or explicitly reducing scopes can resolve such rejection.

Boolean evaluation propagates undefined integers strictly. A quantifier evaluates
its domain first and evaluates its body only for actual members. The empty
universal is true; the empty existential is false. With admitted ranges and
declaration/scope-conforming instances the intent is that all integer observations
fit. The general column-bound/no-overflow induction is not a delivered theorem;
the analysis is implemented and tested. Runtime range checks remain mandatory and
report an explicit error if an unrepresentable observation occurs.

`check` distinguishes `malformedSyntax` and `unsupportedBounds`. `evaluate`
distinguishes `malformedInstance`, `unrepresentableInteger` and a Boolean result.
False is violation by this candidate, not a claim of bounded UNSAT. `Satisfies`
conjoins independently defined syntax, bounds, finite table, declaration, scope
and compositional formula conditions. A `run` seeks its body; a `check` seeks a
counterexample to its body while retaining all facts and declarations. Neither
operation in Lean searches all possible instances.

## Source correspondence and external boundary

The [official reference](https://alloytools.org/spec.html) was retained externally
on 2026-10-20 (America/Phoenix), SHA-256
`7cc1e10f30f3b879545b1a7c464032add5d0cb6f084e3bb25664d590f2946231`.
This records the inspected live document, not an immutable language edition.
The [pinned Alloy 6.2.0 distribution](sources.md) is tested separately.

| Reference heading | Target correspondence |
| --- | --- |
| Signature Declarations; Subtypes | `Signature`, `Schema.wellFormed`, `Instance.declarations`: forest, inclusion, disjointness, abstract coverage |
| Field Declarations; Multiplicity Keywords | `Field`, `Multiplicity.holds`: binary owner/target tuples and owner fibers |
| Relational Expressions | `Rel.eval`: extensional tuple operations; empty binary relation denotes `none -> none` |
| Integer Expressions | `Integer.eval`, `boundedInt`: literals and checked tuple cardinalities |
| Boolean Expressions; Quantification | `Formula.eval`: comparisons, connectives, singleton binding; truth/falsity are internal sugar for `no none`/`some none` |
| Commands; Semantic Basis | `Module.eval`, `Satisfies`, `Instance.inScope`: facts, declarations, polarity and explicit finite bounds |

The pinned Haskell generator's `claferDecl`, `genRelations`, `genParentConst`,
`genGroupConst` and `mkCard` were inspected as compatibility context (S6). They
motivate field, quantifier and count coverage but do not define target truth.
The pinned upstream [bounded comparison contract](https://github.com/kbak/clafer-semantics/blob/1454e3bd2ce9697923cdcef3863c816651ffc147/docs/bounded-comparison.md)
supplies the external profile and documents declaration-scope restrictions.
Existing Haskell/default discrepancies remain unchanged. No third-party source
is copied into the target modules or new fixtures.

## Proofs, tests and dependent-task handoff

`proof~compiler-alloy-model-laws~1`

`boundedInt_some_iff` proves the range guard for returning the requested integer.
`evaluate_iff_satisfies` proves equivalence between successful candidate evaluation
and the independent target predicate for a checked module. `Rel.fold_join`,
`Formula.fold_neg` and `Formula.fold_all` prove constructor equations given the
operands' stack results. `eval_neg_truth`, `eval_all_empty` and `eval_exists_empty`
give truth/empty-domain laws for arbitrary instances and environments. These are kernel proofs about this model,
not proofs of Alloy's translator, SAT4J or source compilation.

Covers:
- `req~compiler-alloy-core~1`
- `req~compiler-bounds~1`

## Kernel and Analyzer observations

`utest~compiler-alloy-kernel~1`

[AlloyCore](../tests/AlloyCore.lean) kernel-reduces a named truth table and rejects
malformed syntax/tables, unsafe counts, out-of-range literals and incomplete
scopes. [The live regression](../tests/test_alloy_core.py) compares the actual
Lean observations with independently authored [Alloy cases](../tests/fixtures/alloy-core/cases.json)
through [AlloyCoreBridge](../scripts/oracles/AlloyCoreBridge.java). The positive
relational cases pin the candidate up to atom renaming; negative declaration
cases ask for the violating memberships/tuples and must be unsatisfiable.
This is finite integration evidence, not a text round-trip proof or exhaustive
semantic equivalence result. #9 owns serialization correspondence.

Covers:
- `req~compiler-alloy-core~1`
- `req~compiler-bounds~1`

## Retained evidence and review

The mandatory check retains copied inputs, exact commands, source/tool hashes,
Java build/vendor, effective solver options, parsed command/formula, outcomes
and SAT XML under the external `CLAFER_ORACLE_EVIDENCE` directory. Replaying the
recorded `javac-command.json` and `analyzer-command.json` in that bundle reproduces
the Analyzer checks while the recorded tool paths remain available. Lean replay
requires the source-matched checkout and prepared pinned dependencies. A failed
process, timeout or absent tool fails the gate; none becomes a Boolean observation.
The full existing oracle suite still exercises Haskell and upstream Lean.

Acceptance of #8 through PR #26 covers the reference mapping, conservative analysis
and finite observations. Later changes still require their own review. IntentBond
exit 4 leaves that review pending; no scope or coverage policy changes are part
of this task.
