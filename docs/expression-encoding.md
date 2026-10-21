# Static constraint encoding

[Issue #15](https://github.com/kbak/clafer-compiler-lean/issues/15) is selected
after accepted #9, #10 and #14 (PRs #27, #28 and #32). The starting implementation
baseline is `b36a9b8478a2ad3e2310c768aac04943369d31ba`. This work extends the
independent Alloy target and consumes the [typed expression API](expressions.md).
Target arithmetic was merged through PR #34. The source range-proof continuation
is pending semantic review; the issue's source-to-target constructor and attachment
preservation obligations remain acceptance criteria.

## Delivered target arithmetic

`impl~compiler-target-integers~1`

`Integer.literal`, `count`, `add` and `subtract` build ordered postfix programs
in the existing [target syntax](../ClaferCompiler/Backend/Alloy/Syntax.lean).
`Integer.wellTyped` rejects stack underflow, surplus operands and invalid relation
leaves. This changes the raw `Integer` representation from a two-constructor
inductive to a `code` record; the original `literal`/`count` builder calls remain
available. Raw consumers must now inspect `IntegerOp` or use `Integer.fold`.

[Bounds](../ClaferCompiler/Backend/Alloy/Bounds.lean) computes intervals with
addition `[a.lower+b.lower,a.upper+b.upper]` and subtraction
`[a.lower-b.upper,a.upper-b.lower]`. Literals, counts and every intermediate must
fit the requested signed width. Failure propagates to target bounds admission;
neither final-value cancellation nor a false implication antecedent hides it.
The independent [evaluator](../ClaferCompiler/Backend/Alloy/Semantics.lean)
performs the same representability check at every executed arithmetic operation,
preserving `none` separately from a defined false comparison. Empty quantifier
domains still evaluate no bodies; conservative admission still checks their code.

Covers:
- `req~compiler-target-arithmetic~1`

## Proved arithmetic boundary

`proof~compiler-target-integers~1`

[IntegerArithmetic](../ClaferCompiler/Correctness/IntegerArithmetic.lean) proves:

| Theorem | Established boundary |
| --- | --- |
| `Integer.eval_add`, `eval_subtract` | Exact ordered, strict bounded evaluation equations |
| `Integer.add_defined_iff`, `subtract_defined_iff` | Defined result iff both operands are defined and the mathematical result fits |
| `IntRange.representable`, `add_contains`, `subtract_contains` | Checked interval membership implies representability; arithmetic preserves calculated intervals |
| `Integer.range_sound` | A successful analysis evaluates to the mathematical result inside its returned interval, under `Integer.Term` and explicit `CountsFit` leaf capacities |

`Integer.Term` only establishes stack construction. `CountsFit` states for each
actual counted relation that its distinct tuple count is at most the product of
its independently computed column budgets. It contains no source or target truth
assumption. Deriving those premises generally from arbitrary relation typing and
instance admission is still unfinished. The mathematical evaluator in this proof
is target arithmetic, not the independent upstream source denotation; no
source-to-target theorem is claimed from that equality.

Covers:
- `req~compiler-target-arithmetic~1`

## Source range-analysis proofs

`proof~compiler-source-ranges~1`

[Observation bounds](../ClaferCompiler/Correctness/ExprObservationBounds.lean)
derive finite recorded membership, distinct-object budgets, observed integer
intervals and map endpoints from the executable `Observation.withinBounds` check.
`recorded_result` proves that every admitted collection stays within these finite
observations, including identity/inclusion widening, relational image/join and
lexical variables. Equal-ID observations and original inclusion links supply the
widening argument; membership in the infinite primitive class alone is insufficient.

[Range soundness](../ClaferCompiler/Correctness/ExprRanges.lean) proves
`analyzeAt_sound` for the existing executable analyzer and every typed constructor.
`admitted_sound` exposes its result: numbers that are defined lie in the returned
representable interval; collections are total finite sets whose distinct cardinality
is at most the returned budget. No expression truth or definedness premise is used
to obtain these guarantees. Undefined singleton extraction remains undefined.

[Intermediate ranges](../ClaferCompiler/Correctness/ExprIntermediateRanges.lean)
proves `admitted_all_numbers_fit`, including numeric operands under both Boolean
branches and bodies at every actual quantified object. Empty domains have no body
evaluations, while admission still checks their body syntax. `bounded_environment_sound`
derives the observation and lexical premises directly from `Environment.bounded`.
All results retain the independent `ObservationValid` binding obligations, which
describe identities, links and inclusion maps and contain no constraint truth.

`admitted_extension_sound` composes the established finite-observation bridge to
preserve the returned estimate in every full mathematical integer extension.
`admitted_integer_target` shows that a defined admitted source integer is accepted
unchanged by the target's `boundedInt`. This scalar representability lemma is not
source-to-Alloy expression correspondence. `AllNumbersFit` is stated over the
canonical full-integer extension; it is a property of the upstream denotation,
not another evaluator. Structural primitive/root composition remains separate.

Covers:
- `req~compiler-arithmetic~1`

`utest~compiler-source-ranges~1`

[Kernel witnesses](../tests/ExprRanges.lean) instantiate the analyzer theorems on
navigation/extraction, ordered subtraction, a binary join count and a quantified
primitive variable with a false Boolean sibling. They retain undefined extraction,
reject unrecorded external integers and reject intermediate overflow despite final
cancellation. [Native interval tests](../tests/ExprNative.lean) enumerate every
mathematical input value for 360 interval/operator/width combinations, independently
of the analyzer's endpoint formulas. The existing [runner](../tests/test_expressions.py)
executes these alongside the earlier 882 literal-boundary combinations. These
tests and theorems establish source range safety, not emitted expression facts.

Covers:
- `req~compiler-arithmetic~1`

## Serialization and target validation

`utest~compiler-target-integers~1`

The existing successful-render reconstruction theorem covers the extended parser
and printer. The canonical grammar adds `( plus [ a , b ] )` and
`( minus [ a , b ] )`, with integer operands and complete parentheses. It uses
the built-ins named in the official reference and the active Haskell generator
branches. Actual Analyzer parsing and native execution remain external evidence.

[Kernel witnesses](../tests/IntegerArithmetic.lean) exercise ordered subtraction,
signed endpoints, intermediate overflow, strict implication and empty-domain
vacuity. [Native checks](../tests/IntegerArithmeticNative.lean) cover 2,372
addition/subtraction boundary combinations across widths 1–16, malformed programs,
unsafe counts and hidden overflow, and serialize 20 deterministic target modules.
The [external runner](../tests/test_integer_arithmetic.py) compares independently
authored Analyzer ASTs, actual meanings and five valid-syntax mutations for swapped
operands, regrouping and binder capture. Cardinality candidates use exact scopes
and a complete-relation fact where needed. The adapter reuses the existing parser,
normalizer, SAT4J setup and evidence retention; only recognized integer built-in
calls extend the AST normalizer.

At width 16, the pinned Analyzer parses and normalizes the two endpoint fixtures
but reports `Translation capacity exceeded` for a universe with 65,536 atoms and
binary relations. The runner retains this exact result as `toolError`, separately
from the 18 successfully solved fixtures. It neither counts the tool error as
semantic agreement nor converts it to UNSAT. An unexpected failure or a change
to this known outcome fails the regression. Native width-16 admission/evaluation
is tested; successful external solving at that width is not established.

Covers:
- `req~compiler-target-arithmetic~1`
- `req~compiler-alloy-text~1`

## Remaining work

Issue #15 remains In Progress. The following obligations are unchanged:

- Encode every accepted source constructor, including singleton integer
  extraction, primitive observations, owner/navigation bindings and lexical scope.
- Generate separate definedness and value/truth, with explicit interval/domain
  enforcement and inherited-context restrictions for every attachment occurrence.
- Prove source-to-target constructor correspondence and the all-attachments theorem
  against the independent upstream denotation. Compose the source range proofs
  with concrete target representation and generated enforcement without assuming
  final truth.
- Extend target representation, serialization and actual Analyzer checks for
  integer-valued relations and source-context/definedness mutations.

No source constructor is newly admitted or rejected by this target-only stage.
M1 admission, dependency pins, the trusted scope and its deadline are unchanged.

## Reuse assessment

The source range-proof continuation starts from accepted main at
`92b21bd7b5ac9e47a39a4fa71428bc8338773e52` (the original checkout was
`81e57ccb770643252165dd99ac28b318650e7973`). It reuses `ExprBounds.analyzeAt`,
`Observation.withinBounds`, the existing interpretation and finite-observation
bridge. The pinned upstream `CollectionMeaning` proves membership in full class
domains, but that is insufficient for bounded primitive observations: its integer
domain contains all mathematical integers. The downstream proof must additionally
track membership in the recorded finite observations, including after identity
and inclusion widening and lexical binding. This is a compiler budget obligation,
not a change to the upstream denotation.

Mathlib's existing `Set.ncard_le_ncard`, `ncard_union_le`, `ncard_image_le` and
`ncard_prod`, plus the existing structural proof's generic `eraseDups_nodup`,
supply the collection counting machinery. Lean's existing finite
lists, vectors and recursors remain the executable implementation. The pinned
Haskell `genOp` arithmetic branches were checked as the supplementary operand-order
reference; they supply no proof of the adopted conservative source policy.
No new evaluator, container library, solver, package or copied source is needed.
The new proof modules remain outside the native import closure and add no
dependency or license cost.

The accepted target already provides postfix relation/formula algebras, checked
syntax and bounds, finite set-of-tuples evaluation, hygienic names and a checked
serializer using Lean's standard Parsec. Extend these APIs rather than introduce
a second Alloy language or parser. The existing correctness stack lemmas provide
the construction-witness pattern for new integer operators. Lean Std folds,
lists and arbitrary-precision `Int` provide the runtime machinery; Mathlib interval
and order reasoning stays in proof modules. These choices add no dependency or
license cost and preserve the native/proof import boundary.

The pinned upstream `Constraints/Denotation.lean`, `Integer.lean`,
`DenotationInvariance.lean` and the existing expression bridge supply independent
partial mathematical meaning. They cannot be imported into native target code.
The source range proof now connects that existing analyzer to the independent
denotation; it does not introduce a source evaluator or target encoding.

The retained official Alloy reference's Integer Expressions section and pinned
Haskell `Generator/Alloy.hs` `genOp` distinguish integer addition/subtraction from
relational union/difference. Emit Alloy's `plus`/`minus` operators, preserving operand
order. Reuse the pinned Analyzer and current Java oracle adapters to inspect and
execute generated text; they are external tests, not kernel proofs. No upstream
source or specification text is copied, and no dependency pin changes.

## Required boundaries

Integer evaluation must check every intermediate against the signed bitwidth.
Unsafe expressions remain unsupported even in a vacuous implication or an empty
quantifier body. Undefined source extraction requires separate generated
definedness and truth, including under negation and universal quantification.
Attachment IDs and occurrences, owner context, inherited restrictions and lexical
positions must survive translation. Primitive observation and structural
integration must retain the explicit boundaries in the architecture contract.
