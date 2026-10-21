# Static constraint encoding

[Issue #15](https://github.com/kbak/clafer-compiler-lean/issues/15) is selected
after accepted #9, #10 and #14 (PRs #27, #28 and #32). The starting implementation
baseline is `b36a9b8478a2ad3e2310c768aac04943369d31ba`. This work extends the
independent Alloy target and consumes the [typed expression API](expressions.md).
Target arithmetic and source range proofs were accepted through PRs #34 and #38.
The constraint-translation continuation starts at accepted main
`9ef2d6a6bc9a047cb0985033960aa4c92e2c2cb2` and was accepted through PR #41. It supplies
constructor and attachment preservation under the explicit conditions below.
Source CLI integration #20 is accepted through PR #44; see [composed assurance](pipeline.md).

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

## Source constraint translation

`impl~compiler-source-constraints~1`

[Expressions](../ClaferCompiler/Backend/Alloy/Expressions.lean) compiles every
accepted typed constructor to a `Code`: a definedness formula and a Boolean,
integer or relation value. Lexical variables use their original positions;
`this` occupies the position outside all lexical binders. Operations preserve
ordered operands and explicit widening. Universal definedness requires every
actual domain member's body to be defined; an empty domain is vacuously defined.
Conservative admission still checks every syntactic branch and body for overflow.

Observed integer objects retain their original identity. `Signature.scalar`
adds a `one Int` auxiliary field, named from the existing disjoint hygienic
namespace. `Instance.values` supplies finite object/value rows. Scalar field
admission checks totality, owner typing, unique keys and signed representability.
Generated facts enforce the declared interval and injectivity of numeric values.
`Rel.diagonal` emits restricted `iden` for original inclusion links.

`Integer.scalar` emits a checked conditional using `one`, field join and `sum`.
Its internal fallback is the admitted interval's lower endpoint, so internal
value computation remains bounded even when source extraction is undefined.
That fallback is never asserted as an undefined source value: generated
singleton/domain definedness is separate and is conjoined with attachment truth.
Negation cannot turn undefined extraction into a satisfied constraint. The
independent parser reconstructs the expanded conditional only when all repeated
owner, relation and interval components agree.

[ExpressionAttachments](../ClaferCompiler/Backend/Alloy/ExpressionAttachments.lean)
checks support class IDs, primitive flags and context against admitted inherited
IR. Original map owner IDs and endpoint roles select head, parent, dereference,
target and inclusion relations; display names do not select maps. Each `Body`
retains its identity, owner, optional span and term, including repeated entries.
`compile` appends numeric enforcement and every encoded body to inherited
structural facts, then runs target admission. Explicit scopes and intervals feed
the existing source admission; no scope inference or language extension is added.

Covers:
- `req~compiler-expression-encoding~1`

## Constructor and attachment proofs

`proof~compiler-source-constraints~1`

The proof modules retain the pinned independent partial denotation. There is no
second source evaluator and no source-semantic import in the runtime encoder.

| Theorem | Established boundary |
| --- | --- |
| `encodeAt_agrees`, `admitted_agrees` | Every typed constructor preserves definedness and every defined value/truth; source admission supplies intermediate representability |
| `admitted_full_agrees` | The same correspondence for every full mathematical integer extension of the recorded observation |
| `attachment_iff`, `encoded_body_iff` | Generated owner quantification holds exactly when the original body is defined and true at every recorded owner |
| `occurrences_preserved` | The compiled original-body list equals the entire input list, including repeats, order, owners and spans |
| `all_attachments_iff`, `satisfied_attachments` | All emitted body facts characterize all original body meanings; satisfying the compiled module enforces them |
| `scalar_field_rows`, `scalarFacts_enforce`, `compiled_scalar_enforcement` | Field admission and actual generated facts enforce total/functional typed rows, declared numeric intervals and unique integer identity |

[ExpressionPreservation](../ClaferCompiler/Correctness/ExpressionPreservation.lean)
uses `ObservationValid`, the executable `Observation.withinBounds` check,
recorded lexical environments, and `LayoutRep`. The latter states injective atom
coding and concrete equality of target extent/map/scalar rows with the recorded
objects, original links and mathematical integer values. It contains no source
truth, extraction-success, expression-preservation or target-truth premise.
Construction witnesses establish postfix stack shape; they contain no semantics.

[ExpressionAttachments](../ClaferCompiler/Correctness/ExpressionAttachments.lean)
binds these conditions to actual compilation, preserving the original typed term.
Its `Realization` records the checked observation, concrete leaf equations and
full-integer extension separately for each occurrence. The all-attachments result
is an equivalence for the generated body facts; structural and numeric facts
remain additional conjuncts. `satisfied_attachments` obtains body truth from
membership in the emitted fact list. [Scalar enforcement](../ClaferCompiler/Correctness/ExpressionScalarFacts.lean)
obtains interval/injectivity facts from the actual numeric compilation and module
satisfaction, with explicit scalar-field declaration lookup premises.

These are conditional source-to-target theorems. Constructing the representation
from arbitrary decoded instances and composing frontend, structural, primitive/root
and CLI results remain #20; no whole-domain finite structural equivalence is claimed.

Covers:
- `req~compiler-expression-encoding~1`

## Constraint validation

`utest~compiler-source-constraints~1`

[Kernel examples](../tests/ExpressionPreservation.lean) instantiate an injective
object/integer representation, concrete nonempty owner and navigation domains,
source subtraction and its compiled attachment. They also prove that negating an
undefined source extraction cannot satisfy its generated constraint.

[Native checks](../tests/ExpressionEncodingNative.lean) exercise 35 source cases
covering every constructor, zero/one/multiple primitive observations, parent and
dereference roles, nested shadowing, `this` under binders, false siblings, empty
quantification and undefined negation. The complete inherited Appendix 6 skeleton
supplies repeated owner-specific version constraints and identity/role rejection
variants. Scalar row, numeric range/injectivity, overflow and malformed canonical
conditional mutations exercise admission and enforcement.

The [external runner](../tests/test_expression_encoding.py) runs those 35 generated
modules through the real pinned Analyzer and adds three independently authored
scalar/identity AST references. Four valid-syntax mutations change comparison
order, binder capture, parent/dereference selection and singleton definedness
under a false antecedent. Evidence retains native source identities, actual solver
results and reconstruction outcomes. This adds tests to the existing exact tool
and AST-normalization harness; it does not replace kernel proofs or semantic review.

Covers:
- `req~compiler-expression-encoding~1`
- `req~compiler-alloy-text~1`

## Review and integration boundary

Issue #15 remains In Progress until semantic acceptance. The new requirement and
its implementation/proof/test links are submitted for that review. The resolved-IR
CLI remains M1-only; source integration and scalar instance JSON decoding belong
to #20. M1 admission, dependency pins, the trusted scope and its deadline are unchanged.
The expanded full check initially exceeded the unchanged 120-second deadline.
The existing unittest/Popen worker is reused to schedule the exact comparison
suite alongside the other regressions; its source-matched private receipts and
assertions are unchanged. Existing worker exit/skip/empty-suite guards are retained
and regression-tested for the added suite. No new test framework or dependency is
introduced, and every suite, native build, axiom audit and kernel replay is mandatory.

Existing positional `Signature`/`Instance` constructions include the new scalar
flag/value rows; record callers can use their false/empty defaults.

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

## Constraint-translation continuation: reuse and representation

The continuation of #15 starts from accepted main
`9ef2d6a6bc9a047cb0985033960aa4c92e2c2cb2`. The current runtime and proofs were
inspected before implementation: the postfix Alloy algebras, source checked terms,
finite observations, source range proofs, inherited layout and source attachment
records provide the reusable foundations. Pinned upstream `Denotation`,
`DenotationLaws`, `Integer` and `DenotationInvariance` remain the independent source
meaning. Pinned Haskell `Generator/Alloy.hs` supplies the integer/navigation and
operand-order comparison; it is not a production dependency.

Before this continuation, the target had opaque object atoms and bounded numeric
expressions, but no relation from observed integer objects to scalar values. The selected
representation keeps those original objects and adds one scalar value field on
the finite primitive observation signature. Generated domain and injectivity
facts ensure that observed integer identity agrees with mathematical value.
The primitive signature is not the complete Alloy or mathematical integer domain.
The official Alloy reference's integer expressions, field declarations and
conditional expressions supply the target meaning; the existing parser/printer
and real Analyzer adapter are extended for the emitted forms.

Existing Lean Std list/fold/parser operations and Mathlib finite-set and option
lemmas supply traversal and proof machinery. No new library, evaluator dependency,
solver, copied upstream definitions or license cost is needed. Runtime encoding
stays independent of semantic imports. The constructor and attachment results above discharge the selected conditional
preservation obligations; their semantic acceptance remains a manual review gate.

Task #15 was accepted through PR #41. Selected [#20](pipeline.md) derives the
representation premises from actual target data and composes full structural
integer completion, query agreement and bounded source completeness. Its
semantic acceptance is separate from #15's constructor/attachment acceptance.
