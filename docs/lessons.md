# What the compiler experiment establishes

An independent mathematical semantics can guide an executable structural
Clafer-to-Alloy compiler with machine-checked preservation proofs. This project
provides a concrete implementation, explicit proof assumptions and comparisons
against real external tools. Its guarantees apply to the
[selected language](architecture.md#feature-matrix), not every Haskell Clafer input.

<a id="what-we-learned"></a>

## Established boundaries

**Component proofs need a compatible whole model.** Structural and expression
results must use compatible carriers, roots and primitive domains. Even `[0 = 0]`
requires a full integer realization under the pinned source semantics. The
[kernel counterexamples and carrier contract](pipeline.md#full-integer-carrier)
explain why a root-only carrier or a restricted primitive multiplicity cannot
support that model. The composed proof constructs one source configuration
satisfying both structural and constraint meanings.

**Finite solving needs a connection to infinite meanings.** Alloy represents
bounded observations; the source model realizes all mathematical integers.
[Source pipeline proofs](pipeline.md#composed-assurance) establish that completing
the observed carrier preserves admitted queries and constraints. Unsafe arithmetic
bounds are rejected. Completeness requires the concrete observation witness and
`Fits`; no arbitrary-carrier normalization theorem is claimed.

**Comparisons need identical questions.** Two translations can both be satisfiable
while allowing different instances. The [comparison harness](comparison.md) fixes
the same candidate and retains original objects, reference occurrences, scopes
and tool options. Mutations test whether missing constraints or altered relations
are detected. Haskell comparisons stay inside the common admitted domain;
defaulting differences are recorded explicitly.

**Proofs and execution tests cover different boundaries.** Kernel replay checks
the stated Lean declarations. Parser, native binary, serialized Alloy and Analyzer
tests exercise components outside those proofs. Traceability and source-bound
evidence make the claims reviewable; they do not establish that the requirements
are complete or the proofs state the right properties.

## Comparison with the Haskell compiler

| Dimension | Supported conclusion |
| --- | --- |
| Semantic assurance | This project supplies kernel-checked admission, elaboration and preservation results against independent meanings, with explicit assumptions. The inspected Haskell reference pipeline does not supply an equivalent proof chain. This does not measure overall defect rates. |
| Executable correctness | Parser recognition, JSON decoding correspondence, generated native code, emitted-text interpretation and solving remain tested boundaries. No end-to-end verified executable claim follows. |
| Language coverage | Haskell supports a wider language. This compiler restricts structural syntax, inheritance and arithmetic, and retains adopted defaulting differences. |
| Performance | Measurements apply to the recorded candidate, input corpus and host. The [benchmark method](qualification.md#measurements-and-replay) separates compiler costs from solving; the [native optimization measurements](https://github.com/kbak/clafer-compiler-lean/issues/50) retain results and their source identities. |
| Reliability in use | Field defect rates, long-term maintenance costs, adversarial robustness and user outcomes have not been measured. |

<a id="use-for-other-projects"></a>

## Reuse and alternative implementations

Researchers can reuse the source/target relations, finite-observation construction
and nonvacuous counterexamples. Compiler developers can use the executable
implementation and exact-candidate corpus as references for regression testing.

A faster implementation in Lean or another language can use this compiler as an
executable reference and Clafer Semantics as the mathematical specification.
Matching test results provides comparison evidence. To inherit a preservation
claim, the replacement needs a proof connecting its behavior to the verified
translation or directly to the independent source and target meanings.

Within Lean, this project uses kernel-proved function equalities for cached indices,
shared rendering and early fixed-point termination. These replacements retain
the existing preservation proofs; native tests and benchmarks still check execution
and cost. The [build contract](build.md) describes that boundary.

Reuse remains subject to the documented scope and licenses. The repository and
qualification artifacts remain private; wider sharing requires a separate
maintainer decision.
