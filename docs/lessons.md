# What the compiler experiment establishes

The M0–M3 milestone shows that an independent mathematical semantics can guide a
working structural Clafer-to-Alloy compiler, with preservation proofs and tests
against real external tools. Its most useful result is an explicit account of
what the translation preserves, under which assumptions, and where testing still
supplies the evidence. It does not establish that Lean programs are automatically
correct or that this compiler is a replacement for every Haskell Clafer use case.

## What we learned

**Composition found mistakes that individual components missed.** The initial
synthetic integer declaration had a restricted multiplicity incompatible with
the full mathematical integer domain. A second problem appeared even for
`[0 = 0]`: without an integer reference, elaboration created only the root, while
constraint semantics required all integers in the same carrier. The retained
`Tests.PipelineLimits.root_only_no_integer_realization` theorem demonstrates that
contradiction. Corrections [#42](https://github.com/kbak/clafer-compiler-lean/issues/42)
and [#43](https://github.com/kbak/clafer-compiler-lean/issues/43) repaired downstream
elaboration while retaining upstream meanings. The
[composition account](pipeline.md#carrier-decision-exposed-by-composition) explains
why separate structural and expression theorems were insufficient.

**Finite solving requires an explicit connection to infinite meanings.** Alloy
represents bounded observations; the source model realizes all mathematical
integers. The compiler proves that completing the observed carrier preserves
admitted queries and constraints. It rejects unsafe arithmetic bounds rather
than silently changing mathematical arithmetic to wraparound. Completeness still
requires the concrete observation witness and `Fits`; no arbitrary-carrier
normalization theorem is claimed.

**Independent comparisons need identical questions.** Agreement that two models
are satisfiable can conceal different valid instances. The
[comparison harness](comparison.md) fixes the same candidate and retains original
objects, reference occurrences, scopes and tool options. Mutations check that a
missing constraint or altered relation can be detected. Haskell comparisons stay
inside the common admitted domain; defaulting differences are recorded rather
than classified automatically as bugs in either implementation.

**Proofs and execution tests cover different boundaries.** Kernel replay checks
the stated Lean declarations. Actual parser, native binary, serialized Alloy and
Analyzer tests exercise components outside those proofs. Neither substitutes for
the other. Traceability and source-bound evidence make the claims reviewable;
they do not establish that the requirements are complete or the proofs state the
right properties.

**The validation process needs its own engineering.** The accepted qualification
check took 114.604 seconds against a 120-second deadline. Later unchanged-baseline
timeouts showed how little margin that left. A warm working-tree success cannot
replace a failed fresh-snapshot check. Evidence also needs retained storage and
exact source identities to remain useful after temporary directories disappear.

## Comparison with the Haskell compiler

| Dimension | Supported conclusion |
| --- | --- |
| Semantic assurance in the selected fragment | This project supplies kernel-checked admission, elaboration and preservation results against independent meanings, with explicit assumptions. The inspected Haskell reference pipeline does not supply an equivalent proof chain. This is a stronger documented assurance argument, not a measured overall defect rate. |
| Executable correctness | Parser recognition, JSON decoding correspondence, generated native code, emitted-text interpretation and solving remain tested boundaries. No end-to-end verified executable claim follows. |
| Language coverage and compatibility | The Haskell compiler supports a wider language. This compiler deliberately restricts structural syntax, inheritance and arithmetic, and retains adopted defaulting differences. Even structural inputs must satisfy the published feature matrix. |
| Measured compiler performance | The pinned Haskell compiler was faster and used less memory on all three measured common-domain inputs. No Lean performance advantage was demonstrated. |
| Reliability in use | The experiment did not measure field defect rates, long-term maintenance costs, adversarial robustness or user outcomes. A blanket “higher quality” conclusion is unsupported. |

The [qualification experiment](qualification.md#measurements-and-replay) measured
five fresh-process samples after one warmup, with warm filesystem caches, identical
common-domain source and independently audited scopes. At candidate
`e8164804d1917d7b01f8111e1f269bd6c7ffdb4b`, median Lean/Haskell compilation times were
29.23/12.24 ms, 27.24/12.32 ms and 85.43/22.50 ms for the tiny, representative and
larger inputs. Peak process memory was approximately 65–67 MiB for Lean and
12–18 MiB for Haskell. These are descriptive observations on the recorded host,
not general performance guarantees. Solver performance was not compared.

## Use for other projects

Researchers can reuse the concrete source/target relations, finite-observation
construction and nonvacuous counterexamples. Compiler developers can use the
restricted implementation and exact-candidate corpus as additional references for
regression testing. Teams building model translators can follow the separation
between independent meanings, executable representations, preservation proofs
and external execution evidence.

The project is also a concrete example of agent-assisted formal development with
review gates. It is not a controlled study of AI productivity: there is no matched
human-only baseline or measured cost/defect comparison. The evidence supports
technical feasibility, not autonomous correctness or a general productivity claim.

These uses remain subject to the documented scope, licenses and trust boundaries.
The repository and qualification artifacts remain private; sharing them more
widely requires a separate maintainer decision.
