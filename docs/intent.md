# Intent and delivery boundaries

## Prepare the compiler project

`intent~compiler-foundation~1`

Build a structural Clafer-to-Alloy compiler in Lean 4 in this separate repository,
using Clafer Semantics as its independent mathematical foundation and the Haskell
Clafer compiler as a compatibility reference. Keep the repository and planning
board private, with IntentBond traceability and manual task intake.
Avoid unnecessary infrastructure by checking reusable implementations before
writing new ones and recording concrete reasons for custom solutions.

Needs: req

## Current boundary

The repository contains the adopted structural compiler contract and a Lean/Lake
build bootstrap, reproducible external [comparison tooling](oracles.md), executable
[structural IR](ir.md) with admission proofs and an independent
[static Alloy target core](alloy-core.md) with
[hygienic text serialization](alloy-text.md). The
[guarded structural backend](structural-encoding.md) translates admitted M1 IR into
checked target ASTs with explicit manual bounds. The M1 correctness proof layer
is accepted. Selected [inherited realization](inherited-realization.md) adds the
Appendix 6 structural skeleton and preservation proofs, pending semantic review;
Inherited/source-text CLI integration remains a later task; #19 exposes only M1 IR.
The accepted [static parser](parser.md) preserves authored syntax and source diagnostics;
[checked declaration resolution/defaulting](resolution.md) is accepted through #17/PR #35.
Selected [source constraint elaboration](constraints.md) #18 adds typed bodies and
source derivations, with semantic review pending. The selected direction is
structural only. Behavioral/temporal modeling is outside this roadmap.
The [contract adoption issue](https://github.com/kbak/clafer-compiler-lean/issues/2)
was accepted through merged PR #22. Build, oracle and IR tasks #5–#7 were accepted
through merged PRs #23–#25; target #8, text #9 and structural backend #10 through
PRs #26–#28. Correctness task #11 is accepted through maintainer review of PR #33. Its
[representation and preservation layer](structural-correctness.md) proves M1
soundness and bounded completeness for finite sources fitting explicit scopes
and integer ranges. The maintainer accepted those proofs at
`67b9137cde9e2b486733aecd6eb4f5559b780ea3` and selected #13. Its inherited
structural implementation and proofs await semantic acceptance.
Parser task #16 is accepted through PR #30. Task #17 is accepted through merged
PR #35. Task #18 is selected after #17/#14;
its source elaboration and proof handoff await semantic acceptance.
Typed expression task #14 is accepted through PR #32. The
[expression API](expressions.md) supplies checked syntax, independent denotation
and finite-observation proofs. Task #15 is selected; its
[bounded target arithmetic](expression-encoding.md) was merged through PR #34.
Source range-analysis proofs now connect finite observation budgets to independent
denotation, with semantic review pending. Source constraint translation and
attachment preservation remain unfinished. Selected #19 supplies the
[native resolved-IR CLI](cli.md) after accepted #12,
with strict developer JSON, explicit bounds and deterministic diagnostics/output;
its semantic review is pending. Other tasks require their own selection.
Approval of a roadmap does not start its implementation tickets.

Dependencies flow one way: `ClaferCompiler -> Clafer -> FormalCD -> DPGraph -> Mathlib`.
Upstream owns mathematical meanings, accepted source corrections and reusable
results. This repository owns executable representations, the frontend, Alloy
backend and compiler-specific proofs. The Lake dependency pins the upstream
commit; no semantic definitions are vendored here. The [build contract](build.md)
records executable/proof boundaries. Existing MIT licensing is retained.
Publication remains a separate
[decision](https://github.com/kbak/clafer-compiler-lean/issues/3).

The selected [three-way comparison](comparison.md) connects actual native-generated
Alloy and strict instance decoding to the pinned checker and Haskell comparison.
Its finite execution evidence complements the independent M1 preservation proofs.

## Delivery and selected language scope

The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) delivers:

- **M0:** reviewed contracts, then a reproducible build and comparison tools.
- **M1:** the exact upstream guarded effective structural core, compiled through
  a resolved-IR API and native IR-to-Alloy CLI with explicit bounds.
- **M2:** the upstream typed static core, selected inherited realization and text
  frontend: Boolean logic, sets/relations, navigation, finite quantifiers,
  cardinality, singleton integer extraction and integer addition/subtraction.
  Enums, strings/reals, multiplication/division/aggregations and other wider
  Haskell features are explicitly deferred.
- **M3:** integrated source-text CLI, complete supported Appendix 6 telematics
  model, composed assurance and private qualification.

The [architecture contract](architecture.md) specifies the detailed feature matrix,
interfaces, arithmetic policy, ownership and proposed theorem shapes. Source and
target meanings must be independent. Tested bounded agreement is distinct from
proved soundness/completeness within stated representation and scope bounds;
neither establishes unrestricted Haskell compatibility or unbounded UNSAT.

The [source register](sources.md) pins both guides and records their different
roles. A SoSyM research tag or maintenance branch is not a compiler prerequisite.

## Review and remaining choices

The upstream-core M2 scope is selected. Detailed surface forms, diagnostic/API
conventions, conservative arithmetic admission and the finite observation bridge
were adopted with issue #2. Implementation tasks will supply their
exact Lean declarations, algorithms, fixtures and proof/test artifacts; none exists
by virtue of this plan. See the [review handoff](architecture.md#review-handoff).

## Documentation map

- [Requirements](spec.md): current repository and planning obligations.
- [Architecture](architecture.md): feature, interface, assurance and ownership contract.
- [Sources](sources.md): immutable baselines, paper locators and upgrade policy.
- [Native CLI](cli.md): resolved-IR command, strict JSON, diagnostics and runtime boundary.
- [Three-way comparison](comparison.md): exact candidates, decode, search and replay.
- [Oracles](oracles.md): external tools, fixture admission, replay and triage.
- [IR](ir.md): executable declarations and exact upstream admission proofs.
- [Expressions](expressions.md): typed static syntax, full-integer observation and proof boundaries.
- [Expression encoding](expression-encoding.md): target arithmetic, source range proofs and remaining preservation obligations.
- [Alloy core](alloy-core.md): independent target API, bounds, correspondence and tests.
- [Alloy text](alloy-text.md): naming, source maps, checked serialization and its proof boundary.
- [Structural encoding](structural-encoding.md): M1 target layout, generation and local proofs.
- [Correctness work](structural-correctness.md): finite representation, M1 soundness, bounded completeness and review boundary.
- [Source constraints](constraints.md): inference rules, automatic elaboration, attachment and meaning proofs.
- [Resolution](resolution.md): source identities, lookup, defaults, admission and proof boundaries.
- [Parser](parser.md): authored static grammar, source diagnostics, reuse and assurance limits.
- [Contribution guide](../CONTRIBUTING.md): workflow and validation.
- [Agent guidance](../AGENTS.md): the same workflow for coding agents.
- [Security policy](../SECURITY.md): sensitive reports during the private phase.
