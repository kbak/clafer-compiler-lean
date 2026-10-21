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
checked target ASTs with explicit manual bounds. Global compiler correctness
proofs and CLI integration remain separate tasks. The selected
[static parser](parser.md) preserves authored syntax and source diagnostics;
resolution/defaulting and expression typing remain separate tasks. The selected
direction is
structural only. Behavioral/temporal modeling is outside this roadmap.
The [contract adoption issue](https://github.com/kbak/clafer-compiler-lean/issues/2)
was accepted through merged PR #22. Build, oracle and IR tasks #5–#7 were accepted
through merged PRs #23–#25; target #8, text #9 and structural backend #10 through
PRs #26–#28. Correctness task #11 is selected. Its
[finite representation layer](structural-correctness.md) is partial; global
soundness and bounded completeness remain unfinished. Parser task #16 is selected
after accepted prerequisite #6; its semantic review remains pending. Typed
expression task #14 is selected with semantic review pending. The
[expression API](expressions.md) supplies checked syntax, independent denotation
and finite-observation proofs. Other tasks require their own selection.
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
Its evidence remains finite; it does not complete the outstanding global proofs.

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
- [Three-way comparison](comparison.md): exact candidates, decode, search and replay.
- [Oracles](oracles.md): external tools, fixture admission, replay and triage.
- [IR](ir.md): executable declarations and exact upstream admission proofs.
- [Expressions](expressions.md): typed static syntax, full-integer observation and proof boundaries.
- [Alloy core](alloy-core.md): independent target API, bounds, correspondence and tests.
- [Alloy text](alloy-text.md): naming, source maps, checked serialization and its proof boundary.
- [Structural encoding](structural-encoding.md): M1 target layout, generation and local proofs.
- [Correctness work](structural-correctness.md): finite representation and remaining preservation obligations.
- [Parser](parser.md): authored static grammar, source diagnostics, reuse and assurance limits.
- [Contribution guide](../CONTRIBUTING.md): workflow and validation.
- [Agent guidance](../AGENTS.md): the same workflow for coding agents.
- [Security policy](../SECURITY.md): sensitive reports during the private phase.
