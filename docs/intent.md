# Intent and delivery boundaries

## Build a structural compiler

`intent~compiler-foundation~1`

Build a structural Clafer-to-Alloy compiler in Lean 4 in this separate repository,
using Clafer Semantics as its independent mathematical foundation and the Haskell
Clafer compiler as a compatibility reference. Publish the source under MIT, with
public issues and pull requests, IntentBond traceability and manual task intake.
Avoid unnecessary infrastructure by checking reusable implementations before
writing new ones and recording concrete reasons for custom solutions.

Needs: req

## Current boundary

The compiler accepts the selected structural source language and guarded M1
resolved IR, producing checked static Alloy with explicit bounds. The
[source pipeline](pipeline.md) composes parsing, declaration resolution/defaulting,
typed constraint elaboration, inherited realization and expression encoding.
Its assurance includes M1 soundness and finite bounded completeness, expression
preservation, and full integer source-model composition under the stated
representation, scope and observation assumptions. Grammar-to-parser correspondence
and native/serialized execution remain tested boundaries.

The [qualification inventory](qualification.md#feature-and-evidence-inventory)
links each supported feature to its contract and evidence. Each generated
qualification candidate needs independent semantic review. The [roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4)
and linked issues retain delivery and acceptance history.

New compiler features require explicit selection and accepted dependencies.
Approval of a roadmap does not start its implementation tickets. Behavioral and
temporal modeling remain outside the project.

Dependencies flow one way: `ClaferCompiler -> Clafer -> FormalCD -> DPGraph -> Mathlib`.
Upstream owns mathematical meanings, accepted source corrections and reusable
results. This repository owns executable representations, the frontend, Alloy
backend and compiler-specific proofs. The Lake dependency pins the upstream
commit; no semantic definitions are vendored here. The [build contract](build.md)
records executable/proof boundaries. Existing MIT licensing is retained.

The [three-way comparison](comparison.md) connects actual native-generated
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
  model, composed assurance and candidate qualification.

The [architecture contract](architecture.md) specifies the detailed feature matrix,
interfaces, arithmetic policy, ownership and required theorem shapes. Source and
target meanings must be independent. Tested bounded agreement is distinct from
proved soundness/completeness within stated representation and scope bounds;
neither establishes unrestricted Haskell compatibility or unbounded UNSAT.

The [source register](sources.md) pins both guides and records their different
roles. A SoSyM research tag or maintenance branch is not a compiler prerequisite.

## Review boundaries

The adopted upstream-core M2 scope fixes the selected surface forms, diagnostics,
conservative arithmetic admission and finite observation bridge. Exact delivered
APIs and proof assumptions live in the component contracts below. Scope changes
and semantic acceptance require explicit review; see the
[review handoff](architecture.md#review-handoff).

## Documentation map

- [Requirements](spec.md): compiler, assurance and workflow obligations.
- [Architecture](architecture.md): feature, interface, assurance and ownership contract.
- [Sources](sources.md): immutable baselines, paper locators and upgrade policy.
- [Native CLI](cli.md): source/IR commands, strict JSON, diagnostics and runtime boundary.
- [Source pipeline](pipeline.md): integrated compilation, full-model proofs and complete telematics.
- [Qualification](qualification.md): feature inventory, benchmarks and candidate review.
- [Results and reuse](lessons.md): established guarantees, reuse and limits of the Haskell comparison.
- [Build](build.md): module ownership, dependency preparation and kernel/native checks.
- [Three-way comparison](comparison.md): exact candidates, decode, search and replay.
- [Oracles](oracles.md): external tools, fixture admission, replay and triage.
- [IR](ir.md): executable declarations and exact upstream admission proofs.
- [Expressions](expressions.md): typed static syntax, full-integer observation and proof boundaries.
- [Expression encoding](expression-encoding.md): source constraint encoding, observation bounds and conditional preservation proofs.
- [Alloy core](alloy-core.md): independent target API, bounds, correspondence and tests.
- [Alloy text](alloy-text.md): naming, source maps, checked serialization and its proof boundary.
- [Structural encoding](structural-encoding.md): M1 target layout, generation and local proofs.
- [Inherited realization](inherited-realization.md): original objects/links, context views and structural preservation.
- [Structural correctness](structural-correctness.md): finite representation, M1 soundness, bounded completeness and review boundary.
- [Source constraints](constraints.md): inference rules, automatic elaboration, attachment and meaning proofs.
- [Resolution](resolution.md): source identities, lookup, defaults, admission and proof boundaries.
- [Parser](parser.md): authored static grammar, source diagnostics, reuse and assurance limits.
- [Contribution guide](../CONTRIBUTING.md): workflow and validation.
- [Agent guidance](../AGENTS.md): the same workflow for coding agents.
- [Security policy](../SECURITY.md): supported versions and private reporting.
