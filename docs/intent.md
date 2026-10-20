# Intent and open decisions

## Prepare the compiler project

`intent~compiler-foundation~1`

Create a well-maintained home for implementing a Clafer compiler in Lean 4,
using the repository practices of Clafer Semantics. Keep this repository and its
planning board private for now. Establish documentation, contribution guidance,
IntentBond traceability, and manual IntentMade intake before compiler work begins.

Needs: req

## Current boundary

Only project scaffolding is authorized. Compiler implementation and architecture
need a separate decision. Existing MIT licensing is retained; a license does not
change repository visibility. No release or public deployment is planned yet.

## Decisions to make before implementation

- Supported Clafer language/version and initial feature subset.
- Compiler inputs, outputs, command-line/API contract, and backend targets.
- Reuse of Clafer Semantics and the boundary between executable code and proofs.
- Lean toolchain, Lake package structure, dependencies, and upgrade policy.
- Compatibility fixtures and reference implementation revisions/licenses.
- Correctness goals and the distinction between tested and proved properties.

These are questions, not accepted requirements or an implementation roadmap.
Track decisions in issues and update this document and the requirements when
approved. Do not infer implementation permission from a Todo item.

## Documentation map

- [Requirements](spec.md): current repository obligations.
- [Contribution guide](../CONTRIBUTING.md): workflow and validation.
- [Agent guidance](../AGENTS.md): the same workflow for coding agents.
- [Security policy](../SECURITY.md): sensitive reports during the private phase.
