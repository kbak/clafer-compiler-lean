# Working on Clafer Compiler Lean

Read [intent](docs/intent.md), [requirements](docs/spec.md),
[architecture](docs/architecture.md), [sources](docs/sources.md),
[contribution guidance](CONTRIBUTING.md), and [scope](scope.json).
This is a structural Clafer-to-Alloy compiler with a selected
[behavioral integration contract](docs/behavioral.md). Follow the adopted
contract and manual intake gates. The [documentation map](docs/intent.md#documentation-map)
and [qualification inventory](docs/qualification.md#feature-and-evidence-inventory)
identify the delivered APIs, proof assumptions and testing boundaries. The
[roadmap](https://github.com/kbak/clafer-compiler-lean/issues/4) and linked issues
record acceptance and dependencies.

Do not implement compiler features until their owning task is selected and its
dependencies are accepted. Candidate acceptance requires independent review;
behavioral implementation requires its own selected task and explicit profile.
Feature PRs target `main`; preserve the static regression baseline.
Keep imports one-way from compiler to semantics; use both pinned semantics and
Haskell sources as described in the source register. Do not silently resolve a
discrepancy by changing upstream meanings or broadening language support.

Before implementing, check existing repository code, pinned upstream sources,
standard libraries and relevant maintained libraries/tools for reusable solutions.
Prefer reuse when it meets the contract. Before writing custom infrastructure,
record the candidates checked and concrete gaps or tradeoffs in the affected design
or task notes, including proof/runtime boundaries and dependency/license costs.
An independence requirement alone does not justify rebuilding library machinery.

Use IntentBond for planning, implementation and review. Read the development skill
and applicable references from the revision pinned in
[requirements/intentbond.txt](requirements/intentbond.txt):
[IntentBond skill](https://github.com/kbak/intentbond/blob/f9b4f9e40722dc6a83067ac9e62480159322dd09/intentbond/skills/intentbond/SKILL.md).
Reuse matching installed tooling; follow `CONTRIBUTING.md` if missing.
Capture the starting Git commit before editing. Maintain affected intent,
requirements, source, tests and links together. Run `ib check` and retain external
evidence before handoff. Exit 4 leaves semantic review pending. Do not weaken
scope or coverage to pass. Scope adoption and amendments require explicit review.

Search issues before creating work; use `python3 scripts/tickets.py`. Maintainers
track status in the [Project](https://github.com/users/kbak/projects/3); contributors
without Project access can use `--no-project`. Keep acceptance criteria and status
current. Planning tickets do not authorize implementation. In IntentMade,
only the coordinator runs credential-bearing ticket operations. Keep credentials,
private deployment paths and runtime state outside source.

Use OFT tags in actual Lean comments beside implementations, proofs and tests;
the pinned IntentBond preserves their source paths and lines. Keep component
contracts as explanations of the linked declarations and assumptions. A `proof`
tag does not replace kernel checking or independent review.

When Lean work is authorized, do not present `sorry`, `admit`, or unchecked axioms
as completed proofs. Keep tested behavior distinct from proved properties.

Follow the [documentation style](CONTRIBUTING.md#documentation-and-conduct):
keep the README concise, link authoritative contracts, format code-related terms
with backticks, and retain task history in issues/PRs rather than living docs.
