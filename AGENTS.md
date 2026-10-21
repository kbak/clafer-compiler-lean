# Working on Clafer Compiler Lean

Read [intent](docs/intent.md), [requirements](docs/spec.md),
[architecture](docs/architecture.md), [sources](docs/sources.md),
[contribution guidance](CONTRIBUTING.md), and [scope](scope.json).
This is a private structural IR/build project with an adopted Clafer-to-Alloy contract.
Follow the contract's review status and manual intake gates. The build, comparison
and structural IR/admission tasks #5, #6 and #7 are accepted through PRs #23–#25.
Independent Alloy target #8, text #9 and structural backend #10 are accepted
through PRs #26–#28. Correctness task #11 is selected; its representation layer is
partial and global preservation remains unfinished. Do not implement compiler
features until their owning task is selected and its dependencies are accepted.
Behavior and publication remain outside this work.
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
[IntentBond skill](https://github.com/kbak/intentbond/blob/a430efa8d82e2a88ed2607bfe838066bb9d73f3c/intentbond/skills/intentbond/SKILL.md).
Reuse matching installed tooling; follow CONTRIBUTING.md if missing.
Capture the starting Git commit before editing. Maintain affected intent,
requirements, source, tests and links together. Run `ib check` and retain external
evidence before handoff. Exit 4 leaves semantic review pending. Do not weaken
scope or coverage to pass. Scope adoption and amendments require explicit review.

Search issues before creating work; use `python3 scripts/tickets.py` and the
[private Project](https://github.com/users/kbak/projects/3). Keep acceptance criteria
and status current. Planning tickets do not authorize implementation. In IntentMade,
only the coordinator runs credential-bearing ticket operations. Keep credentials,
private deployment paths and runtime state outside source.

When Lean work is authorized, do not present `sorry`, `admit`, or unchecked axioms
as completed proofs. Keep tested behavior distinct from proved properties.
