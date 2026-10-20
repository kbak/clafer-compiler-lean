# Working on Clafer Compiler Lean

Read [intent](docs/intent.md), [requirements](docs/spec.md),
[contribution guidance](CONTRIBUTING.md), and [scope](scope.json).
This is a private scaffold. Do not implement compiler features, select architecture,
add a Lean toolchain, or make the repository public without the maintainer's decision.

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
