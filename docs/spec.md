# Scaffold requirements

## Honest project boundary

`req~scaffold-boundary~1`

The README and intent document explain the planned compiler, its relationship to
Clafer Semantics, and the absence of an implementation. Compiler design,
dependencies, proof promises, and releases remain undecided. Keep the repository
and Project private until the maintainer explicitly requests publication.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Contribution and validation workflow

`req~intentbond-workflow~1`

Pin IntentBond to an immutable source revision. Keep intent, requirements and
artifact links together, and run the repository check through IntentBond before
handoff. Retain evidence outside source. Exit 4 means automation passed with
semantic review pending, never approval. CI must preserve evidence and expose
that distinction. Scope changes require explicit review.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Issue tracking and manual intake

`req~github-tracking~1`

Use repository issues and a private Project with Todo, In Progress, and Done.
Tasks describe scope, acceptance criteria, sources/requirements, and dependencies.
Planning tickets do not trigger implementation. IntentMade registration uses manual
intake and draft PR publication; deployment configuration and credentials stay
outside this repository.

Covers:
- `intent~compiler-foundation~1`

Needs: impl

## Scaffold artifacts

`impl~scaffold-boundary~1`

[README](../README.md), [intent](intent.md), [security policy](../SECURITY.md), and
[license](../LICENSE) describe the current boundary. GitHub visibility is an
external setting: verify it separately before reporting repository publication.

Covers:
- `req~scaffold-boundary~1`

`impl~intentbond-workflow~1`

[Contribution guidance](../CONTRIBUTING.md), [agent instructions](../AGENTS.md),
[pin](../requirements/intentbond.txt), [scope](../scope.json),
[check entrypoint](../scripts/check.sh), and [CI](../.github/workflows/ci.yml)
provide the scaffold validation workflow. These checks do not verify a compiler.

Covers:
- `req~intentbond-workflow~1`

`impl~github-tracking~1`

[Project configuration](../.github/project.json), [ticket helper](../scripts/tickets.py),
[task template](../.github/ISSUE_TEMPLATE/task.yml), and contribution guidance
support issue tracking. IntentMade's private deployment owns registration and
manual intake settings; repository checks cannot attest to their live state.

Covers:
- `req~github-tracking~1`
