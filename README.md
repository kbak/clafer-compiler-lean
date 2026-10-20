# Clafer Compiler Lean

A planned structural [Clafer](https://www.clafer.org/)-to-Alloy compiler in Lean 4.

**Status: scaffolding and planning.** There is no compiler implementation yet.
The repository and its [planning board](https://github.com/users/kbak/projects/3)
are private while the design is being worked out.

[Intent](docs/intent.md) · [Architecture](docs/architecture.md) · [Contributing](CONTRIBUTING.md) ·
[Issues](https://github.com/kbak/clafer-compiler-lean/issues) · [MIT license](LICENSE)

## Scope

This repository will host the compiler. The separate
[Clafer Semantics](https://github.com/kbak/clafer-semantics) project formalizes
Clafer's modeling semantics and will be a commit-pinned Lake dependency; it is not
configured yet. The [Haskell compiler](https://github.com/gsdlab/clafer) guides
syntax and compatibility comparisons. [Pinned sources](docs/sources.md) define
their separate roles.

Start with the upstream guarded structural core through a resolved-IR API, then
add its selected static expressions, inherited realization and text frontend.
Behavioral/temporal modeling is excluded. The [feature matrix](docs/architecture.md#feature-matrix)
records the exact boundaries; full Haskell compatibility is not promised.

## Working with the scaffold

Run the repository checks with Python 3.11+ and Bash:

```sh
bash scripts/check.sh
```

Contributions also require the pinned [IntentBond](https://github.com/kbak/intentbond)
check; see [setup and validation](CONTRIBUTING.md#setup-and-validation).
The scaffold intentionally has no Lean toolchain or Lake package yet. CI checks
repository structure and traceability; it does not build or verify a compiler.

Plan work in issues before implementation. Factory intake is manual, and a
planning issue does not authorize compiler work. Contract review precedes dependent
implementation intake. The [requirements](docs/spec.md) distinguish current
planning obligations from reserved future implementation requirements.
