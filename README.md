# Clafer Compiler Lean

A compiler for [Clafer](https://www.clafer.org/), implemented in Lean 4.

**Status: scaffolding and planning.** There is no compiler implementation yet.
The repository and its [planning board](https://github.com/users/kbak/projects/3)
are private while the design is being worked out.

[Intent and open decisions](docs/intent.md) · [Contributing](CONTRIBUTING.md) ·
[Issues](https://github.com/kbak/clafer-compiler-lean/issues) · [MIT license](LICENSE)

## Scope

This repository will host the compiler. The separate
[Clafer Semantics](https://github.com/kbak/clafer-semantics) project formalizes
Clafer's modeling semantics. Reuse of that formalization, compiler stages,
supported language features, output targets, and correctness claims remain
undecided. No dependency on the semantics project is configured yet.

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
planning issue does not authorize compiler work. The
[requirements](docs/spec.md) define the current scaffolding obligations.
