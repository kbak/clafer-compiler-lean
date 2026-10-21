# Clafer Compiler Lean

A planned structural [Clafer](https://www.clafer.org/)-to-Alloy compiler in Lean 4.

**Status: guarded structural backend candidate.** Executable declaration
tables, [proved M1 admission](docs/ir.md), the pinned Lake build, native checks
and [comparison tools](docs/oracles.md) are available. The independent
[static Alloy target model](docs/alloy-core.md) is accepted. The
[structural backend](docs/structural-encoding.md) translates admitted M1 IR into
checked target ASTs with manual bounds and was accepted through PR #28. Global
preservation proofs remain pending. The selected [representation work](docs/structural-correctness.md)
proves concrete decoding and data round trips; serialization and CLI integration
are separate tasks.
The repository and its [planning board](https://github.com/users/kbak/projects/3)
are private while the design is being worked out.

[Intent](docs/intent.md) · [Architecture](docs/architecture.md) · [Contributing](CONTRIBUTING.md) ·
[Issues](https://github.com/kbak/clafer-compiler-lean/issues) · [MIT license](LICENSE)

## Scope

This repository hosts the compiler. The separate
[Clafer Semantics](https://github.com/kbak/clafer-semantics) project formalizes
Clafer's modeling semantics and is an immutable, commit-pinned Lake dependency.
The [Haskell compiler](https://github.com/gsdlab/clafer) guides
syntax and compatibility comparisons. [Pinned sources](docs/sources.md) define
their separate roles.

Start with the upstream guarded structural core through a resolved-IR API, then
add its selected static expressions, inherited realization and text frontend.
Behavioral/temporal modeling is excluded. The [feature matrix](docs/architecture.md#feature-matrix)
records the exact boundaries; full Haskell compatibility is not promised.

## Build and check

Install Lean through Elan, Python 3.11+, Git, Bash, Java 17, GMP headers and a C toolchain. The repository
selects Lean 4.35.0. Prepare pinned dependencies once, then run all gates:

```sh
bash scripts/prepare_dependencies.sh
python3 scripts/oracles/oracle.py prepare /tmp/clafer-oracle-tools-UNIQUE
export CLAFER_ORACLE_TOOLS=/tmp/clafer-oracle-tools-UNIQUE/tools.json
bash scripts/check.sh
.lake/build/bin/clafer-compiler --version
```

Contributions also require the pinned [IntentBond](https://github.com/kbak/intentbond)
check; see [setup and validation](CONTRIBUTING.md#setup-and-validation).
The [build contract](docs/build.md) describes module ownership, kernel/axiom
auditing and the native execution trust boundary. The executable only supports
`--version`; compilation commands arrive in later tasks.

Plan work in issues before implementation. Factory intake is manual, and a
planning issue does not authorize compiler work. Contract review precedes dependent
implementation intake. The [requirements](docs/spec.md) distinguish current
planning obligations from reserved future implementation requirements.
