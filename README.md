# Clafer Compiler Lean

A planned structural [Clafer](https://www.clafer.org/)-to-Alloy compiler in Lean 4.

**Status: source pipeline implemented; semantic review pending.** Executable declaration
tables, [proved M1 admission](docs/ir.md), the pinned Lake build, native checks
and [comparison tools](docs/oracles.md) are available. The independent
[static Alloy target model](docs/alloy-core.md),
[structural backend](docs/structural-encoding.md) and
[hygienic serialization](docs/alloy-text.md) are accepted through PRs #26–#28.
The backend translates admitted M1 IR into checked target ASTs with manual bounds.
The [correctness work](docs/structural-correctness.md) proves decoding,
M1 soundness and finite bounded completeness with explicit scope and integer-range
hypotheses. The maintainer accepted #11 through PR #33. Accepted
[inherited realization](docs/inherited-realization.md) (PR #36) adds the full Appendix 6
structural skeleton and preservation proofs.
The [three-way comparison](docs/comparison.md) exercises native-generated Alloy
and strict instance decoding. Accepted #19 (PR #39) supplies the
[native resolved-IR CLI](docs/cli.md).
The accepted [static source parser](docs/parser.md) retains authored syntax and
source diagnostics. Accepted [resolution/defaults](docs/resolution.md) (#17/PR #35)
adds checked declaration elaboration. Accepted [source constraints](docs/constraints.md)
(#18/PR #40) adds automatic typed elaboration and source derivations.
The accepted [typed expression API](docs/expressions.md) adds checked static syntax
and independent semantic interpretation. Accepted [expression encoding](docs/expression-encoding.md)
(PR #41) supplies constructor and attachment preservation. Selected
[source pipeline #20](docs/pipeline.md) composes the actual source command, full
integer source soundness and bounded completeness, and all twelve telematics
bodies. Semantic acceptance, including the primitive-carrier corrections, is pending.
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
auditing and the native execution trust boundary. The executable compiles the
guarded M1 developer IR with explicit bounds:

```sh
.lake/build/bin/clafer-compiler compile-ir tests/fixtures/cli/optional.json \
  --bounds tests/fixtures/cli/bounds.json --output /tmp/example.als
```

See the [CLI contract](docs/cli.md) for stdin/stdout, diagnostics, exit codes and
runtime-only use. Compile source with explicit version-2 bounds:

```sh
.lake/build/bin/clafer-compiler compile-source tests/fixtures/constraints/telematics.cfr \
  --bounds tests/fixtures/pipeline/telematics.bounds.json --output /tmp/telematics.als
```

The validation suite also
requires Bubblewrap and `ldd` on Linux/glibc.

Plan work in issues before implementation. Factory intake is manual, and a
planning issue does not authorize compiler work. Contract review precedes dependent
implementation intake. The [requirements](docs/spec.md) distinguish current
planning obligations from reserved future implementation requirements.
