# Native resolved-IR compiler

[Issue #19](https://github.com/kbak/clafer-compiler-lean/issues/19) selects the
native M1 driver after accepted #12. Its implementation is subject to semantic
review. Source-text compilation remains #20; publication is not authorized.

## Reuse assessment

The driver composes the existing `IR.Structural.validateDocument`,
`Backend.Alloy.Structural.compile` and `Text.render`. It preserves their guards,
explicit scopes and successful-render reconstruction boundary. The #12 numeric
test transport is deliberately not the developer JSON protocol. The pinned
upstream `Clafer/Verification/ImportMain.lean` also requires external strict JSON
decoding and imports proof machinery, so it cannot serve the standalone driver.

Lean 4.35.0 supplies `Std.Internal.Parsec`, `Lean.Json`, UTF-8 validation, streams,
exclusive file creation and rename. Its JSON parser overwrites duplicate keys,
normalizes number tokens and replaces unmatched surrogate escapes with U+FFFD.
Those behaviors conflict with the accepted [IR interchange](ir.md). Reuse its
Parsec cursor/combinators, hexadecimal decoding, valid surrogate-pair decoding,
JSON value representation and output escaping; add only strict string/object and
natural-token admission plus schema-specific field decoding. Recursive JSON
nesting reuses the source parser's `Nat.repeat` construction with input-derived
fuel; option handling uses standard-library folds. This also avoids compiler-generated
recursion helpers rejected by the project's declaration audit. Parsing and native IO remain tested runtime
boundaries, not new kernel correspondence proofs.

Lake's general CLI utilities are geared toward Lake commands and add a Lake
runtime import. The already pinned MIT `lean4-cli` package was also inspected:
`Cli.Cmd.parse` checks duplicate flags, but installs built-in help/version rules
and a broader flag/positional grammar; selecting it would require an adapter for
the fixed pair grammar, stable diagnostic codes and required option checks. This
small command uses a total list traversal; no generic option-parser framework or
foreign JSON runtime is added. Python's existing
unittest runner, JSON encoder, seeded generators and subprocess tools support
boundary and metamorphic tests. Hypothesis was considered; the existing finite
generation convention suffices for these small selected domains without another
dependency. Runtime isolation uses maintained Bubblewrap namespaces and the
system dynamic loader. These tools are verification prerequisites, not compiler
runtime dependencies. Lean library imports retain Apache-2.0 licensing; original
driver/test code remains MIT. No dependency pins or scope policy change.

The full check's fixed 120-second deadline also requires overlapping the new CLI
suite with existing regressions. The existing unittest discovery/runner and
standard `subprocess` are reused: one separate process runs the two CLI modules,
while the parent runs all remaining discovered cases. Both must execute nonempty
suites without skips and pass. Separate processes avoid sharing Python mocks or
module state. The CLI process builds only its own test harness and runtime objects
already built by the production executable, plus frontend parser objects unused
by the concurrently starting target tests. Pytest/xdist was considered but would
add dependencies and change collection semantics for an established unittest suite.
No case, assertion, kernel gate or timeout is removed; failure propagation is tested.

## Command contract

`clafer-compiler --version` reports the package version, exact M1 profile, IR and
bounds versions, semantic/Haskell source pins and absence of source-text support.
`--help` prints usage. Compilation is:

```sh
clafer-compiler compile-ir model.json --bounds bounds.json --output model.als
clafer-compiler compile-ir - --bounds bounds.json --output - --diagnostics json
```

All three input/bounds/output arguments are required. `-` selects stdin/stdout;
at most one input may use stdin. `--objects N` and `--bitwidth N` override the
explicit corresponding bounds-file values. Duplicate/unknown options fail.
Numbers use nonnegative decimal tokens without signs or leading zeroes.
`compile-source` is unsupported. No solver or reference compiler runs implicitly.

The [closed `clafer-bounds/1` schema](../schemas/clafer-bounds-1.schema.json)
contains `version`, `objects`, `bitwidth`, and
`declarations`, an array of closed `{id, size, exact}` entries. Every declaration,
including the root and abstract declarations, needs exactly one entry. The object
budget counts distinct live objects, including the root, rather than summing
overlapping inherited extents. Widths 1–16 are checked by the existing backend;
unsafe count/literal bounds are unsupported. Contradictory valid bounds compile.
The schema describes values; the same strict lexical rules as developer IR reject
duplicate keys, exponent/fraction/signed number tokens and invalid UTF-8/escapes.

Run the committed [optional model](../tests/fixtures/cli/optional.json) with its
[bounds](../tests/fixtures/cli/bounds.json):

```sh
.lake/build/bin/clafer-compiler compile-ir tests/fixtures/cli/optional.json \
  --bounds tests/fixtures/cli/bounds.json --output /tmp/example.als
```

Success writes only complete deterministic Alloy, with exit 0 and empty stderr.
Compilation makes no SAT claim. Malformed input/options exit 2, unsupported
profiles/ranges/source input exit 3, and IO/internal failures exit 1. Diagnostics
go only to stderr, in text by default or one version-1 JSON object with
`--diagnostics json`. JSON carries stable code, phase, category, message, primary
IR filename/pointer/declaration ID and related locations. IR metadata has no
source buffer: no line/column is invented from supplied byte spans. Exact English
wording is not stable. The driver reports the first failure deterministically.
Its order is argument checks, input/bounds reads, lexical/schema IR decoding,
existing IR admission, bounds decoding, target generation/range checks, checked
serialization and output. Schema fields use fixed decoder order. Argument and
IO diagnostics without an IR position use an empty pointer and null declaration.
`Driver.sourceDiagnosticJson` serializes the existing source diagnostic shape,
including original CRLF/Unicode byte positions, one-based scalar coordinates and
related source spans; it does not add source compilation to the command.

| Code(s) | Phase | Category |
| --- | --- | --- |
| `cli.arguments` | arguments | malformed |
| `cli.source-unsupported` | arguments | unsupported |
| `input.utf8`, `input.json`, `input.schema` | decode | malformed |
| `ir.version`, `ir.profile`, `bounds.version` | decode | unsupported |
| Existing [IR codes](ir.md#diagnostics) | admission | unchanged |
| `bounds.declarations` | bounds | malformed |
| `bounds.unsafe` | bounds | unsupported |
| `compiler.target`, `compiler.render` | encoding, serialization | operational |
| `io.read`, `io.write` | io | operational |

All decoding, admission, generation and rendering finish before opening output.
File output uses an exclusively created sibling temporary file, flush and rename;
failure before rename preserves an existing output. Stdout is buffered until
rendering completes, but the OS cannot roll back a failed pipe write. File-system
crash durability is not promised. Source names and paths never enter Alloy syntax.

## Native runtime

Build with the pinned Lean/Lake toolchain as described in [build](build.md), then
copy `.lake/build/bin/clafer-compiler` into a private Linux/glibc runtime. The
tested platform is x86-64 Linux. The binary links Lean and its compiler support
statically; no `.olean`, Lake, Elan, source checkout, Haskell, Java or Alloy is
needed to compile developer IR. The ELF loader and glibc libraries remain system
dependencies: `ld-linux-x86-64.so.2`, `libc.so.6`, `libm.so.6`, `libpthread.so.0`,
`libdl.so.2` and `librt.so.1` in the tested build. Inspect `ldd` on the actual binary
on each deployment platform; this is not a portability claim to older glibc,
other architectures or operating systems.

[The runtime test](../tests/test_cli_external.py) builds an empty Bubblewrap root
containing only that binary, the exact `ldd` library closure, kernel device/proc
mounts and an input/output directory. It clears the environment, runs `--version`
and compiles the example, comparing bytes with ordinary execution. No development
toolchain or oracle is mounted. It retains command logs and binary/library hashes
under `CLAFER_ORACLE_EVIDENCE`. Missing isolation tools or failed namespace setup
fail the required test rather than skip it. Bubblewrap and `ldd` are verification
tools only. Validation needs working unprivileged user/mount/PID namespaces;
network isolation is not required for this runtime dependency check.

System glibc components retain their LGPL licenses and Lean's statically linked
components retain their upstream notices. This private execution check uses host
libraries without copying them into source or publishing a distribution. Packaging
license qualification remains #21. This issue authorizes no public binary release.

## Assurance and handoff

The driver adds no semantic theorem or assumption. Existing admission,
structural preservation and successful-render theorems retain their precise
in-memory boundaries. JSON/schema correspondence, argument parsing, diagnostic
serialization, native execution and file operations are exercised externally.
Compile success, target SAT, bounded UNSAT, timeout and unsupported input remain
distinct. The implementation/test inventory and runtime-only commands are
recorded below. IntentBond exit 4 leaves semantic acceptance pending.

`Driver.Decode.document` returns the original `IR.Structural.Raw` fields;
`Driver.Decode.bounds` returns the existing manual bound structure.
`Driver.compileText` returns `Driver.Product` containing complete text, original
declaration maps and generated byte maps. `Driver.options`, `run`, `readInput`
and `writeOutput` implement the command/IO boundary. The driver does not change
upstream meanings or add theorem hypotheses. `Correctness.version_response` and
`empty_response` remain pure informational-response equations; they do not prove
the command dispatcher. #20 can reuse the decoder/diagnostic/output components
after this task's acceptance.

## Implementation and test trace

`impl~compiler-cli-integration~1`

[Driver](../ClaferCompiler/Driver.lean), [strict JSON](../ClaferCompiler/Driver/Json.lean),
[schema decoder](../ClaferCompiler/Driver/Decode.lean),
[diagnostics](../ClaferCompiler/Driver/Diagnostic.lean) and [Main](../Main.lean)
implement the command above by composing the existing M1 APIs. The exact
toolchain JSON imports are admitted by [module inventory](../scripts/project_modules.py);
arbitrary Lean/elaborator imports remain rejected.

Covers:
- `req~compiler-cli~1`
- `req~compiler-diagnostics~1`
- `req~compiler-ir~1`

`utest~compiler-cli-boundaries~1`

[Native command tests](../tests/test_cli.py) cover file/stdin/stdout, strict JSON,
schema/admission errors, identities, unsupported profiles, bounds overrides,
contradictions, IO failures and existing-file preservation. Twenty-four generated
identity/name/JSON-layout variants (seed 190021) assert identical Alloy bytes;
independent variant/lexical-error subprocesses use four workers with separate
input/output directories and unchanged assertions. These finite tests are not a
universal invariance proof. [API tests](../tests/Driver.lean)
check actual source maps and serialization of a parser-generated CRLF/Unicode EOF
diagnostic. [External tests](../tests/test_cli_external.py) invoke the actual
production executable and reuse [the Analyzer adapter](../scripts/oracles/AlloyTextBridge.java)
through a [small integration wrapper](../tests/CLIOracle.java). They distinguish
SAT/UNSAT for optional, zero-root, duplicate bag-target and set-key cases, and run
the runtime-only environment described above. Existing exact three-way and
mutation tests remain required. All external parsing/native results are tested
behavior, not new semantic proofs.

Covers:
- `req~compiler-cli~1`
- `req~compiler-diagnostics~1`
- `req~compiler-ir~1`
