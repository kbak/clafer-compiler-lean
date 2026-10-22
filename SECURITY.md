# Security

This is a private research compiler with a native command-line interface and no
supported stable releases. Fixes apply to `main`. Qualification archives are
private review artifacts, not supported releases.

Report sensitive issues directly to repository owner `@kbak` through an established
private channel. Include the affected revision, platform, impact and a minimal
reproducer. Do not include credentials in issues, pull requests, logs or reports.
A contact route usable by outside contributors remains required by
[readiness issue #3](https://github.com/kbak/clafer-compiler-lean/issues/3).

The compiler reads source/IR and bounds files and writes Alloy and optional
metadata. Treat model inputs as untrusted. Running the compiler does not invoke
Haskell or a solver; those tools belong to the development and validation workflow.
Preservation proofs concern the documented mathematical translation. They do not
establish memory safety, resistance to resource exhaustion, dependency security
or correctness of native execution.

Ordinary bugs and incorrect semantic claims belong in repository issues with the
affected revision and reproduction steps or a small counterexample. Report a
suspected security impact privately first when disclosure could expose users.
