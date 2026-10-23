# Security

Security fixes apply to `main`. There are no supported stable releases.
Qualification bundles are review artifacts, not supported releases.

Report sensitive issues to `@kbak` through this repository's
[private reporting form](https://github.com/kbak/clafer-compiler-lean/security/advisories/new).
Include the revision, platform, impact and a minimal reproducer. The form requires
a GitHub account. Use the same private route for conduct concerns. Do not include
credentials or publish sensitive details in public issues.

The compiler reads source/IR and bounds files and writes Alloy and optional
metadata. Treat model inputs as untrusted. Running the compiler does not invoke
Haskell or a solver; those tools belong to the development and validation workflow.
Preservation proofs concern the documented mathematical translation. They do not
establish memory safety, resistance to resource exhaustion, dependency security
or correctness of native execution.

Ordinary bugs and incorrect semantic claims belong in repository issues with the
affected revision and reproduction steps or a small counterexample. Report a
suspected security impact privately first when disclosure could expose users.
