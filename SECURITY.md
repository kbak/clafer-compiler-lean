# Security

This is a private research compiler with a native command-line interface and no
supported stable releases. Fixes apply to `main`. Qualification archives are
private review artifacts, not supported releases.

Report sensitive issues to `@kbak` through the shared
[Clafer Semantics private reporting form](https://github.com/kbak/clafer-semantics/security/advisories/new).
Identify `clafer-compiler-lean` as the affected project and include the revision,
platform, impact and a minimal reproducer. The form requires a GitHub account;
private reporting is enabled on that repository. Use the same private route for
conduct concerns. Do not include credentials or publish sensitive details in
public issues. This compiler repository remains private.

The compiler reads source/IR and bounds files and writes Alloy and optional
metadata. Treat model inputs as untrusted. Running the compiler does not invoke
Haskell or a solver; those tools belong to the development and validation workflow.
Preservation proofs concern the documented mathematical translation. They do not
establish memory safety, resistance to resource exhaustion, dependency security
or correctness of native execution.

Ordinary bugs and incorrect semantic claims belong in repository issues with the
affected revision and reproduction steps or a small counterexample. Report a
suspected security impact privately first when disclosure could expose users.
