# Oracle fixture inventory

`inventory.json` lists immutable source paths, hashes, MIT notice locations,
categories, explicit per-UID bounds and expected admission. `semantics` origins
resolve against the pinned Lake dependency; `compiler` origins resolve against
this repository. The four local sources are original MIT-licensed examples under
the repository [license](../../../LICENSE).

No generated receipts, solver results or machine-specific paths belong here.
See the [oracle contract](../../../docs/oracles.md) for admitted versus unsupported
cases and the distinction between tested behavior and proved properties.
