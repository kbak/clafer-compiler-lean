# Executable structural IR

The separate [behavioral IR](behavioral-ir.md) reuses these guarded declarations
under explicit temporal admission; the static interchange remains unchanged.

The M1 in-memory IR exposes executable declaration tables and admission checks.
Its runtime code imports only `Std`; its proof interpretation imports the pinned
upstream admission module. The [native file/JSON driver](cli.md) composes admission
with the [structural backend](structural-encoding.md) and serializer. Source
parsing, defaulting and candidate satisfaction have separate contracts.

## Data and entrypoints

`ClaferCompiler.IR.Structural` in [Structural.lean](../ClaferCompiler/IR/Structural.lean)
provides `Declaration`, `Bounds`, `Reference`, `Origin`, `SourceSpan`, `Authored`,
`Core`, `Certificate`, `Raw`, `Validated`, `Diagnostic` and `ReferenceOccurrence`.

A `Core n` stores a `Vector` of exactly `n` declarations and a finite root index.
The vector has an executable array representation. IDs are nonnegative integers,
separate from names and internal indices; duplicate display names are valid.
Parent, super and reference targets are checked `Fin n` indices. `Raw` instead
uses declaration IDs at every edge and arrays at the boundary. `lookup` performs
a terminating finite scan. `validateRaw` rejects duplicate IDs, bad byte spans,
missing roots, certificate lengths and dangling edges before core admission.
Resolution preserves input order and binds by ID, including forward edges.
Neither reference cycles nor repeated targets trigger recursive traversal or merging.
`ReferenceOccurrence` separately retains declaration, head-object, owner-object and
target-object IDs; two bag heads at the same owner/target remain distinct records.
Candidate validation and set/bag satisfaction are checked by the
[comparison layer](comparison.md), separately from IR admission.

`validate : Core n → Certificate n → Except Diagnostic (Validated n)` is the
proved admission boundary. The certificate contains parent/super ranks and an
unused-abstract flag per declaration. Every parent/super edge must strictly decrease
its rank. Unused flags must identify only abstract declarations and propagate to
all subtypes; a zero-bound abstract requires that flag. This is the exact upstream
checked-certificate interface: every supported well-formed core has a suitable
certificate. Bad auxiliary data is an input failure, never evidence of UNSAT.
Ranks are explicit in the v1 interchange. The [source resolver](resolution.md)
computes ranks for authored input; its `toM1` conversion applies these guards.

Core guards enforce unique IDs, the unique concrete basic synthetic root, valid
intervals, rank descent and parentless abstractness. Support guards enforce all
[exact M1 conditions](architecture.md#exact-m1-admission), including leaf abstracts,
abstract-only super targets, basic subtypes, user reference targets, unused zero
abstract chains and positive group lower bounds having a child declaration.
`validate` returns the original table and certificate with proofs of those guards.
There is no satisfaction premise. A well-formed but impossible group or local
bound remains admissible. Primitive origins are represented so they can be rejected
as unsupported; constraints, behavior and M2 inherited forms are not enabled.

Effective local/group bounds and abstractness are authoritative at this boundary.
The optional `Authored` record preserves supplied abstract/local/group observations
as opaque metadata; `none` explicitly means effective-only provenance. No authored
value is inferred, checked for default agreement, or interpreted into the source
AST. Keyword provenance and authored elaboration are retained by the separate
[in-memory frontend candidate](resolution.md); the v1 interchange profile is unchanged. The
effective-core interpretation is sufficient for M1; building
an AST here would invent missing authored/default information.

## Resolved structural normalization

[`IR.Structural.Normalization`](../ClaferCompiler/IR/StructuralNormalization.lean)
provides a library pass over the existing resolved tables. `normalize` sets
`localBounds` to `0..*` exactly when a declaration is parentless and abstract.
For example, an admitted unused abstract chain with `0..0` slots becomes an
unrestricted chain while retaining the original checked `unused` flags. Its
normal form is the independently stated `NormalForm` field predicate.
This canonicalizes one semantically irrelevant slot, not all equivalent models.

`normalize : Core n → Core n` is a pure projection and does not admit its input.
`admitted : Validated n → Validated n` is total and preserves the exact certificate.
`checked : Core n → Certificate n → Except Diagnostic (Validated n)` first runs
the existing `validate` on the original input. It preserves every validation
error, so a bad abstract interval or missing unused certificate cannot disappear
through rewriting. Raw IDs, metadata spans, version/profile and JSON decoding
retain their existing validation boundaries. The typed-core API does not add
checks beyond `validate`.

The pass retains declaration count/order, identities and names, root, origins,
parent/super/reference edges, reference mode, abstractness, group bounds, source
spans and authored metadata. Parented local bounds and the concrete root's local
slot are unchanged. An authored `0..0` observation may therefore coexist with a
normalized effective `0..*` slot; the authored record remains opaque provenance.
Full structural equality includes that metadata. No fields are discarded for
comparison and no byte-equality, source-parser or JSON round-trip claim is made.
Solver scopes and options are not inputs to this library pass. Existing ID-keyed
scopes need no remapping because IDs and declaration order are unchanged.

The [source resolver](resolution.md) reuses `normalize` in `m1Core`.
`Frontend.Resolution.m1Core_eq` proves exact equality with its previous field
projection. That source conversion continues to check source correspondence
before projection and exact M1 admission afterward. It does not use the new
checked typed-M1 API, which would reject some pre-projection source slots.
The source conversion's domain and diagnostics remain unchanged.

### Reuse and evidence

The implementation extracts the existing `m1Core` rule and reuses `Core`,
`Declaration`, `Certificate`, `Validated`, `validate`, and Std vector mapping
and equality. Pinned upstream `Configuration.Multiplicities` constrains only
actual parent fibers; `StructuralSatisfies` supplies independent whole-model
meaning. Existing native fixtures, linking and unittest infrastructure supply
runtime coverage. Alloy printers handle a different output language; Haskell
explicit-output qualification cannot establish this Lean IR theorem. No new
library, runtime or license dependency is introduced; existing MIT code and
Apache-2.0 Lean primitives suffice.

`impl~compiler-resolved-normalization~1`

The runtime module above implements `NormalForm`, `normalize`, `admitted` and
`checked`; `Frontend.Resolution.m1Core` uses the same projection.

Covers:
- `req~compiler-resolved-normalization~1`

`proof~compiler-resolved-normalization~1`

The runtime module proves `normal_form`, `fixed` and `idempotent` for every
`Core n`. `declaration_preserves`, `get_normalize` and `root_preserved` expose
exact unchanged data. `unchanged` preserves whole parented or concrete rows,
and `admitted_certificate` preserves certificate data. `core_checked` and
`support_checked` retain the original
certificate guards. `admitted_fixed`, `admitted_idempotent`, `checked_admitted`,
`checked_fixed` and `checked_again` establish successful fixed points on admitted
inputs. `checked_success` gives normal form and unchanged successful rechecking
for every successful checked result; `checked_error` preserves every original
typed validation error.

The [normalization bridge](../ClaferCompiler/SemanticsBridge/StructuralNormalization.lean)
proves `multiplicities_iff` and `satisfies_iff` for the same upstream configuration
in both directions, without finiteness, admission or satisfaction premises.
`admitted_domain` supplies upstream well-formedness and support for validated
output. First-pass semantic preservation is independent of idempotence. These
proofs do not extend behavioral source normalization or prove native execution.

Covers:
- `req~compiler-resolved-normalization~1`

`utest~compiler-resolved-normalization~1`

[Kernel witnesses](../tests/StructuralNormalization.lean) and
[native tests](../tests/StructuralNormalizationNative.lean) check a nontrivial
unused abstract chain with arbitrary IDs, a nonzero root index, repeated and
punctuation-heavy names, set/bag references and retained provenance. Independent
expected output checks the first pass; the second must preserve the entire core
and certificate. Invalid interval and missing-unused witnesses would pass if
rewriting preceded admission; the checked API must reject them. Tests preserve
parented abstract bounds in the pure projection and reuse existing typed
admission fixtures. The [native runner](../tests/test_structural_ir.py) executes
these checks in the mandatory regression suite. Source parsing and native
execution retain their existing tested boundaries.

Covers:
- `req~compiler-resolved-normalization~1`

## Developer interchange contract

[clafer-ir-1.schema.json](../schemas/clafer-ir-1.schema.json) specifies the JSON
shape for `version: "clafer-ir/1"`, `profile: "m1-effective"`. The selected
[driver decoder](../ClaferCompiler/Driver/Decode.lean) implements
this contract with strict lexical admission. The in-memory
`validateDocument version profile raw` selects this version/profile on already
decoded data and rejects others deterministically.

All fields listed in the schema are required and objects are closed to additional
keys. IDs, bounds, ranks and byte offsets are natural-number JSON tokens: reject
booleans, strings, negative values, fractions and exponent notation in these slots.
A decoder must reject duplicate keys at every depth *before* constructing an object
map, including escape-equivalent keys; JSON Schema cannot detect that loss of
information. Reject malformed UTF-8, trailing input and invalid escape/surrogate
sequences. Unknown semantic fields/constructors must never be discarded. Unknown
version/profile or recognized excluded features are unsupported; invalid field
shapes, unknown fields and duplicate keys are malformed. These lexical/decoder
obligations are not certified by the in-memory Lean admission theorems.

`declarations` is ordered. Each object has `id`, `name`, `origin`, `parent`, `super`,
`reference`, `isAbstract`, `localBounds`, `groupBounds`, `source` and `authored`.
Origins are `root`, `user`, `integer`, `string`, `boolean`; only the first two pass
M1 support. Absent parent/super use `null`. References are `{ "kind": "basic" }`
or `{ "kind": "set" | "bag", "target": ID }`. Bounds use `lower` and `upper`,
with `"*"` as the unbounded upper marker. Infinity is never an integer.
The parallel `parentRanks`, `superRanks`, `unused` arrays have exactly one entry
per declaration in the same order. The `root` field is a declaration ID.

`source: null` records no source location. Otherwise `file` is a logical filename
and `startByte`, `endByte` are zero-based half-open UTF-8 offsets in original bytes,
with start ≤ end; no source buffer is available here to check the upper endpoint.
Unicode spelling and CRLF offsets are preserved. `authored: null` is effective-only;
a supplied record retains the fields shown in the schema without elaborating them.
Source locations and names never substitute for IDs. Haskell JSON is a separate
format and requires the [receipt-aware oracle adapter](oracles.md).

A complete root-only document is:

```json
{
  "version": "clafer-ir/1", "profile": "m1-effective", "root": 100,
  "declarations": [{
    "id": 100, "name": "root", "origin": "root", "parent": null, "super": null,
    "reference": {"kind": "basic"}, "isAbstract": false,
    "localBounds": {"lower": 0, "upper": "*"},
    "groupBounds": {"lower": 0, "upper": "*"}, "source": null, "authored": null
  }],
  "parentRanks": [0], "superRanks": [0], "unused": [false]
}
```

## Diagnostics

The API returns one deterministic first failure. Priority is version, profile,
duplicate IDs, first invalid span in declaration order, missing root, parent/super/
unused certificate length, first unresolved declaration (parent, super, reference
order), core guards, then support guards. Core/support aggregate failures use the
empty JSON pointer (the document); dangling edges identify the declaration array
position and its ID. No source span is invented. No outcome is SAT or UNSAT.

| Code | Category | Meaning |
| --- | --- | --- |
| `ir.version`, `ir.profile` | Unsupported | Unrecognized version/profile |
| `ir.duplicate-id`, `ir.missing-root`, `ir.dangling-id` | Malformed | Invalid identity/binding |
| `ir.invalid-span`, `ir.certificate-length` | Malformed | Invalid metadata or auxiliary array shape |
| `ir.invalid-core-or-ranks` | Malformed | Failed core or supplied rank checks |
| `ir.unsupported-or-invalid-certificate` | Unsupported | Failed support or unused certificate checks |

The [diagnostic serializer](cli.md) wraps these payloads with the architecture's
version, phase (`admission`), human message and related-location fields. Codes and
category meanings are stable within v1; English rendering is not fixed here.

## Implementation trace

`impl~compiler-ir-table~1`

The runtime file above implements `lookup`, `resolveDeclaration`, `validateRaw`,
`validateDocument`, `coreChecks`, `supportChecks` and `validate`. Arrays/vectors and
finite decidable quantifiers terminate. Worst-case scans are quadratic in declaration
count; this API makes no performance or resource bound claim. The JSON schema and
this document supply the interchange/handoff specification.

Covers:
- `req~compiler-ir~1`

## Proof trace and assumptions

`proof~compiler-ir-admission~1`

[The bridge](../ClaferCompiler/SemanticsBridge/Structural.lean) defines `interpret`
and `certificate`; no source satisfaction is defined downstream. In namespace
`ClaferCompiler.SemanticsBridge.Structural`:

- `coreChecks_iff`, `supportChecks_iff` identify the executable guards with upstream
  `Clafer.Verification.coreChecks` and `supportChecks`, in both directions.
- `validated_domain` and `validateRaw_domain` supply upstream `WellFormed` and
  `Supported` from validated values. `validate_success_iff` characterizes success.
- `admission_complete` and `admission_iff` prove existence of successful admission
  exactly when the interpreted core is well-formed and supported, using upstream
  `certificate_exists`. Completeness quantifies over certificates; it does not
  claim acceptance of an arbitrary incorrect supplied certificate.
- `validate_preserves` proves successful typed admission returns the entire original
  core and certificate, including metadata. `interpret_fields` gives all semantic
  field equations (root, IDs, names, origins, parent/super/reference, abstractness,
  local/group bounds). `lookup_sound` and `lookup_complete` prove lookup identity;
  completeness assumes unique IDs, not unique names.
- `resolveId_roundtrip`, `resolveOption_roundtrip`, `resolveReference_roundtrip`
  and `resolveDeclaration_roundtrip` prove that successful resolution followed by
  replacing indices with original IDs recovers every declaration field, including
  authored/source metadata. No uniqueness assumption is needed for this direction.

No source-model satisfaction or compiler-correctness premise occurs. Theorems use
only the standard logical axioms permitted by the build audit, no project axioms
or proof placeholders. The raw-array resolver is native-tested and each declaration has the round-trip
proof above; a full-document JSON decode/re-encode theorem is not claimed. Authored
metadata/source spans have no counterpart in the effective-core semantics and are
preserved in the compiler table, not invented upstream. Candidate satisfaction,
Alloy translation and compiler correctness remain in their owning tasks.

Covers:
- `req~compiler-ir~1`

## Test trace and trust

`utest~compiler-ir-regressions~1`

[Kernel witnesses](../tests/Structural.lean) check root-only and cyclic-reference
tables, duplicate-ID rejection, name irrelevance and an actual upstream-domain
witness. [Native fixtures](../tests/StructuralNative.lean) exercise 28 positive/
negative raw cases, version/profile rejection, binding and separate bag-head data.
The [Python runner](../tests/test_structural_ir.py) builds their C objects, links a
fresh temporary IO harness with `leanc`, and executes it without Haskell, Alloy or
upstream semantic code in the runtime import closure. The harness is tooling; native
execution trusts Lean code generation, the C toolchain/runtime and OS. This native
check is included in the mandatory regression runner. All owned Lean declarations
also undergo the existing axiom audit and kernel replay. Scope policy is unchanged.

Covers:
- `req~compiler-ir~1`
