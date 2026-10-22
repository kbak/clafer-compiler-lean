# Hygienic Alloy serialization

The serializer emits hygienic Alloy text and source maps from the independent
[target API](alloy-core.md). The [structural backend](structural-encoding.md)
produces target modules; the [native driver](cli.md) writes their text, and
[three-way comparison](comparison.md) checks actual Analyzer instances.
Successful rendering carries a reconstruction proof. Native and Analyzer
execution retain the boundaries described below.

## API, identities and mappings

`impl~compiler-alloy-serialization~1`

The public namespace is `ClaferCompiler.Backend.Alloy.Text`:

- [Names](../ClaferCompiler/Backend/Alloy/Names.lean): `Symbol`, `SourceName`,
  `Names`, `Mapping`, and `readSymbol`.
- [Print](../ClaferCompiler/Backend/Alloy/Print.lean): `render`, `Rendered`,
  `RenderError`, `anonymousNames`, and the internal unchecked `serialize` helper.
- [Parse](../ClaferCompiler/Backend/Alloy/Parse.lean): independent `parse`,
  which imports syntax and names but never the printer.

`render : CheckedModule → Names → Except RenderError (Rendered module)` is the
handoff API. A successful output contains text, a declaration map, and a proof
that parsing those exact bytes reconstructs the entire original module. Invalid
metadata reports `malformedMetadata`; failed reconstruction reports
`syntaxCorrespondence`. Neither failure returns a partial output. `serialize`
is an unchecked implementation helper, not a substitute for this checked API.
Target admission retains #8's malformed/unsafe-bound distinctions.

All identifiers are `cc` followed by a canonical decimal natural number. The
number is `4 * identity + tag`: tags 0, 1, 2 and 3 belong to signatures, fields,
lexical binder levels and reserved auxiliary identities respectively. Names are
ASCII legal identifiers and cannot be Alloy keywords, including Alloy 6's
`always`, `eventually`, `var` and other temporal keywords. Signature/field IDs
remain the target's positional identities; metadata never supplies binding.
Binders use lexical levels in text and de Bruijn indices in the target. Nested
binders have different names; siblings can reuse a name without overlapping scope.
Domains resolve in the outer environment and bodies in the extended environment.

`Names` has one optional source entry per signature/field. A source entry retains
the display name verbatim, plus either no location or a logical filename and a
valid half-open UTF-8 byte span. Repeated/shadowed names, Unicode, reserved words,
strings resembling generated identifiers, newlines and comment delimiters affect
only the sidecar. No source label, filename, comment, timestamp, private path or
diagnostic is interpolated into Alloy. Auxiliary declarations can have no source.

Mappings are ordered by emitted declaration position and identify the generated
name, symbol, optional source and exact half-open UTF-8 byte range of the name at
its declaration. Fields are grouped under their owner while preserving field IDs;
map order need not equal field-table order. This is a declaration map, not a span
for every expression/reference occurrence. The text has ASCII tokens, spaces and
LF line endings, independent of platform and hash traversal. Equal inputs produce
equal bytes and maps; changing source labels alone leaves bytes unchanged.

Covers:
- `req~compiler-alloy-text~1`

## Complete emitted grammar and correspondence

Every relation, integer and formula has explicit outer parentheses. Binary
operands retain their own parentheses, including non-associative difference,
join operands, implication and quantifier bodies. No precedence inference is
needed to reconstruct a target. There is one signature, fact or command per line.
The small parser recognizes this canonical subset, not arbitrary Alloy source:
space-separated tokens, LF-separated paragraphs, no comments or string literals.
It rejects missing grouping, unknown forms, duplicate/gapped IDs, wrong binder
levels, free variables, domain capture and additional commands.

| Target | Emitted form (operands are parenthesized) |
| --- | --- |
| Unary/binary empty | `( none )` / `( none -> none )` |
| Signature, field, bound variable | `( ccN )`, resolved in distinct identity namespaces |
| Union, intersection, difference | `( a + b )`, `( a & b )`, `( a - b )` |
| Product, join, transpose | `( a -> b )`, `( a . b )`, `( ~ a )` |
| Integer literal/cardinality | `( -8 )`, `( 7 )`, `( # a )` |
| Integer arithmetic | `( plus [ a , b ] )`, `( minus [ a , b ] )`; ordered integer operands, distinct from relational `+`/`-` |
| Truth/falsity | `( no none )`, `( some none )` |
| Relational equality/inclusion | `( a = b )`, `( a in b )` |
| `lone`, `one`, `some` predicates | `( lone a )`, `( one a )`, `( some a )` |
| `set` predicate | `( ( a ) in ( a ) )`; reflexive inclusion is a tautology, with redundant grouping retaining its canonical constructor identity |
| Integer equality/order | `( a = b )`, `( a < b )`, `( a =< b )` |
| Negation/conjunction/disjunction/implication | `( not p )`, `( p and q )`, `( p or q )`, `( p implies q )` |
| Universal/existential | `( all ccN : a \| p )`, `( some ccN : a \| p )` |
| Signature | Optional `abstract`, optional `lone`/`one`/`some`, `sig ccN`, optional `extends ccM`, field block |
| Field | `ccN : set/lone/one/some ccM`; owner comes from its signature block |
| Fact | `fact { p }`, in original fact order |
| Command | `run/check { p } for B Int , [exactly] N ccM , ...` |

`set` signature multiplicity emits no keyword. Empty field blocks and a module
without user signatures are supported. Every signature gets its original exact
or upper scope; the bitwidth is explicit, with no overall/default scope replacing
an input bound. There are no new user atoms, fields or facts. Tautological sugar
and binary `none` introduce neither arithmetic nor extra cardinality obligations.
No M2 constructor or target admission meaning changes in this task. Future #15
constructors must extend printing, independent parsing, reference correspondence,
round-trip checks and Analyzer fixtures together.

The guide is the [official Alloy reference](https://alloytools.org/spec.html),
Lexical Issues, Namespaces, Grammar, Precedence and Associativity, Signature/Field
Declarations and Commands, using the [retained reference identity](alloy-core.md#source-correspondence-and-external-boundary)
and pinned Alloy 6.2.0 distribution in the [source register](sources.md).
The pinned Haskell generator's `genRelations`, `genRelName`, `genRefName`,
`genAlloyRel` and `genConstraints` were inspected for owner/target direction,
field naming and group/count context. Their source-name conventions are not
copied. Upstream's bounded-comparison contract supplies the exact-candidate and
scope profile. New code and reference fixtures are original MIT project code.

## Parser reuse assessment

The reconstruction parser consumes the canonical Alloy output of #9. The Clafer
source-language frontend remains #16. Independence from the printer permits shared
general parser libraries; it requires independently specified recognition and
reconstruction logic, not a parser framework written from scratch.

| Candidate inspected | Fit and remaining tradeoffs |
| --- | --- |
| Pinned Lean `Std.Internal.Parsec` ([basic combinators](https://github.com/leanprover/lean4/blob/v4.35.0/src/Std/Internal/Parsec/Basic.lean), [string input](https://github.com/leanprover/lean4/blob/v4.35.0/src/Std/Internal/Parsec/String.lean)) | Used by this candidate for input, sequencing, alternatives, backtracking and repetition, without a new package dependency. Grammar and identity reconstruction remain project code. Its repetition helpers are partial and opaque to kernel computation; the successful-render proof still uses the computed result conditionally. |
| Pinned official Alloy Java parser | Already reused by the external tests for actual Alloy acceptance and normalized AST comparison. It runs outside Lean's kernel and would add Java/Alloy to the compiler runtime if used there; it cannot directly supply the current kernel reconstruction proof. |
| Pinned Haskell Clafer frontend | Its [build rules](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/src/Makefile) generate a parser with BNFC/Happy and a lexer with Alex from `clafer.cf`. This reuses established tools but recognizes Clafer source rather than Alloy output. The [Cabal file](https://github.com/gsdlab/clafer/blob/15adb2216909421bcb5022174d2d84ef2b42307c/clafer.cabal) also lists Parsec; the main frontend is generated by Happy. |
| Fold-based custom recognizer | Total list folds support kernel reduction, but require project-owned delimiter stacks and a separate binder scan/resolution pass. Parsec removes that machinery; either implementation needs independent Alloy checks for shared assumptions with the printer. |

This Parsec candidate remains subject to review. Quantifiers parse their domain
at the outer depth and their body at the extended depth, resolving binder levels
directly to de Bruijn indices. Every repeated parser consumes input on success.
Recursive expression parsing uses the line's character count as its nesting budget:
each nested expression consumes an opening parenthesis, so there is no separately
configured depth cap. Each line requires end-of-input; token boundaries and the
canonical space/LF grammar remain explicit. The implementation introduces no
project `partial` declarations, but library repetition is not a kernel-reducible
termination proof. Tests cover the finite domain below; they do not establish
universal successful renderability, better performance or official Alloy semantics.

## Proved boundary and review obligation

`proof~compiler-alloy-text-assurance~1`

`Symbol.number_injective` and `Symbol.name_injective` prove that equal generated
names imply equal identities across all four namespaces, for arbitrary natural
IDs. They use standard natural-number decimal injectivity, not bounded examples.

`render_reconstructs` proves that any successful `render` call has
`parse (serialize module.raw) = some module.raw`. `render_roundTrip` exposes the
same reconstruction guarantee for the returned text. Equality includes all raw
instruction lists, signature flags/parents, field identities/order/multiplicities,
facts, de Bruijn indices, command polarity, scopes and bitwidth; there is no
lossy normalization or source/target satisfaction hypothesis in this equation.

The proof method is **translation validation**: an independent parser
reconstructs the output and decidable structural equality is checked before
success. It is not a structural-induction theorem that `render` always succeeds
for every checked module. Successful coverage is separately exercised by the
finite test domain below; malformed metadata and correspondence failure remain
explicit API errors. Review must assess this successful-render assurance boundary
against issue #9's round-trip criterion before acceptance, rather than treating
finite successful examples as a totality proof.

The parser combines standard Parsec machinery with its own expression/declaration
grammar, symbol-table reconstruction and lexical resolution. It does not call `serialize` or inspect
input targets. Nonetheless it is project code: a proof about it alone does not
prove Alloy grammar/meaning correspondence. Reflexive `set` sugar and concrete
syntax correspondence are tested against the Analyzer, not claimed as a proved
Analyzer semantics theorem. #8's independent model remains the semantic authority
for compiler proofs. Native Lean/C execution, the external parser,
Analyzer translation, SAT4J and later external decoding remain trust boundaries.

Covers:
- `req~compiler-alloy-text~1`

## Required tests and evidence

`utest~compiler-alloy-text-integration~1`

[AlloyText](../tests/AlloyText.lean) and its [native harness](../tests/AlloyTextOracle.lean)
exercise 36 constructor/declaration/binding/bounds cases and a finite exhaustive
156-case relation/formula generator. Every member must pass admission and checked
rendering; failures are never discarded. They test round trips, repeatability,
metadata-independent bytes, original names/spans, malformed metadata, 4,000
identity/name decodings and twenty rejecting parser mutations. The latter include
full-consumption, token-boundary, unmatched-delimiter and malformed-list cases
that exercise Parsec backtracking and committed failures. Additional native round
trips cover negation depths 0, 1, 16 and 128, and a module with 32 signatures/scopes,
64 fields and 32 facts. These tests retain explicit failure on rejected inputs.

[The regression](../tests/test_alloy_text.py) links and runs actual native code,
checks every declaration-map byte slice, parses all 192 outputs with the real
pinned Analyzer, and compares 36 normalized ASTs with [independently authored
reference text](../tests/fixtures/alloy-text/references.json). Normalization in
[AlloyTextBridge](../scripts/oracles/AlloyTextBridge.java) removes no-op grouping
and alpha-renames bound variables; it retains operator order, declaration endpoints,
multiplicities, command polarity and scope details. Unhandled AST nodes fail.

Twenty-six generated modules additionally receive an independently authored
four-atom exact-candidate pin. Actual SAT/UNSAT results must equal the independent
Lean target evaluator's results. Both truth values occur. Valid Alloy mutations
remove essential difference parentheses or alias a reference; their normalized
ASTs must differ. These tests supplement #8's independent target comparisons and
the #6 Haskell/upstream oracle suite; they do not claim source compiler correctness.

The mandatory check retains emitted text/maps, reference and mutated files,
source copies/hashes, native build/link/run commands, actual JAR/Java identity,
normalized ASTs, all effective solver options, outcomes and SAT XML witnesses in
an external `CLAFER_ORACLE_EVIDENCE` bundle. Missing tools, timeout, parser failure,
undefined Lean observation, normalization errors or mismatch fail the check.
Replay the retained commands with the same source and pinned dependencies.
IntentBond checks and kernel/axiom replay remain mandatory; exit 4 leaves semantic
review pending. No scope, coverage, dependency pin or publication setting changes.

Covers:
- `req~compiler-alloy-text~1`
