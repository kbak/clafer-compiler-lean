# Authored static source parser

`ClaferCompiler.Frontend.parse : String → String → Except Diagnostic Document`
accepts a logical filename and original UTF-8 source. The [source pipeline](pipeline.md)
uses this in-memory API before [resolution/defaulting](resolution.md) and
[constraint elaboration](constraints.md). Successful parsing does not establish
semantic validity, M1 admission, satisfiability or compiler correctness.

## Reuse and representation

[Lexer](../ClaferCompiler/Frontend/Lexer.lean) reuses the pinned Lean 4.35.0
`Std.Internal.Parsec` primitives, alternatives and UTF-8 `String.Pos` cursor.
[Parser](../ClaferCompiler/Frontend/Parser.lean) uses the standard `StateT`/`Except`
types. String scanning and comment searches reuse the standard string library.
Parser repetition uses standard-library `Nat.repeat` to build a finite grammar
approximation, and standard loops/folds consume tokens and test observations.
This follows the target core's existing use of standard folds: Lean generates
unsafe native helpers even for ordinary recursive project definitions and recursive
`Repr`/`BEq` derivations. Standard `Parsec.many` also uses partial recursion. The
project audit prohibits these project helpers and remains unchanged. The Clafer
layout rules and precedence table are language-specific. No parser framework, Unicode table, Haskell runtime, or new
package dependency is introduced. These internal Std APIs are pinned by the
existing toolchain and must be rechecked on upgrades. The existing
[Alloy text parser](../ClaferCompiler/Backend/Alloy/Parse.lean) parses emitted target
syntax, with different AST and whitespace assumptions; the source frontend reuses
the same Std primitives without depending on the target grammar.

[Surface](../ClaferCompiler/Frontend/Surface.lean) reuses the IR's `SourceSpan` and
malformed/unsupported categories. `Document` retains the complete original source,
ordered declaration/constraint tree and logical filename. `Header` retains the
name, authored abstract/use token, optional group/cardinality, superclass and
reference arrow/target. Numeric cardinalities contain both bounds and the original
tokens; `none` is omission, not an inferred default. `xor` and `1..1` therefore stay
distinct. Set and bag arrows stay distinct. References remain names; no IDs,
lookups, inherited views, coercions or effective defaults are invented.

`Expr` contains names, natural integer tokens, unary/binary operators, explicit
parentheses and single-binder quantifiers. Minus remains a unary node. All nodes
have source spans, and operators/binder names retain their tokens. The two-word
`not in` operator has the canonical label `not in`; its span and retained source
recover the original inter-word whitespace/comments. Repeated and
shadowed names are preserved; typing and scope are intentionally unchecked.
Constraints retain every ordered body and their containing declaration occurrence.
Comments remain recoverable from `Document.source`, rather than becoming semantic
nodes. No input is rewritten or Unicode-normalized.

## Independent grammar

This grammar describes the accepted syntax independently of the implementation.
It specializes the adopted [surface whitelist](architecture.md#m2-surface-forms-and-explicit-exclusions).
Quoted tokens are literal. Braces in the following EBNF mean repetition only when
unquoted; `?` means optional. Layout supplies the same `body` tree as explicit
braces. No semantic meaning is assigned by these productions.

```text
module      = { element }
element     = declaration | use | constraint
declaration = "abstract"? group? name (":" name)? reference? card? body?
use         = "`" name card? body?
reference   = ("->" | "->>") name
group       = "xor" | "or" | "mux" | "opt" | interval
card        = "?" | "+" | "*" | decimal | interval
interval    = decimal ".." (decimal | "*")
body        = "{" { element } "}" | indented-elements
constraint  = "[" { expression } "]"
atom        = name | decimal | "(" expression ")"
quantifier  = "some" | "no" | "not" | "one" | "lone"
binder      = ("all" | "some" | "no" | "not") name ":" E21 "|" E1
```

Names start with ASCII `A–Z`, `a–z`, or a Latin-1 code point in `U+00C0–U+00FF`
other than `U+00D7` and `U+00F7`. Continuations also allow ASCII digits, underscore
and apostrophe. Decimal literals contain one or more ASCII digits; spelling,
including leading zeroes, is retained. This is the pinned generated Alex class,
not all Unicode letters. Latin-1 names such as `Café` are supported; Greek, CJK,
combining accents and non-ASCII digits are rejected. `integer`, `int`, `this`,
`parent`, and other unreserved names are resolved by the
[declaration](resolution.md) and [constraint](constraints.md) elaborators. The reserved
words are exactly the selected keywords and excluded keyword inventory in the
lexer; in particular `U`, `W`, `F`, `G` and `X` are temporal tokens.

Space, tab, LF and CR are whitespace; CRLF counts as one newline without changing
original offsets. Tabs before the first token of a line are malformed. `//` runs
to LF or EOF; `/* ... */` is non-nesting and must close. Blank/comment-only lines
do not create layout elements. Leading block comments do not contribute to logical
indentation; display columns still count their characters. Indentation is the
leading spaces before the first token or block comment. A layout module starts at
column one. A greater indentation after a declaration opens children; dedents must
return to an existing sibling level. Within explicit braces, indentation has no
structural meaning. Sibling declarations must begin on separate lines, including
in braces; hard constraints may be adjacent or share a declaration's line.
Headers can continue across equally indented lines or across whitespace inside
explicit braces. Greater indentation cannot interrupt a header's required syntax.
The pinned grammar greedily consumes a following cardinality: `A` followed by
`1..* B` at the same indentation gives A card `1..*` and a separate B with no group;
indenting the second line instead gives A a child B with group `1..*`.
Invalid numeric intervals are malformed; a valid but impossible group is retained.

Expression precedence uses the pinned grammar's numbered levels. Operators at
each binary level associate **left**, including implication and equivalence.
Unlisted levels are coercions to the next tighter level. Parentheses admit any
expression at the atom level.

| Level (low to high) | Production |
| --- | --- |
| 1 | single-binder quantifiers; domain is E21, body E1 |
| 3 | `<=>` |
| 4 | `=>` |
| 5 | `\|\|` |
| 6 | `xor` |
| 7 | `&&` |
| 11 | prefix `!`, operand E11 |
| 15 | `=`, `!=`, `<`, `>`, `<=`, `>=`, `in`, `not in` |
| 16 | collection `some`, `no`, `not`, `one`, `lone`, operand E20 |
| 17 | `+`, `-` |
| 20 | prefix `#`, `-`, operand E21 |
| 23 | `++` |
| 24 | `--` |
| 25 | `**` |
| 26 | `.` |
| 27 | atoms |

For example, `a => b => c` means `(a => b) => c`, `!a = b` means `!(a = b)`,
and `a + b ++ c` means `a + (b ++ c)`. `not E` is a collection test, distinct
from Boolean `!E`. Collection tests cannot be unparenthesized arithmetic operands;
`[a + some b]` and `[some a + b]` are malformed. Because hard bodies have no
separator, `[one a - b]` contains two bodies: `one a` and unary `-b`; parentheses
can instead make a collection test an arithmetic operand for later type checking. Multiple expression bodies inside brackets remain
separate entries; [constraint elaboration](constraints.md) preserves each occurrence
for conjunction by the encoder.

## Diagnostics and exclusions

`Diagnostic` has version 1, stable code, phase (`lexer` or `parser`), category,
message, primary span, one-based line/scalar column, and related-span array.
Primary spans are zero-based half-open UTF-8 byte offsets in the original file;
EOF is a zero-width span. The parser reports one deterministic error, with no
partial successful document. This API does not serialize diagnostics or assign
process exits. Exact message wording is not the stability contract.

| Code | Category / meaning |
| --- | --- |
| `lexer.character`, `lexer.comment`, `lexer.indentation-tab` | malformed character, unclosed comment, or indentation tab |
| `lexer.excluded`, `lexer.directive`, `lexer.real` | unsupported keyword/operator/escape, directive, or real/double literal |
| `parser.expected`, `parser.name`, `parser.integer`, `parser.expression` | malformed/missing required syntax |
| `parser.interval`, `parser.group`, `parser.layout`, `parser.precedence` | malformed interval, group, layout or operand placement |
| `parser.binder` | malformed missing `all` binder; unsupported `one`/`lone` binder |
| `parser.type-expression`, `parser.initializer`, `parser.arithmetic` | unsupported type expression, initializer or multiplication |
| `lexer.progress`, `parser.progress` | malformed result from exhausted internal progress bound; a valid-input occurrence is a parser defect |

Recognized excluded primitives, operators, temporal keywords/transitions, assertions,
goals, enums, module-qualified names, multi-binders, disjoint binders, initializers,
backend escapes and source option directives fail explicitly. No desugaring erases
them. Lexical exclusions are checked before grammatical analysis, so a later
excluded token can take priority over an earlier grammar error. Missing syntax
does not count as evidence for an otherwise unsupported complete construct.

## Sources and comparison

The [source register](sources.md) pins the paper's Appendix 3/Figure 27 and
Appendix 4/Figure 28, upstream `Syntax`/`Typing` (S2/S4), and Haskell grammar (S5).
The Haskell commit is `6750e6f591b2131549122c13dee94d3d2257eaea`; inspected files:

| File | SHA-256 | Correspondence |
| --- | --- | --- |
| `src/clafer.cf` | `14176e1c241d7d44d368535ff1664b75da39a054ee32f880456a4b7291921a2f` | retained Module/Element/Clafer/Card/GCard/Exp productions, tokens, precedence |
| `src/Language/Clafer/Front/LexClafer.x` | `d888bfe16746efd3ef02f21e8929e044974f3ee6ff9f8c5473b74d73bef83b7e` | actual Latin-1 character classes and longest-match tokens |
| `src/Language/Clafer.hs` | `54fd365648eb38f44e9ceb5d4e3f35bcfdcc3f315314d2a7bc9978d9f4954b4b` | public parse/layout boundary and same-line sibling guard |

No Haskell or paper text/code/fixtures are redistributed. New implementation and
fixtures are original MIT project code. Lean's Apache-2.0 implementation is
imported through the existing toolchain, not copied. External Haskell notices
remain in the [oracle tools bundle](oracles.md).

[Native tests](../tests/ParserNative.lean) and [Python tests](../tests/test_parser.py)
reuse the existing unittest runner, native linking pattern, seeded standard-library
generators, and hash-checked Haskell capture adapter. Finite exhaustive properties
cover every two-operator precedence pairing and layout/braces equivalence for
depths 1–16 and widths 1–4. Tests also check authored provenance, repeated/shadowed
names, comments, CRLF, Unicode byte spans, every excluded production family,
malformed mutations and arbitrary input termination. These are test domains, not
language limits. The parser has no backend dependency; the
[source pipeline](pipeline.md) connects it to elaboration and compilation.

The reference capture's `unsupported` source audit occurs **after** `C.parse`;
it can establish reference parse success for M2 expressions even though the M1
capture rejects them. `ParseErr` is separated from later semantic/type failures.
Captured structural cases compare declaration and set/bag constructor inventories.
Full normalized Haskell expression trees are not exposed by that adapter; exact
expression trees are instead checked against the independent precedence grammar.
The differential test retains each source, raw output, identity and observation
outside source under `CLAFER_ORACLE_EVIDENCE` (or a fresh system temporary directory).

Reviewed profile differences remain explicit: Haskell accepts indentation tabs,
some inconsistent dedents, multiplication and string references; this project's
adopted contract rejects them. On `A {`, `[a`, and `A ->`, the pinned Haskell
parser crashes with EOF; the test records **tool error**, not parse rejection or
agreement. This parser returns malformed diagnostics. The retained oracle evidence
records these differences without changing upstream meanings or dependency pins.

## Assurance boundary and handoff

There are no parser correctness theorems. Lean checks the implementation's total
definitions and the normal project kernel/axiom audit still applies. The grammar
to parser/AST correspondence, sufficient fuel, diagnostic completeness and native
execution remain **tested, unproved** boundaries. No `sorry`, admission axiom or
claim of complete Haskell compatibility is used. The standard parser primitives,
UTF-8 runtime and native C/IO remain part of the execution trust boundary.

The [resolver](resolution.md) receives the complete `Document`, including source
and authored tokens, and establishes resolution/default rules independently.
[Constraint elaboration](constraints.md) handles every expression and attachment
occurrence, including typing, coercions and meaning. The [source pipeline](pipeline.md)
retains this unproved parsing boundary in its composed assurance statement.
IntentBond exit 4 leaves semantic review pending; acceptance and dependent intake
require review.

## Trace artifacts

`impl~compiler-authored-parser~1`

[Surface types](../ClaferCompiler/Frontend/Surface.lean),
[lexing](../ClaferCompiler/Frontend/Lexer.lean), and
[parsing](../ClaferCompiler/Frontend/Parser.lean) implement the authored grammar,
layout, precedence and explicit rejection boundary described above. They reuse
Std parser primitives and IR spans/categories. No semantic elaboration is claimed.

Covers:
- `req~compiler-parser~1`

`impl~compiler-parser-diagnostics~1`

`Diagnostic`, `lexError` and `reject` in those modules implement the versioned
source diagnostic and its original-byte/line/column locations. The result returns
one error rather than a partial document; serialization remains outside this API.

Covers:
- `req~compiler-diagnostics~1`

`utest~compiler-parser-native~1`

[Native assertions](../tests/ParserNative.lean) check authored flags, numeric
values, spelling, omission, reference arrows, spans and source retention. The
[Python runner](../tests/test_parser.py) links and executes them and checks the
independent expected trees, rejection corpus, generated properties and actual
pinned Haskell observations described above. The shared check discovers this test;
missing tools and failed native/harness operations fail rather than skip.

Covers:
- `req~compiler-parser~1`
- `req~compiler-diagnostics~1`
