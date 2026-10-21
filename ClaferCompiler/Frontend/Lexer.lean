module

public import ClaferCompiler.Frontend.Surface
public import Std.Internal.Parsec.String
public import Init.Data.String.Search

@[expose] public section
namespace ClaferCompiler.Frontend
open Std.Internal Parsec Parsec.String

-- Requirement: compiler-parser; trace artifacts are in docs/parser.md.
/-- BNFC/Alex's pinned Latin-1 letter class, not ASCII or all Unicode letters. -/
def isLetter (c : Char) : Bool :=
  c.isAlpha || (192 ≤ c.toNat && c.toNat ≤ 255 && c != '×' && c != '÷')

def isNameRest (c : Char) : Bool := isLetter c || c.isDigit || c == '_' || c == '\''

def scanWhile (p : Char → Bool) {s : String} (pos : s.Pos) : s.Pos :=
  String.Pos.ofSliceFrom ((s.sliceFrom pos).skipPrefixWhile p)

/-- Reuse total standard-library string scanning; Parsec.many is partial. -/
def takeWhile (p : Char → Bool) : Parser String := fun it =>
  let stop := scanWhile p it.2
  .success ⟨it.1, stop⟩ (it.1.slice! it.2 stop).copy

def word : Parser String := do
  let first ← satisfy isLetter
  return String.singleton first ++ (← takeWhile isNameRest)

def number : Parser String := takeWhile Char.isDigit

def symbols : List String :=
  ["[alloy|", "[choco|", "-->>", "]->>", "<=>", "->>", "-->", "]->", "-[",
   "->", "..", "++", "--", "**", "&&", "||", "=>", "!=", "<=", ">=",
   "<:", ":>", ":=", "<<", ">>", "{", "}", "[", "]", "(", ")", ":",
   "?", "+", "*", "`", ".", "!", "=", "<", ">", "-", "#", "|", ";",
   ",", "&", "/", "%", "\\", "\""]

def symbol : Parser String :=
  symbols.foldr (fun s rest => pstring s <|> rest) (fail "unrecognized character")

def atom : Parser String := do
  let c ← peek?
  match c with
  | some c => if isLetter c then word else if c.isDigit then number else symbol
  | none => fail "unexpected end of input"

def excludedWords : List String :=
  ["enum", "string", "real", "double", "bool", "boolean", "initial", "final",
   "finalref", "finaltarget", "assert", "min", "max", "minimize", "maximize",
   "sum", "product", "if", "then", "else", "let", "disj", "never", "sometime",
   "lonce", "always", "must", "precede", "follow", "initially", "finally", "U",
   "until", "W", "weakuntil", "F", "eventually", "G", "globally", "X", "next",
   "before", "after", "between", "and"]

def excludedSymbols : List String :=
  ["[alloy|", "[choco|", "-->>", "]->>", "-->", "]->", "-[", "<:", ":>",
   ":=", "<<", ">>", ";", ",", "&", "/", "%", "\\", "\""]

def reservedWords : List String :=
  excludedWords ++ ["abstract", "xor", "or", "mux", "opt", "all", "some", "no",
    "not", "one", "lone", "in"]

def isName (t : Token) : Bool :=
  t.text.toList.head?.any isLetter && !reservedWords.contains t.text

def advance (line column : Nat) (leading : Bool) (text : String) : Nat × Nat × Bool :=
  text.foldl (fun (l, c, b) ch =>
    if ch == '\n' then (l + 1, 1, true)
    else if ch == '\r' then (l, c, b)
    else (l, c + 1, b && (ch == ' ' || ch == '\t'))) (line, column, leading)

def blockEnd {s : String} (pos : s.Pos) : Option s.Pos :=
  (pos.find? "*/").map (·.nextn 2)

-- Requirement: compiler-diagnostics; trace artifacts are in docs/parser.md.
def lexError (file : String) (start stop line column : Nat)
    (category : Category) (code message : String) : Diagnostic :=
  { code, phase := "lexer", category, message,
    primary := ⟨file, start, stop⟩, line, column }

structure LexerState where
  cursor : Sigma String.Pos
  line : Nat := 1
  column : Nat := 1
  leading : Bool := true
  indent : Nat := 0
  out : Array Token := #[]
  done : Bool := false

def lexStep (file : String) (state : LexerState) : Except Diagnostic LexerState := do
  let ⟨it, line, col, leading, indent, out, _⟩ := state
  let start := it.2.offset.byteIdx
  if it.2.IsAtEnd then
    return { state with done := true, out := out.push ⟨"", ⟨file, start, start⟩, line, col, indent + 1⟩ }
  let rest := it.1.sliceFrom it.2
  if rest.startsWith "//#" then
    throw (lexError file start (start + 3) line col .unsupported
      "lexer.directive" "source option directives are unsupported")
  if rest.startsWith "//" then
    let stop := scanWhile (· != '\n') it.2
    let consumed := (it.1.slice! it.2 stop).copy
    let (l, c, b) := advance line col leading consumed
    return ⟨⟨it.1, stop⟩, l, c, b, indent, out, false⟩
  if rest.startsWith "/*" then
    let some stop := blockEnd (it.2.nextn 2)
      | throw (lexError file start it.1.utf8ByteSize line col .malformed
          "lexer.comment" "unterminated block comment")
    let consumed := (it.1.slice! it.2 stop).copy
    let (l, c, _) := advance line col leading consumed
    return ⟨⟨it.1, stop⟩, l, c, leading || consumed.contains '\n',
      (if consumed.contains '\n' then 0 else indent), out, false⟩
  let ch := it.2.get!
  if ch == '\t' && leading then
    throw (lexError file start (start + 1) line col .malformed
      "lexer.indentation-tab" "tabs in indentation are not permitted")
  if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' then
    let (l, c, b) := advance line col leading (String.singleton ch)
    return ⟨⟨it.1, it.2.next!⟩, l, c, b,
      (if ch == '\n' then 0 else if leading && ch == ' ' && col == indent + 1 then indent + 1 else indent), out, false⟩
  match atom it with
  | .error _ e => throw (lexError file start (it.2.next!).offset.byteIdx line col
      .malformed "lexer.character" (toString e))
  | .success next text =>
    let stop := next.2.offset.byteIdx
    if excludedWords.contains text || excludedSymbols.contains text then
      throw (lexError file start stop line col .unsupported "lexer.excluded"
        s!"unsupported source construct: {text}")
    -- Longest-match decimal real/double tokens must not become integer joins.
    if ch.isDigit && (next.1.sliceFrom next.2).startsWith "." &&
        !(next.2.next!).IsAtEnd &&
        (next.2.next!).get!.isDigit then
      throw (lexError file start stop line col .unsupported "lexer.real"
        "real and double literals are unsupported")
    let (l, c, b) := advance line col false text
    return ⟨next, l, c, b, indent, out.push ⟨text, ⟨file, start, stop⟩, line, col, indent + 1⟩, false⟩

def lex (file source : String) : Except Diagnostic (Array Token) := do
  let mut state : LexerState := { cursor := ⟨source, source.startPos⟩ }
  for _ in [:source.utf8ByteSize + 1] do
    state ← lexStep file state
    if state.done then return state.out
  throw (lexError file source.utf8ByteSize source.utf8ByteSize state.line state.column
    .malformed "lexer.progress" "tokenizer progress exhausted")

end ClaferCompiler.Frontend
