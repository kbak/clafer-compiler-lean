module

public import ClaferCompiler.Frontend.Lexer

@[expose] public section
namespace ClaferCompiler.Frontend

-- Requirement: compiler-parser; trace artifacts are in docs/parser.md.
structure Cursor where
  rest : List Token
  previous : Token
  eof : Token

abbrev P := StateT Cursor (Except Diagnostic)

def peek : P Token := do return (← get).rest.headD (← get).eof
def pop : P Token := do
  let s ← get
  let t := s.rest.headD s.eof
  set { s with rest := s.rest.drop 1, previous := t }
  return t

-- Requirement: compiler-diagnostics; trace artifacts are in docs/parser.md.
def reject (t : Token) (code message : String)
    (category : Category := .malformed) : P α := do
  throw { code, phase := "parser", category, message, primary := t.span, line := t.line, column := t.column }

def expect (text : String) : P Token := do
  let t ← peek
  if t.text == text then pop else reject t "parser.expected" s!"expected '{text}'"

def accept (text : String) : P (Option Token) := do
  if (← peek).text == text then return some (← pop) else return none

def name : P Name := do
  let t ← peek
  if isName t then pop else reject t "parser.name" "expected an unqualified name"

/-- Layout inserts a body only at greater indentation; braces disable it.
At equal indentation the pinned grammar can continue a declaration header. -/
def headerContinues (layout : Bool) (start : Token) : P Bool := do
  let t ← peek
  return !layout || t.line == start.line || t.layoutColumn == start.layoutColumn

def headerName (layout : Bool) (start : Token) : P Name := do
  unless ← headerContinues layout start do
    reject (← peek) "parser.layout" "unexpected layout boundary inside a header"
  name

def typeName (layout : Bool) (start : Token) : P Name := do
  let t ← peek
  if ["(", "#", "-"].contains t.text then
    reject t "parser.type-expression" "type positions require a single name" .unsupported
  headerName layout start

def extent (first last : SourceSpan) : SourceSpan :=
  { first with endByte := last.endByte }

def numberValue (t : Token) : P Nat :=
  match t.text.toNat? with
  | some n => pure n
  | none => reject t "parser.integer" "expected a nonnegative decimal integer"

def cardinality (layout : Bool) (start : Token) (group : Bool) : P (Option Cardinality) := do
  unless ← headerContinues layout start do return none
  let t ← peek
  let shorthand := if group then
      [("xor", 1, some 1), ("or", 1, none), ("mux", 0, some 1), ("opt", 0, none)]
    else [("?", 0, some 1), ("+", 1, none), ("*", 0, none)]
  if let some (_, lo, hi) := shorthand.find? (fun x => x.1 == t.text) then
    return some ⟨#[← pop], lo, hi⟩
  if let some lo := t.text.toNat? then
    let _ ← pop
    if let some dots ← accept ".." then
      unless ← headerContinues layout start do
        reject (← peek) "parser.layout" "unexpected layout boundary inside an interval"
      let upper ← pop
      let hi ← if upper.text == "*" then pure none else some <$> numberValue upper
      if hi.any (· < lo) then
        reject upper "parser.interval" "interval upper bound is below its lower bound"
      return some ⟨#[t, dots, upper], lo, hi⟩
    if group then reject t "parser.group" "a numeric group requires an interval"
    return some ⟨#[t], lo, some lo⟩
  return none

/-- Binding powers and left associativity from the retained Exp3..Exp27 rules. -/
def binaryPower : String → Option Nat
  | "<=>" => some 3 | "=>" => some 4 | "||" => some 5 | "xor" => some 6
  | "&&" => some 7
  | "<" | ">" | "=" | "<=" | ">=" | "!=" | "in" | "not" => some 15
  | "+" | "-" => some 17 | "++" => some 23 | "--" => some 24
  | "**" => some 25 | "." => some 26 | _ => none

/-- The highest grammar category that can derive an unparenthesized node.
This matters when a collection test is followed by arithmetic: subtraction may
start a new hard body, while addition is malformed (Exp16 cannot be Exp17). -/
def expressionPower : Expr → Nat
  | .quantified .. => 1
  | .unary t _ _ => if t.text == "!" then 11 else if t.text == "#" || t.text == "-" then 20 else 16
  | .binary t _ _ _ => if t.text == "not in" then 15 else (binaryPower t.text).getD 27
  | _ => 27

def header (layout : Bool) (start : Token) : P Header := do
  if let some use ← accept "`" then
    let n ← headerName layout start
    let card ← cardinality layout start false
    if (← peek).text == "=" then
      reject (← peek) "parser.initializer" "initializers are unsupported" .unsupported
    return { name := n, useToken := some use, cardinality := card }
  let abstractToken ← accept "abstract"
  let group ← cardinality layout start true
  let n ← headerName layout start
  let super ← if (← headerContinues layout start) && (← accept ":").isSome then some <$> typeName layout start else pure none
  let reference ← if (← headerContinues layout start) && ["->", "->>"].contains (← peek).text then do
    let arrow ← pop
    let target ← typeName layout start
    pure (some (arrow, target))
    else pure none
  let card ← cardinality layout start false
  let next ← peek
  if next.text == "=" then
    reject next "parser.initializer" "initializers are unsupported" .unsupported
  if super.isSome || reference.isSome then
    if [".", "++", "--", "**", "("].contains next.text then
      reject next "parser.type-expression" "type positions require a single name" .unsupported
  return { name := n, abstractToken, group, super, reference, cardinality := card }

/-- A finite approximation to the mutually recursive grammar, constructed using
standard-library iteration. This avoids Lean's generated unsafe recursive helpers
without weakening the project audit. A successful parse still consumes EOF. -/
structure Parsers where
  expression : Nat → P Expr
  expressionTail : Nat → Expr → P Expr
  bodies : P (List Expr)
  element : Bool → P Element
  elements : Option Nat → Option Nat → P (List Element)

def progressError : P α := do
  reject (← peek) "parser.progress" "parser progress exhausted"

def parserBase : Parsers :=
  ⟨fun _ => progressError, fun _ _ => progressError, progressError,
    fun _ => progressError, fun _ _ => progressError⟩

def expressionStep (previous : Parsers) (minimum : Nat) : P Expr := do
  let t ← pop
  let left ←
    if t.text == "(" then do
      let body ← previous.expression 1
      let close ← expect ")"
      pure (Expr.parens body (extent t.span close.span))
    else if t.text == "!" && minimum ≤ 11 then do
      let body ← previous.expression 11
      pure (Expr.unary t body (extent t.span body.span))
    else if (t.text == "-" || t.text == "#") && minimum ≤ 20 then do
      let body ← previous.expression 21
      pure (Expr.unary t body (extent t.span body.span))
    else if ["all", "some", "no", "not", "one", "lone"].contains t.text then do
      let s ← get
      let binderForm := (s.rest.drop 1).head?.any (fun x => x.text == ":")
      if binderForm then
        if t.text == "one" || t.text == "lone" then
          reject t "parser.binder" "one/lone binders are unsupported" .unsupported
        else if minimum > 1 then
          reject t "parser.precedence" "parenthesize the quantified expression"
        else do
          let binder ← name
          let _ ← expect ":"
          let domain ← previous.expression 21
          let _ ← expect "|"
          let body ← previous.expression 1
          pure (Expr.quantified t binder domain body (extent t.span body.span))
      else if t.text == "all" then reject t "parser.binder" "all requires a single binder"
      else if minimum > 16 then reject t "parser.precedence" "parenthesize the collection test"
      else do
        let body ← previous.expression 20
        pure (Expr.unary t body (extent t.span body.span))
    else if let some n := t.text.toNat? then pure (Expr.integer t n)
    else if isName t then pure (Expr.name t)
    else reject t "parser.expression" "expected a static expression"
  previous.expressionTail minimum left

def expressionTailStep (previous : Parsers) (minimum : Nat) (left : Expr) : P Expr := do
  let t ← peek
  if t.text == "*" then
    reject t "parser.arithmetic" "multiplication is unsupported" .unsupported
  let some power := binaryPower t.text | return left
  if power < minimum || expressionPower left < power then return left
  -- 'not' is also a prefix collection test starting the next hard body.
  if t.text == "not" && !((← get).rest.drop 1).head?.any (fun x => x.text == "in") then
    return left
  let _ ← pop
  let op ← if t.text == "not" then do
    let last ← expect "in"
    pure { t with text := "not in", span := extent t.span last.span }
    else pure t
  let right ← previous.expression (power + 1)
  previous.expressionTail minimum (.binary op left right (extent left.span right.span))

def bodiesStep (previous : Parsers) : P (List Expr) := do
  if (← peek).text == "]" then return []
  let body ← previous.expression 1
  return body :: (← previous.bodies)

def elementStep (previous : Parsers) (layout : Bool) : P Element := do
  let start ← peek
  if (← accept "[").isSome then
    let expressions ← previous.bodies
    let close ← expect "]"
    return .constraint expressions (extent start.span close.span)
  let h ← header layout start
  let next ← peek
  let children ←
    if (← accept "{").isSome then do
      let es ← previous.elements none none
      let _ ← expect "}"
      pure es
    else if layout && next.text != "" && next.text != "}" && next.line > start.line &&
        next.layoutColumn > start.layoutColumn then
      previous.elements (some next.layoutColumn) none
    else pure []
  let last := (← get).previous
  return .declaration h children (extent start.span last.span)

def elementsStep (previous : Parsers) (column previousDecl : Option Nat) : P (List Element) := do
  let t ← peek
  if t.text == "" || t.text == "}" then return []
  if let some c := column then
    if t.layoutColumn < c then return []
    if t.layoutColumn > c then reject t "parser.layout" "inconsistent indentation"
  let isDeclaration := t.text != "["
  if isDeclaration && previousDecl == some t.line then
    reject t "parser.layout" "sibling declarations must start on separate lines"
  let e ← previous.element column.isSome
  return e :: (← previous.elements column (if isDeclaration then some t.line else previousDecl))

def parserStep (previous : Parsers) : Parsers :=
  ⟨expressionStep previous, expressionTailStep previous, bodiesStep previous,
    elementStep previous, elementsStep previous⟩

/-- Parsing is independent of name resolution, typing, defaulting and compilation.
The original source and authored tokens are retained verbatim. -/
def parse (file source : String) : Except Diagnostic Document := do
  let tokens ← lex file source
  let eof : Token := tokens.back?.getD ⟨"", ⟨file, source.utf8ByteSize, source.utf8ByteSize⟩, 1, 1, 1⟩
  let action : P (List Element) := do
    let grammar := Nat.repeat parserStep (4 * tokens.size + 4) parserBase
    let es ← grammar.elements (some 1) none
    let _ ← expect ""
    return es
  let (es, _) ← action.run ⟨tokens.toList, eof, eof⟩
  return ⟨file, source, es⟩

end ClaferCompiler.Frontend
