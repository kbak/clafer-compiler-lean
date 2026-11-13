module

public import ClaferCompiler.Frontend.Parser
public import ClaferCompiler.Frontend.Behavioral.Surface
public import ClaferCompiler.IR.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral

/-- Only explicit profile selection enables the behavioral lexical inventory. -/
def excluded (text : String) : Bool :=
  ["string", "real", "double", "bool", "boolean", "minimize", "maximize",
   "[alloy|", "[choco|", "<<", ">>", "\\", "\""].contains text

def binaryPower : String → Option Nat
  | "U" | "until" => some 8 | "W" | "weakuntil" => some 9
  | "*" | "/" | "%" => some 18 | "<:" => some 21 | ":>" => some 22
  | "," => some 23 | "&" => some 26
  | t => Frontend.binaryPower t

def expressionPower : Expr → Nat
  | .quantified .. | .letSet .. | .conditional .. => 1
  | .pattern .. => 2
  | .transition .. => 0
  | .unary t _ _ =>
    if ["initially", "finally"].contains t.text then 2
    else if ["X", "next", "F", "eventually", "G", "globally"].contains t.text then 10
    else if t.text == "!" then 11
    else if ["max", "min"].contains t.text then 19
    else if ["#", "-", "sum", "product"].contains t.text then 20 else 16
  | .binary t _ _ _ => if t.text == "not in" then 15 else (binaryPower t.text).getD 27
  | _ => 27

structure Parsers where
  expression : Nat → P Expr
  tail : Nat → Expr → P Expr
  bodies : P (List Expr)
  element : Bool → Bool → P Element
  elements : Bool → Option Nat → Option Nat → P (List Element)

def parserBase : Parsers :=
  ⟨fun _ => progressError, fun _ _ => progressError, progressError,
    fun _ _ => progressError, fun _ _ _ => progressError⟩

/-- Token-count bounded collection consumes every token or reports a diagnostic. -/
def names (separator : String) : P (List Name) := do
  let first ← name
  let mut found := [first]
  let limit := (← get).rest.length + 1
  for _ in [:limit] do
    if (← accept separator).isNone then return found.reverse
    found := (← name) :: found
  progressError

def modifiers : P (List Token) := do
  let mut found := []
  let limit := (← get).rest.length + 1
  for _ in [:limit] do
    if !["initial", "final", "finalref", "finaltarget"].contains (← peek).text then
      return found.reverse
    found := (← pop) :: found
  progressError

def arrow (previous : Parsers) : P (Token × Option Expr) := do
  let start ← pop
  if start.text == "-->" || start.text == "-->>" then return (start, none)
  if start.text != "-[" then reject start "behavioral.arrow" "expected a transition arrow"
  let guard ← previous.expression 1
  let close ← pop
  unless close.text == "]->" || close.text == "]->>" do
    reject close "behavioral.arrow" "expected a guarded transition arrow terminator"
  let op := { start with
    text := (if close.text == "]->" then "-->" else "-->>")
    span := extent start.span close.span }
  return (op, some guard)

def pattern (previous : Parsers) (kind : Token) (first : Expr)
    (second : Option Expr) (start : SourceSpan) : P Expr := do
  let t ← peek
  let (scope, opener, closer) : Option Token × Option Expr × Option Expr ←
    if t.text == "before" then do
      let _ ← pop
      let r ← previous.expression 11
      pure (some t, none, some r)
    else if t.text == "after" then do
      let _ ← pop
      let q ← previous.expression 11
      if let some untilToken ← accept "until" then
        let r ← previous.expression 11
        pure (some { t with text := "after until", span := extent t.span untilToken.span }, some q, some r)
      else pure (some t, some q, none)
    else if t.text == "between" then do
      let _ ← pop
      let q ← previous.expression 11
      let _ ← expect "and"
      let r ← previous.expression 11
      pure (some t, some q, some r)
    else pure (none, none, none)
  return .pattern kind first second scope opener closer (extent start (← get).previous.span)

def expressionStep (previous : Parsers) (minimum : Nat) : P Expr := do
  let t ← pop
  let left ←
    if t.text == "(" then do
      let body ← previous.expression 0
      let close ← expect ")"
      pure (.parens body (extent t.span close.span))
    else if ["never", "sometime", "lonce", "always"].contains t.text && minimum ≤ 2 then do
      let body ← previous.expression 3
      pattern previous t body none t.span
    else if t.text == "if" && minimum ≤ 1 then do
      let condition ← previous.expression 1
      let _ ← expect "then"
      let yes ← previous.expression 1
      let _ ← expect "else"
      let no ← previous.expression 1
      pure (.conditional t condition yes no (extent t.span no.span))
    else if t.text == "let" && minimum ≤ 1 then do
      let binder ← name
      let _ ← expect "="
      let value ← name
      let _ ← expect "in"
      let body ← previous.expression 1
      pure (.letSet t binder value body (extent t.span body.span))
    else if ["all", "some", "no", "not", "one", "lone"].contains t.text then do
      let s ← get
      let isBinder := (s.rest.drop 1).head?.any (fun x => x.text == ":" || x.text == ";") ||
        s.rest.head?.any (fun x => x.text == "disj")
      if isBinder then do
        if minimum > 1 then reject t "parser.precedence" "parenthesize the quantified expression"
        let disjoint ← accept "disj"
        let binders ← names ";"
        let _ ← expect ":"
        let domain ← previous.expression 21
        let _ ← expect "|"
        let body ← previous.expression 1
        pure (.quantified t disjoint binders domain body (extent t.span body.span))
      else if t.text == "all" then reject t "parser.binder" "all requires a binder"
      else if minimum > 16 then reject t "parser.precedence" "parenthesize the collection test"
      else do
        let body ← previous.expression 20
        pure (.unary t body (extent t.span body.span))
    else if let some (power, bodyPower) :=
      if ["initially", "finally"].contains t.text then some (2, 3)
      else if ["X", "next", "F", "eventually", "G", "globally"].contains t.text then some (10, 10)
      else if t.text == "!" then some (11, 11)
      else if ["max", "min"].contains t.text then some (19, 20)
      else if ["-", "#", "sum", "product"].contains t.text then some (20, 21)
      else none then do
        if minimum > power then reject t "parser.precedence" "parenthesize the prefix expression"
        let body ← previous.expression bodyPower
        pure (.unary t body (extent t.span body.span))
    else if let some n := t.text.toNat? then pure (.integer t n)
    else if isName t || t.text == "noclafer" then pure (.name t)
    else reject t "behavioral.expression" "expected a behavioral expression"
  previous.tail minimum left

def tailStep (previous : Parsers) (minimum : Nat) (left : Expr) : P Expr := do
  let t ← peek
  if ["-->", "-->>", "-["].contains t.text && minimum == 0 && expressionPower left ≥ 1 then
    let (op, guard) ← arrow previous
    let right ← previous.expression 0
    return .transition op left guard right (extent left.span right.span)
  if t.text == "must" && minimum ≤ 2 && expressionPower left ≥ 3 then
    let _ ← pop
    let kind ← pop
    unless ["precede", "follow"].contains kind.text do
      reject kind "behavioral.pattern" "expected precede or follow"
    let right ← previous.expression 3
    let result ← pattern previous kind left (some right) left.span
    return ← previous.tail minimum result
  let some power := binaryPower t.text | return left
  if power < minimum || expressionPower left < power then return left
  if t.text == "not" && !((← get).rest.drop 1).head?.any (fun x => x.text == "in") then return left
  let _ ← pop
  let op ← if t.text == "not" then do
      let last ← expect "in"
      pure { t with text := "not in", span := extent t.span last.span }
    else pure t
  let right ← previous.expression (power + 1)
  previous.tail minimum (.binary op left right (extent left.span right.span))

def bodiesStep (previous : Parsers) : P (List Expr) := do
  if (← peek).text == "]" then return []
  let body ← previous.expression 0
  return body :: (← previous.bodies)

def header (previous : Parsers) (layout : Bool) (start : Token) : P Header := do
  if let some use ← accept "`" then
    let n ← headerName layout start
    let card ← cardinality layout start false
    return { structural := { name := n, useToken := some use, cardinality := card } }
  let abstractToken ← accept "abstract"
  let mods ← modifiers
  let group ← cardinality layout start true
  let n ← headerName layout start
  let super ← if (← headerContinues layout start) && (← accept ":").isSome then
      some <$> typeName layout start else pure none
  let reference ← if (← headerContinues layout start) && ["->", "->>"].contains (← peek).text then do
      let op ← pop
      let target ← typeName layout start
      pure (some (op, target))
    else pure none
  if super.isSome || reference.isSome then
    if [".", "++", "--", "**", "&", ",", "("].contains (← peek).text then
      reject (← peek) "behavioral.type-expression" "type positions require a single name" .unsupported
  let card ← cardinality layout start false
  let initializer ← if (← headerContinues layout start) && ((← peek).text == "=" || (← peek).text == ":=") then do
      let op ← pop
      let value ← previous.expression 0
      pure (some (op, value))
    else pure none
  let trans ← if (← headerContinues layout start) && ["-->", "-->>", "-["].contains (← peek).text then do
      let (op, guard) ← arrow previous
      let target ← previous.expression 0
      pure (some (op, guard, target))
    else pure none
  return {
    structural := { name := n, abstractToken, group, super, reference, cardinality := card }
    modifiers := mods
    initializer
    transition := trans }

def elementStep (previous : Parsers) (top layout : Bool) : P Element := do
  let start ← peek
  if start.text == "enum" then
    unless top do reject start "behavioral.enum-placement" "enum declarations must be top-level"
    let _ ← pop
    let n ← name
    let _ ← expect "="
    let literals ← names "|"
    return .enumeration n literals (extent start.span (← get).previous.span)
  let assertion ← accept "assert"
  if (← accept "[").isSome then
    let bodies ← previous.bodies
    let close ← expect "]"
    return .property (if assertion.isSome then .assertion else .constraint) bodies (extent start.span close.span)
  if assertion.isSome then reject (← peek) "parser.expected" "expected '[' after assert"
  let h ← header previous layout start
  let next ← peek
  let children ←
    if (← accept "{").isSome then do
      let es ← previous.elements false none none
      let _ ← expect "}"
      pure es
    else if layout && next.text != "" && next.text != "}" && next.line > start.line &&
        next.layoutColumn > start.layoutColumn then
      previous.elements false (some next.layoutColumn) none
    else pure []
  return .declaration h children (extent start.span (← get).previous.span)

def elementsStep (previous : Parsers) (top : Bool) (column previousDecl : Option Nat) : P (List Element) := do
  let t ← peek
  if t.text == "" || t.text == "}" then return []
  if let some c := column then
    if t.layoutColumn < c then return []
    if t.layoutColumn > c then reject t "parser.layout" "inconsistent indentation"
  let isDecl := t.text != "[" && t.text != "assert"
  if isDecl && previousDecl == some t.line then
    reject t "parser.layout" "sibling declarations must start on separate lines"
  let e ← previous.element top column.isSome
  return e :: (← previous.elements top column (if isDecl then some t.line else previousDecl))

def parserStep (previous : Parsers) : Parsers :=
  ⟨expressionStep previous, tailStep previous, bodiesStep previous, elementStep previous, elementsStep previous⟩

-- [impl->req~compiler-behavioral-frontend~1]
-- [impl->req~compiler-diagnostics~1]
def parseBehavioral (profile file source : String) : Except Diagnostic Document := do
  if profile != IR.BehavioralStructural.profile then
    throw (lexError file 0 0 1 1 .unsupported "behavioral.profile" "unsupported behavioral profile")
  let tokens ← lexWith excluded file source
  let eof : Token := tokens.back?.getD ⟨"", ⟨file, source.utf8ByteSize, source.utf8ByteSize⟩, 1, 1, 1⟩
  let action : P (List Element) := do
    let grammar := Nat.repeat parserStep (4 * tokens.size + 4) parserBase
    let es ← grammar.elements true (some 1) none
    let _ ← expect ""
    return es
  let (elements, _) ← action.run ⟨tokens.toList, eof, eof⟩
  return ⟨file, source, elements⟩

end ClaferCompiler.Frontend.Behavioral
