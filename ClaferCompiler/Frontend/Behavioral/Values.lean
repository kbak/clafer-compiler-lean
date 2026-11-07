module

public import ClaferCompiler.Frontend.Behavioral.ValueCore

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Values
open IR.Behavioral

/-- Set operations on total head paths remain navigable. Partial primitives use
the corresponding partial constructor instead of discarding definedness. -/
def combine (op : String) (a b : Expression.Collection k n) : Expression.Collection k n :=
  match a, b with
  | .set a, .set b => .set (if op == "++" || op == "," then .union a b
      else if op == "--" then .diff a b else .inter a b)
  | a, b => if op == "++" || op == "," then .union a b
      else if op == "--" then .diff a b else .inter a b

-- [impl->req~compiler-behavioral-elaboration~1]
def unary (v : IR.BehavioralStructural.Validated k) (op : String) (a : Value k n) : Except String (Value k n) := do
  if op == "!" then return .formula (.not (← boolean a))
  if op == "X" || op == "next" then return .formula (.next (← boolean a))
  if op == "F" || op == "eventually" then return .formula (.eventually (← boolean a))
  if op == "G" || op == "globally" then return .formula (.always (← boolean a))
  if op == "initially" then return .formula (.initially (← boolean a))
  if op == "finally" then return .formula (.finally (← boolean a))
  if op == "-" then return .integer (.negate (← integer v a))
  if op == "#" then return .integer (.cardinality (← heads a).2)
  if op == "some" then return .formula (present (← heads a).2)
  if op == "no" || op == "not" then return .formula (.not (present (← heads a).2))
  if op == "one" then return .formula (.atom (.primitive (.integerEqual (.cardinality (← heads a).2) (.literal 1))))
  if op == "lone" then return .formula (.atom (.primitive (.less (.cardinality (← heads a).2) (.literal 2))))
  if op == "min" || op == "max" then
    let (type, a) ← heads (← target v a)
    unless type == .integers || type == .empty do throw "behavioral.expected-integer"
    return .collection .integers (.extreme (if op == "min" then .minimum else .maximum) a)
  throw "behavioral.unsupported-unary"

def booleanLike : Value k n → Bool
  | .formula _ | .chain _ => true
  | _ => false

def emptyPair (a b : Value k n) : Bool :=
  match a, b with
  | .collection .empty _, _ | _, .collection .empty _ => true
  | _, _ => false

def compareValues (v : IR.BehavioralStructural.Validated k) (op : String) (a b : Value k n) : Except String (Value k n) := do
  -- An empty operand selects head comparison, preserving `no heads`.
  let empty := emptyPair a b
  let a ← if empty then pure a else target v a
  let b ← if empty then pure b else target v b
  let (ta, a) ← heads a
  let (tb, b) ← heads b
  let _ ← overlap v ta tb
  let body := if op == "=" || op == "!=" then .equal a b else .subset a b
  let f := FormulaF.atom (Expression.Atom.primitive body)
  return .formula (if op == "!=" || op == "not in" then .not f else f)

-- [impl->req~compiler-behavioral-elaboration~1]
def binary (v : IR.BehavioralStructural.Validated k) (op : String) (a b : Value k n) : Except String (Value k n) := do
  if op ∈ ["&&", "||", "=>", "<=>", "xor", "U", "until", "W", "weakuntil"] then
    let a ← boolean a
    let b ← boolean b
    return .formula (match op with
      | "&&" => .and a b | "||" => .or a b | "=>" => .implies a b
      | "<=>" => .iff a b | "xor" => .xor a b
      | "U" | "until" => .strongUntil a b | _ => .weakUntil a b)
  if op ∈ ["+", "-", "*", "/", "%", "<", ">", "<=", ">="] then
    let a ← integer v a
    let b ← integer v b
    match op with
    | "+" => return .integer (.binary .add a b)
    | "-" => return .integer (.binary .subtract a b)
    | "*" => return .integer (.binary .multiply a b)
    | "/" => return .integer (.binary .divide a b)
    | "%" => return .integer (.binary .remainder a b)
    | "<" => return .formula (.atom (.primitive (.less a b)))
    | ">" => return .formula (.atom (.primitive (.less b a)))
    | "<=" => return .formula (.not (.atom (.primitive (.less b a))))
    | _ => return .formula (.not (.atom (.primitive (.less a b))))
  if op ∈ ["++", ",", "--", "**", "&", "<:", ":>"] then
    let (ta, a) ← heads a
    let (tb, b) ← heads b
    let type ← if op == "++" || op == "," then common v ta tb else overlap v ta tb
    return .collection (if op == "--" then ta else type) (combine op a b)
  if (op == "=" || op == "!=") && (booleanLike a || booleanLike b) then
    let a ← boolean a
    let b ← boolean b
    let f := FormulaF.iff a b
    return .formula (if op == "!=" then .not f else f)
  if op ∈ ["=", "!=", "in", "not in"] then
    return ← compareValues v op a b
  throw "behavioral.unsupported-binary"

-- [impl->req~compiler-behavioral-elaboration~1]
def conditional (v : IR.BehavioralStructural.Validated k) (condition : Expression.Formula k n)
    (yes no : Value k n) : Except String (Value k n) := do
  match yes, no with
  | .formula _, _ | .chain _, _ | _, .formula _ | _, .chain _ =>
    return .formula (.ite condition (← boolean yes) (← boolean no))
  | .integer _, _ | _, .integer _ =>
    return .integer (.ite condition (← integer v yes) (← integer v no))
  | .collection a x, .collection b y =>
    return .collection (← common v a b) (.ite condition x y)

end ClaferCompiler.Frontend.Behavioral.Values
