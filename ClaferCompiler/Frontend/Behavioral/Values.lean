module

public import ClaferCompiler.Frontend.Behavioral.Binders
public import ClaferCompiler.Frontend.ConstraintsRules
public import ClaferCompiler.IR.BehavioralSupport
public import ClaferCompiler.IR.Behavioral.Surface

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Values
open IR.Behavioral

/-- Empty sets remain polymorphic until a surrounding operation supplies a type. -/
inductive Ty (k : Nat) where
  | objects (declaration : Fin k)
  | integers
  | empty
  deriving DecidableEq, BEq, Repr

/-- An object collection retains its head type. Value conversion is explicit and
performs at most one inherited dereference. Scalars and integer sets differ. -/
inductive Value (k n : Nat) where
  | collection (type : Ty k) (term : Primitive.Collection k n)
  | integer (term : Primitive.Integer k n)
  | formula (term : Grouped.Formula k n)
  | chain (term : Surface.Transitions.ChainF (Grouped.Atom k) (Primitive.Collection k) n)

abbrev Context (k n : Nat) := Binders.Context (Ty k) n

def present (a : Primitive.Collection k n) : Grouped.Formula k n := .atom (.primitive (.inhabited a))
def self : Grouped.Formula k n := present (.set .this)

-- [impl->req~compiler-behavioral-elaboration~1]
def boolean : Value k n → Except String (Grouped.Formula k n)
  | .formula a => .ok a
  | .chain a => .ok (Surface.Transitions.expand self a)
  | .collection _ a => .ok (present a)
  | .integer _ => .error "behavioral.expected-formula"

def heads : Value k n → Except String (Ty k × Primitive.Collection k n)
  | .collection t a => .ok (t, a)
  | .integer a => .ok (.integers, .integer a)
  | _ => .error "behavioral.expected-collection"

def isInteger (v : IR.BehavioralStructural.Validated k) (d : Fin k) : Bool :=
  (v.core.structural.get d).origin == .integer

def classType (v : IR.BehavioralStructural.Validated k) (d : Fin k) : Ty k :=
  if isInteger v d then .integers else .objects d

/-- First navigation from the fixed context identity differs from navigation
from observed standalone `this`, which is empty after the context disappears. -/
def navigateSet (step : Step k) (a : SetExpr k n) : SetExpr k n :=
  match a with
  | .this => .thisStep step
  | _ => .step step a

-- [impl->req~compiler-behavioral-elaboration~1]
def target (v : IR.BehavioralStructural.Validated k) : Value k n → Except String (Value k n)
  | .collection (.objects d) (.set a) =>
      match IR.BehavioralSupport.referenceView v d with
      | none => .ok (.collection (.objects d) (.set a))
      | some r => .ok (.collection (classType v r.target) (.set (.step (.deref d) a)))
  | a => .ok a

def integer (v : IR.BehavioralStructural.Validated k) (a : Value k n) : Except String (Primitive.Integer k n) := do
  match ← target v a with
  | .integer a => return a
  | .collection .integers a | .collection .empty a => return .coerce a
  | _ => throw "behavioral.expected-integer"

/-- A finite class search reuses the static frontend's independent nearest-field
predicate. Inherited reference ownership comes from behavioral admission. -/
def navigation (v : IR.BehavioralStructural.Validated k) : Nat →
    (d : Fin k) → (a : SetExpr k n) → (name : String) → Except String (Value k n) :=
  Nat.rec (fun _ _ _ => .error "behavioral.navigation-cycle") (fun _ next d a name => do
    let c := v.core.structural
    if name == "parent" then
      match (c.get d).parent with
      | some p => return .collection (classType v p) (.set (navigateSet .parent a))
      | none => throw "behavioral.heterogeneous-parent-type"
    if name == "dref" then
      match IR.BehavioralSupport.referenceView v d with
      | some r => return .collection (classType v r.target) (.set (navigateSet (.deref d) a))
      | none => throw "behavioral.not-reference"
    if Resolution.integerName name then throw "behavioral.infinite-primitive-extent"
    for depth in List.range (k + 1) do
      for p in List.finRange k do
        for y in List.finRange k do
          if Constraints.Field c d name depth p y then
            return .collection (classType v y) (.set (navigateSet (.child y) a))
    if Constraints.HasField c d name then throw "behavioral.ambiguous-navigation"
    match IR.BehavioralSupport.referenceView v d with
    | some r => next r.target (navigateSet (.deref d) a) name
    | none => throw "behavioral.missing-navigation")

/-- Bare-name fallback searches only the original context's reference chain.
A cycle without a matching field does not hide a unique global declaration. -/
def targetHasField (v : IR.BehavioralStructural.Validated k) (start : Fin k) (name : String) : Bool :=
  (List.range (k + 1)).any fun depth =>
    let target := depth.repeat (fun d => d.bind fun d =>
      (IR.BehavioralSupport.referenceView v d).map (·.target)) (some start)
    target.any fun d => decide (Constraints.HasField v.core.structural d name)

-- [impl->req~compiler-behavioral-elaboration~1]
def name (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (Γ : Context k n)
    (cursor : Option (Value k n)) (text : String) : Except String (Value k n) := do
  let c := v.core.structural
  if text == "noclafer" then return .collection .empty (.set .empty)
  if Resolution.integerName text then throw "behavioral.infinite-primitive-extent"
  match cursor with
  | some (.collection (.objects d) (.set a)) => return ← navigation v (k + 1) d a text
  | some _ => throw "behavioral.navigation-type"
  | none => pure ()
  if text == "this" then return .collection (.objects owner) (.set .this)
  if text == "parent" || text == "dref" then return ← navigation v (k + 1) owner .this text
  if let some found := Binders.lookup Γ text then
    return .collection found.type (.set (.var found.index))
  let mut scope := some (owner, (SetExpr.this : SetExpr k n))
  for _ in List.range (k + 1) do
    match scope with
    | none => pure ()
    | some (d, a) =>
      if d != c.root && Constraints.HasField c d text then
        return ← navigation v (k + 1) d a text
      scope := (c.get d).parent.map fun p => (p, navigateSet .parent a)
  if let some r := IR.BehavioralSupport.referenceView v owner then
    if targetHasField v r.target text then
      return ← navigation v (k + 1) r.target (navigateSet (.deref owner) .this) text
  for d in List.finRange k do
    if Constraints.Global c text d then return .collection (classType v d) (.set (.extent d))
  if c.declarations.any (fun d => d.name == text) then throw "behavioral.ambiguous-name"
  throw "behavioral.unknown-name"

def common (v : IR.BehavioralStructural.Validated k) (a b : Ty k) : Except String (Ty k) := do
  if a == b then return a
  match a, b with
  | .empty, b => return b
  | a, .empty => return a
  | .objects x, .objects y =>
    for p in v.analysis.ancestors[x] do
      if p ∈ v.analysis.ancestors[y] then return .objects p
    throw "behavioral.incompatible-collections"
  | _, _ => throw "behavioral.incompatible-collections"

/-- Set operations on total head paths remain navigable. Partial primitives use
the corresponding partial constructor instead of discarding definedness. -/
def combine (op : String) (a b : Primitive.Collection k n) : Primitive.Collection k n :=
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
  if op ∈ ["++", ",", "--", "**", "&"] then
    let (ta, a) ← heads a
    let (tb, b) ← heads b
    return .collection (← common v ta tb) (combine op a b)
  if op == "=" || op == "!=" then
    match a, b with
    | .formula a, .formula b =>
      let f := FormulaF.iff a b
      return .formula (if op == "!=" then .not f else f)
    | _, _ => pure ()
  if op ∈ ["=", "!=", "in", "not in"] then
    -- An empty operand selects head comparison, preserving `no heads`.
    let empty := match a, b with
      | .collection .empty _, _ | _, .collection .empty _ => true
      | _, _ => false
    let a ← if empty then pure a else target v a
    let b ← if empty then pure b else target v b
    let (ta, a) ← heads a
    let (tb, b) ← heads b
    let _ ← common v ta tb
    let body := if op == "=" || op == "!=" then .equal a b else .subset a b
    let f := FormulaF.atom (Grouped.Atom.primitive body)
    return .formula (if op == "!=" || op == "not in" then .not f else f)
  throw "behavioral.unsupported-binary"

end ClaferCompiler.Frontend.Behavioral.Values
