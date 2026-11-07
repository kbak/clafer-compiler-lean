module

public import ClaferCompiler.IR.Behavioral.Expression
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
  | mixed (declarations : List (Fin k))
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- An object collection retains its head type. Value conversion is explicit and
performs at most one inherited dereference. Scalars and integer sets differ. -/
inductive Value (k n : Nat) where
  | collection (type : Ty k) (term : Expression.Collection k n)
  | integer (term : Expression.Integer k n)
  | formula (term : Expression.Formula k n)
  | chain (term : Surface.Transitions.ChainF (Expression.Atom k) (Expression.Collection k) n)

abbrev Context (k n : Nat) := Binders.Context (Ty k) n

def present (a : Expression.Collection k n) : Expression.Formula k n := .atom (.primitive (.inhabited a))
def self : Expression.Formula k n := present (.set .this)

-- [impl->req~compiler-behavioral-elaboration~1]
def boolean : Value k n → Except String (Expression.Formula k n)
  | .formula a => .ok a
  | .chain a => .ok (Surface.Transitions.expand self a)
  | .collection _ a => .ok (present a)
  | .integer _ => .error "behavioral.expected-formula"

def heads : Value k n → Except String (Ty k × Expression.Collection k n)
  | .collection t a => .ok (t, a)
  | .integer a => .ok (.integers, .integer a)
  | _ => .error "behavioral.expected-collection"

def isInteger (v : IR.BehavioralStructural.Validated k) (d : Fin k) : Bool :=
  (v.core.structural.get d).origin == .integer

def classType (v : IR.BehavioralStructural.Validated k) (d : Fin k) : Ty k :=
  if isInteger v d then .integers else .objects d

def classes (v : IR.BehavioralStructural.Validated k) : Ty k → List (Fin k)
  | .objects d => [d]
  | .integers => (List.finRange k).filter (isInteger v)
  | .empty => []
  | .mixed ds => ds

def classUnion (v : IR.BehavioralStructural.Validated k) (ds : List (Fin k)) : Ty k :=
  match ds.eraseDups with
  | [] => .empty
  | [d] => classType v d
  | ds => .mixed ds

def common (v : IR.BehavioralStructural.Validated k) (a b : Ty k) : Except String (Ty k) :=
  .ok (classUnion v (classes v a ++ classes v b))

def overlap (v : IR.BehavioralStructural.Validated k) (a b : Ty k) : Except String (Ty k) := do
  let ds := (classes v a).flatMap fun x => (classes v b).filterMap fun y =>
    if y ∈ v.analysis.ancestors[x] then some x
    else if x ∈ v.analysis.ancestors[y] then some y else none
  if ds.isEmpty && a != .empty && b != .empty then throw "behavioral.incompatible-collections"
  return classUnion v ds

/-- First navigation from the fixed context identity differs from navigation
from observed standalone `this`, which is empty after the context disappears. -/
def navigateSet (step : Step k) (a : SetExpr k n) : SetExpr k n :=
  match a with
  | .this => .thisStep step
  | _ => .step step a

def navigateCollection (step : Step k) : Expression.Collection k n → Expression.Collection k n
  | .set a => .set (navigateSet step a)
  | a => .step step a

/-- Parentless abstract types have the actual parents of their concrete
realizations. No single parent is fabricated for such a view. -/
def parentType (v : IR.BehavioralStructural.Validated k) (d : Fin k) : Ty k :=
  match (v.core.structural.get d).parent with
  | some p => classType v p
  | none => classUnion v ((List.finRange k).flatMap fun actual =>
      if d ∈ v.analysis.ancestors[actual] && !(v.core.structural.get actual).isAbstract then
        (v.core.structural.get actual).parent.toList
      else [])

-- [impl->req~compiler-behavioral-elaboration~1]
def target (v : IR.BehavioralStructural.Validated k) : Value k n → Except String (Value k n)
  | .collection (.objects d) a =>
      match IR.BehavioralSupport.referenceView v d with
      | none => .ok (.collection (.objects d) a)
      | some r => .ok (.collection (classType v r.target)
          (match a with | .set a => .set (.step (.deref d) a) | a => .step (.deref d) a))
  | .collection (.mixed ds) a =>
      let pieces := ds.map fun d =>
        match IR.BehavioralSupport.referenceView v d with
        | none => (d, Expression.Collection.ofType d a)
        | some r => (r.target, Expression.Collection.step (.deref d) (.ofType d a))
      .ok (.collection (classUnion v (pieces.map Prod.fst))
        (pieces.foldl (fun acc p => .union acc p.2) (.set .empty)))
  | a => .ok a

def integer (v : IR.BehavioralStructural.Validated k) (a : Value k n) : Except String (Expression.Integer k n) := do
  match ← target v a with
  | .integer a => return a
  | .collection .integers a | .collection .empty a => return .coerce a
  | _ => throw "behavioral.expected-integer"

end ClaferCompiler.Frontend.Behavioral.Values
