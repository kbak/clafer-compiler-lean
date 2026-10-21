module

public import ClaferCompiler.IR.ExprBounds

@[expose] public section
namespace ClaferCompiler.IR.Expr

/-- Nonprimitive objects and integer values inhabit disjoint namespaces. -/
inductive Atom where
  | object (id : Nat)
  | integer (value : Int)
  deriving DecidableEq, Repr

/-!
[impl->req~compiler-arithmetic~1]
-/
/-- Collections are sets: repeating the same integer object is still a singleton.
This helper is not a general expression or structural-candidate evaluator. -/
def extract : List Atom → Option Int
  | [] => none
  | .object _ :: _ => none
  | .integer i :: tail => if tail.all (· == .integer i) then some i else none

/-- Original link IDs and endpoints survive finite observation. Reduced relation
counts and reference-head object counts can therefore remain distinct. -/
structure Link where
  id : Nat
  source : Atom
  target : Atom
  deriving DecidableEq, Repr

structure Observation (n m : Nat) where
  objects : Vector (List Atom) n
  links : Vector (List Link) m
  deriving DecidableEq, Repr

structure Environment where
  this : Atom
  locals : List Atom
  deriving DecidableEq, Repr

def Environment.push (ρ : Environment) (a : Atom) : Environment :=
  ⟨ρ.this, a :: ρ.locals⟩

def member (s : Support n m) (o : Observation n m) (x : Fin n) (a : Atom) : Bool :=
  if s.integer[x] then match a with | .integer _ => true | .object _ => false
  else o.objects[x].contains a

def localsValid (s : Support n m) (o : Observation n m) (Γ : List (Local n)) (xs : List Atom) : Bool :=
  decide (Γ.length = xs.length) && (Γ.zip xs).all (fun (b, a) => member s o b.element a)

@[simp] theorem localsValid_cons (s : Support n m) (o : Observation n m)
    (b : Local n) (Γ : List (Local n)) (a : Atom) (xs : List Atom) :
    localsValid s o (b :: Γ) (a :: xs) = (member s o b.element a && localsValid s o Γ xs) := by
  simp [localsValid, Bool.and_left_comm]

def Environment.valid (s : Support n m) (o : Observation n m) (Γ : List (Local n))
    (ρ : Environment) : Bool := member s o s.context ρ.this && localsValid s o Γ ρ.locals

/-- Validate finite budgets and every observed numeric value without consulting
constraint truth. Primitive budgets count observations, never all integers. -/
def Observation.withinBounds (s : Support n m) (b : Bounds n) (o : Observation n m) : Bool :=
  decide (1 ≤ b.width ∧ b.width ≤ 16) && (List.finRange n).all (fun x =>
    (List.finRange n).all (fun y =>
      s.classes[x] != s.classes[y] ||
        (o.objects[x].all (o.objects[y].contains) && o.objects[y].all (o.objects[x].contains))) &&
    decide (o.objects[x].eraseDups.length ≤ b.extents[x]) &&
    o.objects[x].all (fun a => match a with
      | .object _ => !s.integer[x]
      | .integer i => s.integer[x] && b.integers[x].fits b.width &&
          decide (b.integers[x].lower ≤ i ∧ i ≤ b.integers[x].upper))) &&
    (List.finRange m).all (fun e => o.links[e].all (fun l =>
      o.objects[s.maps[e].source].contains l.source &&
      o.objects[s.maps[e].target].contains l.target))

def localsRecorded (o : Observation n m) (Γ : List (Local n)) (xs : List Atom) : Bool :=
  decide (Γ.length = xs.length) && (Γ.zip xs).all (fun (b, a) => o.objects[b.element].contains a)

/-- Numeric candidate preconditions include every externally bound object and
`this` in the finite observation; raw admissibility alone is not a range proof. -/
def Environment.bounded (s : Support n m) (b : Bounds n) (o : Observation n m)
    (Γ : List (Local n)) (ρ : Environment) : Bool :=
  ρ.valid s o Γ && o.withinBounds s b && o.objects[s.context].contains ρ.this &&
    localsRecorded o Γ ρ.locals

end ClaferCompiler.IR.Expr
