module

public import ClaferCompiler.IR.ExprObservation

@[expose] public section
namespace ClaferCompiler.IR.BehavioralArithmetic
open Expr

inductive Binary where
  | add | subtract | multiply | divide | remainder
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-structural-bridge~1]
def Binary.apply : Binary → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .subtract, x, y => some (x - y)
  | .multiply, x, y => some (x * y)
  | .divide, x, y => if y = 0 then none else some (x.tdiv y)
  | .remainder, x, y => if y = 0 then none else some (x.tmod y)

def Binary.eval (op : Binary) (x y : Option Int) : Option Int :=
  x.bind fun a => y.bind fun b => op.apply a b

/-- Boolean operations inspect every operand. In particular a false condition
does not make an undefined operand or branch disappear. -/
def strictAnd (a b : Option Bool) : Option Bool := a.bind fun x => b.map (x && ·)
def conditional (condition : Option Bool) (yes no : Option α) : Option α :=
  condition.bind fun c => yes.bind fun a => no.map fun b => if c then a else b

/-- Finite observed mathematical values. Deduplication is only for an implicit
integer *set* operand, never for occurrence-indexed explicit aggregation.
The existing fuel/recursor pattern avoids compiler-generated unsafe workers;
`List.rec` itself has no native code generator in the pinned Lean release. -/
def coerceAt : (fuel : Nat) → (values : List Int) → values.length < fuel → Int :=
  Nat.rec (motive := fun fuel => (values : List Int) → values.length < fuel → Int)
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun _ next values h => match values with
      | [] => 0
      | x :: xs =>
        let total := next xs (by simp only [List.length_cons] at h; omega)
        if x ∈ xs then total else x + total)

def coerce (values : List Int) : Int := coerceAt (values.length + 1) values (by omega)

@[simp] theorem coerce_nil : coerce [] = 0 := rfl
@[simp] theorem coerce_cons (x : Int) (xs : List Int) :
    coerce (x :: xs) = if x ∈ xs then coerce xs else x + coerce xs := rfl
def extract (values : List Int) : Option Int :=
  Expr.extract (values.map Atom.integer)

def minimum (values : List Int) : List Int := values.min?.toList
def maximum (values : List Int) : List Int := values.max?.toList

inductive Fold where
  | sum | product
  deriving DecidableEq, Repr

/-- Each list is one syntactic operand, with its original head occurrences.
Repeated targets and overlap between operands contribute separately. -/
def Fold.eval (op : Fold) (operands : List (List (Option Int))) : Option Int := do
  let values ← operands.flatten.mapM id
  return match op with | .sum => values.sum | .product => values.prod

def magnitude (r : Interval) : Nat := max r.lower.natAbs r.upper.natAbs
def symmetric (bound : Nat) : Interval := ⟨-(bound : Int), bound⟩

def Binary.range : Binary → Interval → Interval → Interval
  | .add, a, b => a.add b
  | .subtract, a, b => a.subtract b
  | .multiply, a, b => symmetric (magnitude a * magnitude b)
  | .divide, a, _ | .remainder, a, _ => symmetric (magnitude a)

def Binary.nonzero (op : Binary) (r : Interval) : Bool :=
  match op with
  | .divide | .remainder => r.upper < 0 || 0 < r.lower
  | _ => true

structure Checked (op : Binary) (width : Nat) (a b : Interval) : Type where
  inputs : a.fits width = true ∧ b.fits width = true
  divisor : op.nonzero b = true
  result : (op.range a b).fits width = true

def validateOperation (op : Binary) (width : Nat) (a b : Interval) :
    Except Structural.Diagnostic (Checked op width a b) :=
  if ha : a.fits width = true ∧ b.fits width = true then
    if hd : op.nonzero b = true then
      if hr : (op.range a b).fits width = true then .ok ⟨ha, hd, hr⟩
      else .error { category := .unsupported, code := "behavioral.integer-range" }
    else .error { category := .unsupported, code := "behavioral.possible-zero-divisor" }
  else .error { category := .unsupported, code := "behavioral.integer-range" }

/-- Conservative budgets include every possible contributing occurrence and
every prefix fold. They do not assume that source constraints hold. -/
def setSumRange (budget : Nat) (values : Interval) : Interval :=
  symmetric (budget * magnitude values)

def productRange (budget : Nat) (values : Interval) : Interval :=
  symmetric (max 1 (magnitude values) ^ budget)

def countRange (budget : Nat) : Interval := ⟨0, budget⟩
def negateRange (values : Interval) : Interval := ⟨-values.upper, -values.lower⟩

end ClaferCompiler.IR.BehavioralArithmetic
