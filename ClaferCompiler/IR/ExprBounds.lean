module

public import ClaferCompiler.IR.Expr

@[expose] public section
namespace ClaferCompiler.IR.Expr

structure Interval where
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

def Interval.Contains (r : Interval) (i : Int) := r.lower ≤ i ∧ i ≤ r.upper

def Interval.add (a b : Interval) : Interval := ⟨a.lower + b.lower, a.upper + b.upper⟩
def Interval.subtract (a b : Interval) : Interval := ⟨a.lower - b.upper, a.upper - b.lower⟩

def signedRange (width : Nat) : Interval := ⟨-(2 ^ (width - 1) : Int), 2 ^ (width - 1) - 1⟩
def Interval.fits (width : Nat) (r : Interval) : Bool :=
  decide (1 ≤ width ∧ width ≤ 16 ∧ r.lower ≤ r.upper ∧
    (signedRange width).lower ≤ r.lower ∧ r.upper ≤ (signedRange width).upper)

/-- Explicit finite extent budgets and primitive observation intervals. These are
bounds on observed values, never a finite replacement for mathematical Int. -/
structure Bounds (n : Nat) where
  width : Nat
  extents : Vector Nat n
  integers : Vector Interval n
  deriving DecidableEq, Repr

inductive Estimate where
  | truth | number (range : Interval) | collection (budget : Nat)
  deriving DecidableEq, Repr

def boundsError : Structural.Diagnostic :=
  { category := .unsupported, code := "expr.unsafe-bounds" }

def number (b : Bounds n) (r : Interval) : Except Structural.Diagnostic Estimate :=
  if r.fits b.width then .ok (.number r) else .error boundsError

def combineNumbers (b : Bounds n) (op : Arithmetic) : Estimate → Estimate →
    Except Structural.Diagnostic Estimate
  | .number x, .number y => number b (match op with | .add => x.add y | .subtract => x.subtract y)
  | _, _ => .error { category := .malformed, code := "expr.type-scope-or-span" }

/-- Conservative syntax-directed bounds, inspecting both Boolean operands and
all binder bodies even when a particular candidate would make them vacuous.
Use through `validateBounds`; its type check precedes this analysis. No solver is called. -/
def analyzeAt (s : Support n m) (b : Bounds n) : (fuel : Nat) → (e : Syntax n m) →
    e.depth < fuel → Except Structural.Diagnostic Estimate :=
  Nat.rec (motive := fun fuel => (e : Syntax n m) → e.depth < fuel →
    Except Structural.Diagnostic Estimate)
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun _ next e h => by
      cases e with
      | boolean _ => exact .ok .truth

      | integer i => exact number b ⟨i, i⟩

      | this => exact .ok (.collection 1)

      | var _ => exact .ok (.collection 1)

      | extent x => exact .ok (.collection b.extents[x])

      | map e => exact .ok (.collection (b.extents[s.maps[e].source] * b.extents[s.maps[e].target]))

      | and a c => exact do
          let _ ← next a (by simp_all only [Syntax.depth]; omega)
          let _ ← next c (by simp_all only [Syntax.depth]; omega)
          return .truth
      | equal _ a c => exact do
          let _ ← next a (by simp_all only [Syntax.depth]; omega)
          let _ ← next c (by simp_all only [Syntax.depth]; omega)
          return .truth
      | less a c => exact do
          let _ ← next a (by simp_all only [Syntax.depth]; omega)
          let _ ← next c (by simp_all only [Syntax.depth]; omega)
          return .truth
      | subset _ a c => exact do
          let _ ← next a (by simp_all only [Syntax.depth]; omega)
          let _ ← next c (by simp_all only [Syntax.depth]; omega)
          return .truth
      | not a => exact do let _ ← next a (by simp_all only [Syntax.depth]; omega); return .truth

      | arithmetic op a c => exact do combineNumbers b op (← next a (by simp_all only [Syntax.depth]; omega)) (← next c (by simp_all only [Syntax.depth]; omega))

      | integerOf x a => exact do let _ ← next a (by simp_all only [Syntax.depth]; omega); number b b.integers[x]

      | cardinality _ a => exact do
          match ← next a (by simp_all only [Syntax.depth]; omega) with
          | .collection k => number b ⟨0, k⟩
          | _ => .error boundsError
      | setOp op _ a c => exact do
          match (← next a (by simp_all only [Syntax.depth]; omega)), (← next c (by simp_all only [Syntax.depth]; omega)) with
          | .collection x, .collection y => return .collection (match op with
              | .union => x + y | .difference => x | .intersection => min x y)
          | _, _ => .error boundsError
      | image _ _ a c => exact do
          let _ ← next a (by simp_all only [Syntax.depth]; omega)
          match ← next c (by simp_all only [Syntax.depth]; omega) with
          | .collection y => return .collection y
          | _ => .error boundsError
      | join _ _ _ a c => exact do
          match (← next a (by simp_all only [Syntax.depth]; omega)), (← next c (by simp_all only [Syntax.depth]; omega)) with
          | .collection x, .collection y => return .collection (x * y)
          | _, _ => .error boundsError
      | widenObjects _ _ _ a => exact next a (by simp_all only [Syntax.depth]; omega)

      | widenRelation _ _ _ _ _ _ a => exact next a (by simp_all only [Syntax.depth]; omega)

      | located _ a => exact next a (by simp_all only [Syntax.depth]; omega)

      | all _ d a => exact do let _ ← next d (by simp_all only [Syntax.depth]; omega); let _ ← next a (by simp_all only [Syntax.depth]; omega); return .truth)

def analyze (s : Support n m) (b : Bounds n) (e : Term n m) : Except Structural.Diagnostic Estimate :=
  analyzeAt s b e.budget e.raw e.bound

/-- Admission preserves the original syntax and carries a separately computed
range estimate; an admitted expression may still be undefined or false. -/
structure Admitted (s : Support n m) (b : Bounds n) (Γ : List (Local n)) (t : Ty n) where
  checked : Checked s Γ t
  estimate : Estimate
  width : 1 ≤ b.width ∧ b.width ≤ 16
  analyzed : analyze s b checked.term = .ok estimate

/-!
[impl->req~compiler-arithmetic~1]
-/
def validateBounds (s : Support n m) (b : Bounds n) (Γ : List (Local n)) (t : Ty n)
    (e : Term n m) : Except Structural.Diagnostic (Admitted s b Γ t) :=
  match check s Γ t e with
  | .error d => .error d
  | .ok checked =>
    if hw : 1 ≤ b.width ∧ b.width ≤ 16 then
      match ha : analyze s b checked.term with
      | .error d => .error d
      | .ok estimate => .ok ⟨checked, estimate, hw, ha⟩
    else .error boundsError

end ClaferCompiler.IR.Expr
