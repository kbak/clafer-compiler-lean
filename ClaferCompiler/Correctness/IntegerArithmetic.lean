module

public import ClaferCompiler.Backend.Alloy.Semantics
public import Mathlib.Data.List.Basic

public section

namespace ClaferCompiler.Backend.Alloy

/-! Integer construction and interval theorems are independent of source truth.
[proof->req~compiler-target-arithmetic~1] -/

inductive Integer.Term : Integer → Prop where
  | literal (n) : Term (.literal n)
  | count (r) : Term (.count r)
  | scalar (o lo hi r) : Term (.scalar o lo hi r)
  | add : Term a → Term b → Term (.add a b)
  | subtract : Term a → Term b → Term (.subtract a b)

private theorem Integer.Term.run_exists (h : Integer.Term n) (alg : IntegerAlgebra α) :
    ∃ x, ∀ stack, n.code.foldl alg.step (some stack) = some (x :: stack) := by
  induction h with
  | literal n => exact ⟨alg.literal n, fun _ => rfl⟩
  | count r => exact ⟨alg.count r, fun _ => rfl⟩
  | scalar o lo hi r => exact ⟨alg.scalar o lo hi r, fun _ => rfl⟩
  | add ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.add a b, fun _ => by
      simp [Integer.add, List.foldl_append, ha, hb, IntegerAlgebra.step]⟩
  | subtract ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.subtract a b, fun _ => by
      simp [Integer.subtract, List.foldl_append, ha, hb, IntegerAlgebra.step]⟩

theorem Integer.Term.run (h : Integer.Term n) (alg : IntegerAlgebra α)
    (fallback : α) (stack : List α) :
    n.code.foldl alg.step (some stack) = some (n.fold alg fallback :: stack) := by
  obtain ⟨x, hx⟩ := h.run_exists alg
  simp [Integer.fold, hx]

theorem Integer.fold_add (ha : Integer.Term a) (hb : Integer.Term b)
    (alg : IntegerAlgebra α) (z : α) :
    (a.add b).fold alg z = alg.add (a.fold alg z) (b.fold alg z) := by
  unfold Integer.fold
  simp only [Integer.add, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Integer.fold_subtract (ha : Integer.Term a) (hb : Integer.Term b)
    (alg : IntegerAlgebra α) (z : α) :
    (a.subtract b).fold alg z = alg.subtract (a.fold alg z) (b.fold alg z) := by
  unfold Integer.fold
  simp only [Integer.subtract, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Integer.eval_add (ha : Integer.Term a) (hb : Integer.Term b)
    (w : Nat) (i : Instance) (env : List Nat) :
    (a.add b).eval w i env = (do boundedInt w ((← a.eval w i env) + (← b.eval w i env))) :=
  Integer.fold_add ha hb _ _

theorem Integer.eval_subtract (ha : Integer.Term a) (hb : Integer.Term b)
    (w : Nat) (i : Instance) (env : List Nat) :
    (a.subtract b).eval w i env = (do boundedInt w ((← a.eval w i env) - (← b.eval w i env))) :=
  Integer.fold_subtract ha hb _ _

theorem Integer.add_defined_iff (ha : Integer.Term a) (hb : Integer.Term b)
    (w : Nat) (i : Instance) (env : List Nat) (z : Int) :
    (a.add b).eval w i env = some z ↔
    ∃ x y, a.eval w i env = some x ∧ b.eval w i env = some y ∧
      fitsInt w (x + y) = true ∧ z = x + y := by
  rw [Integer.eval_add ha hb]
  cases hx : a.eval w i env <;> cases hy : b.eval w i env <;>
    simp [boundedInt]
  intro _
  exact eq_comm

theorem Integer.subtract_defined_iff (ha : Integer.Term a) (hb : Integer.Term b)
    (w : Nat) (i : Instance) (env : List Nat) (z : Int) :
    (a.subtract b).eval w i env = some z ↔
    ∃ x y, a.eval w i env = some x ∧ b.eval w i env = some y ∧
      fitsInt w (x - y) = true ∧ z = x - y := by
  rw [Integer.eval_subtract ha hb]
  cases hx : a.eval w i env <;> cases hy : b.eval w i env <;>
    simp [boundedInt]
  intro _
  exact eq_comm

def IntRange.Contains (r : IntRange) (v : Int) : Prop := r.lower ≤ v ∧ v ≤ r.upper

theorem IntRange.checked_iff (w : Nat) (r out : IntRange) :
    r.checked w = some out ↔ r = out ∧ r.lower ≤ r.upper ∧
      fitsInt w r.lower = true ∧ fitsInt w r.upper = true := by
  simp [IntRange.checked, and_assoc, and_comm]

theorem IntRange.representable {r : IntRange} {w : Nat} {v : Int} (h : r.checked w = some r) (hv : r.Contains v) :
    boundedInt w v = some v := by
  obtain ⟨_, _, hl, hu⟩ := (IntRange.checked_iff w r r).mp h
  simp only [fitsInt, Bool.and_eq_true, decide_eq_true_eq] at hl hu
  apply (boundedInt_some_iff _ _).mpr
  simp only [fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  dsimp [IntRange.Contains] at hv
  omega

theorem IntRange.add_contains {a b : IntRange} {x y : Int} (ha : a.Contains x) (hb : b.Contains y) :
    (IntRange.mk (a.lower + b.lower) (a.upper + b.upper)).Contains (x + y) := by
  dsimp [IntRange.Contains] at *
  omega

theorem IntRange.subtract_contains {a b : IntRange} {x y : Int} (ha : a.Contains x) (hb : b.Contains y) :
    (IntRange.mk (a.lower - b.upper) (a.upper - b.lower)).Contains (x - y) := by
  dsimp [IntRange.Contains] at *
  omega

/-- Mathematical target evaluation removes bitwidth checks only. It uses the
same independently defined finite relation interpretation, not source denotation. -/
def Integer.mathematical (i : Instance) (env : List Nat) (n : Integer) : Option Int :=
  n.fold {
    literal := some
    count := fun r => some (Int.ofNat (r.eval i env).eraseDups.length)
    scalar := fun o lo hi r => some (i.scalarValue env o lo hi r)
    add := fun a b => do pure ((← a) + (← b))
    subtract := fun a b => do pure ((← a) - (← b))
  } none

/-- Concrete leaf capacity premise: each counted relation fits its independent
column inventory. No expression value, definedness or final truth is assumed. -/
def Integer.CountsFit (n : Integer) (m : Module) (depth : Nat)
    (i : Instance) (env : List Nat) : Prop :=
  ∀ r, IntegerOp.count r ∈ n.code →
    (r.eval i env).eraseDups.length ≤
      (r.columns m.command.scopes m.schema (List.replicate depth 1)).foldl (· * ·) 1

theorem Instance.scalarValue_range (i : Instance) (env : List Nat) (o : Nat)
    (lo hi : Int) (r : Rel) (h : lo ≤ hi) :
    (IntRange.mk lo hi).Contains (i.scalarValue env o lo hi r) := by
  unfold Instance.scalarValue
  split
  · split
    · split <;> simp_all [IntRange.Contains]
    · exact ⟨Int.le_refl _, h⟩
  · exact ⟨Int.le_refl _, h⟩

/-- Checked intervals guarantee that every integer intermediate is defined and
equal to mathematical arithmetic, assuming the explicit count inventories.
Deriving those inventories for arbitrary target relations is a separate theorem. -/
theorem Integer.range_sound {n : Integer} {m : Module} {depth : Nat}
    {i : Instance} {env : List Nat} {interval : IntRange} (ht : Integer.Term n)
    (hc : n.CountsFit m depth i env) (hr : n.range m depth = some interval) :
    ∃ value, n.mathematical i env = some value ∧
      n.eval m.command.bitwidth i env = some value ∧ interval.Contains value := by
  induction ht generalizing interval with
  | literal v =>
    change (IntRange.mk v v).checked m.command.bitwidth = some interval at hr
    obtain ⟨rfl, _⟩ := (IntRange.checked_iff _ _ _).mp hr
    have hv : (IntRange.mk v v).Contains v := ⟨Int.le_refl _, Int.le_refl _⟩
    exact ⟨v, rfl, IntRange.representable hr hv, hv⟩
  | count r =>
    change (IntRange.mk 0 _).checked m.command.bitwidth = some interval at hr
    obtain ⟨rfl, _⟩ := (IntRange.checked_iff _ _ _).mp hr
    have hv : (IntRange.mk 0 _).Contains (Int.ofNat (r.eval i env).eraseDups.length) :=
      ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (hc r (by simp [Integer.count]))⟩
    exact ⟨_, rfl, IntRange.representable hr hv, hv⟩
  | scalar o lo hi r =>
    change (IntRange.mk lo hi).checked m.command.bitwidth = some interval at hr
    obtain ⟨rfl, hlo, _⟩ := (IntRange.checked_iff _ _ _).mp hr
    have hv := i.scalarValue_range env o lo hi r hlo
    exact ⟨_, rfl, IntRange.representable hr hv, hv⟩
  | @add a b ha hb ia ib =>
    have hca : a.CountsFit m depth i env := fun r h => hc r (by simp [Integer.add, h])
    have hcb : b.CountsFit m depth i env := fun r h => hc r (by simp [Integer.add, h])
    simp only [Integer.range, Integer.fold_add ha hb] at hr
    change (do
      let a ← a.range m depth; let b ← b.range m depth
      IntRange.checked m.command.bitwidth ⟨a.lower + b.lower, a.upper + b.upper⟩) = some interval at hr
    cases hra : a.range m depth with
    | none => simp [hra] at hr
    | some ra =>
      cases hrb : b.range m depth with
      | none => simp [hra, hrb] at hr
      | some rb =>
        simp only [hra, hrb] at hr
        obtain ⟨rfl, _⟩ := (IntRange.checked_iff _ _ _).mp hr
        obtain ⟨x, hx, ex, bx⟩ := ia hca hra
        obtain ⟨y, hy, ey, by'⟩ := ib hcb hrb
        have hv := IntRange.add_contains bx by'
        refine ⟨x + y, ?_, ?_, hv⟩
        · simp only [Integer.mathematical, Integer.fold_add ha hb] at hx hy ⊢
          exact congrArg₂ (fun a b : Option Int => do pure ((← a) + (← b))) hx hy
        · rw [Integer.eval_add ha hb, ex, ey]
          exact IntRange.representable hr hv
  | @subtract a b ha hb ia ib =>
    have hca : a.CountsFit m depth i env := fun r h => hc r (by simp [Integer.subtract, h])
    have hcb : b.CountsFit m depth i env := fun r h => hc r (by simp [Integer.subtract, h])
    simp only [Integer.range, Integer.fold_subtract ha hb] at hr
    change (do
      let a ← a.range m depth; let b ← b.range m depth
      IntRange.checked m.command.bitwidth ⟨a.lower - b.upper, a.upper - b.lower⟩) = some interval at hr
    cases hra : a.range m depth with
    | none => simp [hra] at hr
    | some ra =>
      cases hrb : b.range m depth with
      | none => simp [hra, hrb] at hr
      | some rb =>
        simp only [hra, hrb] at hr
        obtain ⟨rfl, _⟩ := (IntRange.checked_iff _ _ _).mp hr
        obtain ⟨x, hx, ex, bx⟩ := ia hca hra
        obtain ⟨y, hy, ey, by'⟩ := ib hcb hrb
        have hv := IntRange.subtract_contains bx by'
        refine ⟨x - y, ?_, ?_, hv⟩
        · simp only [Integer.mathematical, Integer.fold_subtract ha hb] at hx hy ⊢
          exact congrArg₂ (fun a b : Option Int => do pure ((← a) - (← b))) hx hy
        · rw [Integer.eval_subtract ha hb, ex, ey]
          exact IntRange.representable hr hv

end ClaferCompiler.Backend.Alloy
