module

public import ClaferCompiler.Backend.Alloy.Semantics
public import Mathlib.Data.List.Basic

public section
/-! [proof->req~compiler-structural-representation~1] -/

namespace ClaferCompiler.Backend.Alloy

theorem Instance.scalarFields_of_no_scalars (w : Nat) (s : Schema) (i : Instance)
    (h : ∀ d ∈ s.signatures, d.scalar = false) : i.scalarFields w s = true := by
  apply List.all_eq_true.mpr
  intro pair hp
  have hm := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hp)
  simp [h pair.1 hm]

theorem eraseDups_of_nodup [BEq α] [LawfulBEq α] {xs : List α}
    (h : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons]
    have hf : xs.filter (fun b => !b == x) = xs := by
      apply List.filter_eq_self.mpr
      intro b hb
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      exact fun he => h.1 (he ▸ hb)
    rw [hf, ih h.2]

theorem eraseDups_map_injective [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    (xs.map f).eraseDups = xs.eraseDups.map f := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons]
    have he : (xs.map f).filter (fun b => !b == f x) =
        (xs.filter fun b => !b == x).map f := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro b _
      simp [hf.eq_iff]
    rw [he, eraseDups_map_injective f hf (xs.filter fun b => !b == x)]
    rfl
termination_by xs.length

decreasing_by
  have := List.length_filter_le (fun b => !b == x) xs
  simp only [List.length_cons]
  omega

/-- A construction witness for the postfix relation language. It supplies stack
safety only, without assuming any interpretation or truth. -/
inductive Rel.Term : Rel → Prop where
  | empty (a) : Term (.empty a)
  | sig (i) : Term (.sig i)
  | field (i) : Term (.field i)
  | var (i) : Term (.var i)
  | union : Term a → Term b → Term (.union a b)
  | inter : Term a → Term b → Term (.inter a b)
  | diff : Term a → Term b → Term (.diff a b)
  | product : Term a → Term b → Term (.product a b)
  | join : Term a → Term b → Term (.join a b)
  | transpose : Term a → Term (.transpose a)
  | diagonal : Term a → Term (.diagonal a)

private theorem Rel.Term.run_exists (h : Rel.Term r) (alg : RelAlgebra α) :
    ∃ x, ∀ stack, r.code.foldl alg.step (some stack) = some (x :: stack) := by
  induction h with
  | empty a => exact ⟨alg.empty a, fun _ => rfl⟩
  | sig i => exact ⟨alg.sig i, fun _ => rfl⟩
  | field i => exact ⟨alg.field i, fun _ => rfl⟩
  | var i => exact ⟨alg.var i, fun _ => rfl⟩
  | union ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.union a b, fun _ => by simp [Rel.union, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | inter ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.inter a b, fun _ => by simp [Rel.inter, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | diff ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.diff a b, fun _ => by simp [Rel.diff, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | product ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.product a b, fun _ => by simp [Rel.product, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | join ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.join a b, fun _ => by simp [Rel.join, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | transpose ha ia =>
    obtain ⟨a, ha⟩ := ia
    exact ⟨alg.transpose a, fun _ => by simp [Rel.transpose, List.foldl_append, ha, RelAlgebra.step]⟩

  | diagonal ha ia =>
    obtain ⟨a, ha⟩ := ia
    exact ⟨alg.diagonal a, fun _ => by simp [Rel.diagonal, List.foldl_append, ha, RelAlgebra.step]⟩

theorem Rel.Term.run (h : Rel.Term r) (alg : RelAlgebra α) (fallback : α) (stack : List α) :
    r.code.foldl alg.step (some stack) = some (r.fold alg fallback :: stack) := by
  obtain ⟨x, hx⟩ := h.run_exists alg
  simp [Rel.fold, hx]

theorem Rel.fold_union_term (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.union b).fold alg z = alg.union (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.union, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_join_term (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.join b).fold alg z = alg.join (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.join, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_transpose_term (ha : Rel.Term a) (alg : RelAlgebra α) (z : α) :
    a.transpose.fold alg z = alg.transpose (a.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.transpose, List.foldl_append, ha.run alg z]
  rfl

theorem Rel.fold_inter_term (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.inter b).fold alg z = alg.inter (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.inter, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_diff_term (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.diff b).fold alg z = alg.diff (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.diff, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_product_term (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.product b).fold alg z = alg.product (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.product, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_diagonal_term (ha : Rel.Term a) (alg : RelAlgebra α) (z : α) :
    a.diagonal.fold alg z = alg.diagonal (a.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.diagonal, List.foldl_append, ha.run alg z]
  rfl

@[simp] theorem Rel.eval_empty (i : Instance) (env : List Nat) (a : Arity) :
    (Rel.empty a).eval i env = [] := rfl
@[simp] theorem Rel.eval_sig (i : Instance) (env : List Nat) (s : Nat) :
    (Rel.sig s).eval i env = (i.signatures[s]?.getD []).map (fun x => [x]) := rfl
@[simp] theorem Rel.eval_field (i : Instance) (env : List Nat) (f : Nat) :
    (Rel.field f).eval i env = i.fields[f]?.getD [] := rfl
@[simp] theorem Rel.eval_var (i : Instance) (env : List Nat) (v : Nat) :
    (Rel.var v).eval i env = (env[v]?).toList.map (fun x => [x]) := rfl

theorem Rel.eval_union (ha : Rel.Term a) (hb : Rel.Term b) (i : Instance) (env : List Nat) :
    (a.union b).eval i env = (a.eval i env ++ b.eval i env).eraseDups :=
  Rel.fold_union_term ha hb _ _

theorem Rel.eval_join (ha : Rel.Term a) (hb : Rel.Term b) (i : Instance) (env : List Nat) :
    (a.join b).eval i env = ((a.eval i env).flatMap fun x =>
      ((b.eval i env).filter fun y => x.getLast? == y.head?).map fun y =>
        x.dropLast ++ y.drop 1).eraseDups := Rel.fold_join_term ha hb _ _

theorem Rel.eval_transpose (ha : Rel.Term a) (i : Instance) (env : List Nat) :
    a.transpose.eval i env = ((a.eval i env).map List.reverse).eraseDups :=
  Rel.fold_transpose_term ha _ _

/-- Formula stack safety is independent of relation arity, integer ranges and
satisfaction. These are separate obligations. -/
inductive Formula.Term : Formula → Prop where
  | truth : Term .truth
  | falsity : Term .falsity
  | subset (a b) : Term (.subset a b)
  | neg : Term a → Term (.neg a)
  | equal (a b) : Term (.equal a b)
  | mult (m r) : Term (.mult m r)
  | compare (op a b) : Term (.compare op a b)
  | conj : Term a → Term b → Term (.conj a b)
  | implies : Term a → Term b → Term (.implies a b)
  | all (r) : Term p → Term (.all r p)

private theorem Formula.Term.run_exists (h : Formula.Term p) (alg : FormulaAlgebra α) :
    ∃ x, ∀ stack, p.code.foldl alg.step (some stack) = some (x :: stack) := by
  induction h with
  | truth => exact ⟨alg.truth, fun _ => rfl⟩
  | falsity => exact ⟨alg.falsity, fun _ => rfl⟩
  | subset a b => exact ⟨alg.subset a b, fun _ => rfl⟩
  | neg ha ia =>
    obtain ⟨a, ha⟩ := ia
    exact ⟨alg.neg a, fun _ => by simp [Formula.neg, List.foldl_append, ha, FormulaAlgebra.step]⟩
  | equal a b => exact ⟨alg.equal a b, fun _ => rfl⟩
  | mult m r => exact ⟨alg.mult m r, fun _ => rfl⟩
  | compare op a b => exact ⟨alg.compare op a b, fun _ => rfl⟩
  | conj ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.conj a b, fun _ => by simp [Formula.conj, List.foldl_append, ha, hb, FormulaAlgebra.step]⟩
  | implies ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.implies a b, fun _ => by simp [Formula.implies, List.foldl_append, ha, hb, FormulaAlgebra.step]⟩
  | all r hp ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨alg.all r p, fun _ => by simp [Formula.all, List.foldl_append, hp, FormulaAlgebra.step]⟩

theorem Formula.Term.run (h : Formula.Term p) (alg : FormulaAlgebra α) (fallback : α) (stack : List α) :
    p.code.foldl alg.step (some stack) = some (p.fold alg fallback :: stack) := by
  obtain ⟨x, hx⟩ := h.run_exists alg
  simp [Formula.fold, hx]

theorem Formula.fold_neg_term (ha : Formula.Term a) (alg : FormulaAlgebra α) (z : α) :
    a.neg.fold alg z = alg.neg (a.fold alg z) := by
  unfold Formula.fold
  simp only [Formula.neg, List.foldl_append, ha.run alg z]
  rfl

theorem Formula.fold_conj_term (ha : Formula.Term a) (hb : Formula.Term b)
    (alg : FormulaAlgebra α) (z : α) :
    (a.conj b).fold alg z = alg.conj (a.fold alg z) (b.fold alg z) := by
  unfold Formula.fold
  simp only [Formula.conj, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Formula.fold_implies_term (ha : Formula.Term a) (hb : Formula.Term b)
    (alg : FormulaAlgebra α) (z : α) :
    (a.implies b).fold alg z = alg.implies (a.fold alg z) (b.fold alg z) := by
  unfold Formula.fold
  simp only [Formula.implies, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Formula.fold_all_term (hp : Formula.Term p) (alg : FormulaAlgebra α) (z : α) (r : Rel) :
    (Formula.all r p).fold alg z = alg.all r (p.fold alg z) := by
  unfold Formula.fold
  simp only [Formula.all, List.foldl_append, hp.run alg z]
  rfl

theorem Formula.eval_conj (ha : Formula.Term a) (hb : Formula.Term b)
    (w : Nat) (i : Instance) (env : List Nat) :
    (a.conj b).eval w i env = (do
      let x ← a.eval w i env
      let y ← b.eval w i env
      pure (x && y)) := by
  simp only [Formula.eval, Formula.fold_conj_term ha hb]

theorem Formula.eval_all (hp : Formula.Term p) (w : Nat) (i : Instance) (env : List Nat) (r : Rel) :
    (Formula.all r p).eval w i env = (do
      let vs ← (r.eval i env).mapM fun t => p.eval w i (t.headD 0 :: env)
      pure (vs.all id)) := by
  simp only [Formula.eval, Formula.fold_all_term hp]

/-- A successful strict conjunction forces each conjunct to be defined and true. -/
theorem Formula.eval_conj_true (ha : Formula.Term a) (hb : Formula.Term b)
    (w : Nat) (i : Instance) (env : List Nat) :
    (a.conj b).eval w i env = some true ↔
      a.eval w i env = some true ∧ b.eval w i env = some true := by
  rw [Formula.eval_conj ha hb]
  cases a.eval w i env with
  | none => simp
  | some x => cases x <;> cases b.eval w i env <;> simp

theorem mapM_all_true (xs : List α) (f : α → Option Bool) :
    (do let values ← xs.mapM f; pure (values.all id)) = some true ↔
      ∀ x ∈ xs, f x = some true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx]
    | some b =>
      cases hs : xs.mapM f with
      | none => simp [hs] at ih; simp [List.mapM_cons, hx, hs, ih]
      | some ys =>
        simp [hs] at ih
        cases b <;> simp [List.mapM_cons, hx, hs, ← ih]

theorem Formula.eval_all_true (hp : Formula.Term p)
    (w : Nat) (i : Instance) (env : List Nat) (r : Rel) :
    (Formula.all r p).eval w i env = some true ↔
      ∀ tuple ∈ r.eval i env, p.eval w i (tuple.headD 0 :: env) = some true := by
  rw [Formula.eval_all hp]
  exact mapM_all_true _ _

/-- Each generated fact is defined and true whenever the independent target
module is satisfied; no source bridge is assumed. -/
theorem Module.fact_true (m : Module) (i : Instance) (h : m.eval i = some true)
    (f : Formula) (hf : f ∈ m.facts) : f.eval m.command.bitwidth i [] = some true := by
  have hm : (do
      let vs ← m.facts.mapM (fun p => p.eval m.command.bitwidth i [])
      pure (vs.all id)) = some true := by
    unfold Module.eval at h
    cases hs : m.facts.mapM (fun p => p.eval m.command.bitwidth i []) with
    | none => simp [hs] at h
    | some vs =>
      cases hb : m.command.body.eval m.command.bitwidth i [] with
      | none => simp [hs, hb] at h
      | some b =>
        simp [hs, hb] at h
        simp [h.1.1]
  exact (mapM_all_true _ _).mp hm f hf

end ClaferCompiler.Backend.Alloy
