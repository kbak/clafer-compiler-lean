module

public import ClaferCompiler.Correctness.Behavioral.Expressions

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open Encoding

/-- The selected formula slice emits no partial integer comparisons. -/
def NoArithmetic (p : Formula) : Prop :=
  ∀ op a b, FormulaOp.compare op a b ∉ p.code

@[simp] theorem noArithmetic_truth : NoArithmetic .truth := by intro op a b; simp [Formula.truth]
@[simp] theorem noArithmetic_falsity : NoArithmetic .falsity := by intro op a b; simp [Formula.falsity]
@[simp] theorem noArithmetic_equal (a b : Rel) : NoArithmetic (.equal a b) := by intro op x y; simp [Formula.equal]
@[simp] theorem noArithmetic_subset (a b : Rel) : NoArithmetic (.subset a b) := by intro op x y; simp [Formula.subset]
@[simp] theorem noArithmetic_mult (m : Backend.Alloy.Multiplicity) (r : Rel) : NoArithmetic (.mult m r) := by intro op x y; simp [Formula.mult]
@[simp] theorem noArithmetic_unary (op : Unary) (p : Formula) :
    NoArithmetic (.unary op p) ↔ NoArithmetic p := by simp [NoArithmetic, Formula.unary]
@[simp] theorem noArithmetic_binary (op : Binary) (p q : Formula) :
    NoArithmetic (.binary op p q) ↔ NoArithmetic p ∧ NoArithmetic q := by
  simp [NoArithmetic, Formula.binary, forall_and]
@[simp] theorem noArithmetic_all (r : Rel) (p : Formula) :
    NoArithmetic (.all r p) ↔ NoArithmetic p := by simp [NoArithmetic, Formula.all]
@[simp] theorem noArithmetic_exists (r : Rel) (p : Formula) :
    NoArithmetic (.exists_ r p) ↔ NoArithmetic p := by simp [NoArithmetic, Formula.exists_]

-- [proof->req~compiler-behavioral-correctness~1]
theorem noArithmetic_defined (hb : Formula.Built p) (hr : NoArithmetic p)
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat) : p.Defined s w τ e t := by
  induction hb generalizing e t with
  | truth => trivial
  | falsity => trivial
  | equal => trivial
  | subset => trivial
  | mult => trivial
  | compare op a b => exact (hr op a b (by simp [Formula.compare])).elim
  | @unary op p hp ih =>
    have ih' : ∀ e t, p.fold (definedAlgebra s w τ) (fun _ _ => False) e t :=
      ih ((noArithmetic_unary _ _).mp hr)
    unfold Formula.Defined
    rw [Formula.fold_unary _ _ _ _ hp]
    cases op <;> dsimp only [definedAlgebra]
    all_goals first | exact ih' _ _ | exact fun _ _ => ih' _ _
  | @binary op p q hp hq ihp ihq =>
    have hrs := (noArithmetic_binary _ _ _).mp hr
    have ihp' : ∀ e t, p.fold (definedAlgebra s w τ) (fun _ _ => False) e t := ihp hrs.1
    have ihq' : ∀ e t, q.fold (definedAlgebra s w τ) (fun _ _ => False) e t := ihq hrs.2
    unfold Formula.Defined
    rw [Formula.fold_binary _ _ _ _ _ hp hq]
    cases op <;> dsimp only [definedAlgebra]
    all_goals first | exact ⟨ihp' _ _, ihq' _ _⟩ | exact fun _ _ => ⟨ihp' _ _, ihq' _ _⟩
  | @all r p hp ih =>
    have ih' : ∀ e t, p.fold (definedAlgebra s w τ) (fun _ _ => False) e t :=
      ih ((noArithmetic_all _ _).mp hr)
    unfold Formula.Defined
    rw [Formula.fold_all _ _ _ hp]
    exact fun _ _ => ih' _ _
  | @exists_ r p hp ih =>
    have ih' : ∀ e t, p.fold (definedAlgebra s w τ) (fun _ _ => False) e t :=
      ih ((noArithmetic_exists _ _).mp hr)
    unfold Formula.Defined
    rw [Formula.fold_exists _ _ _ hp]
    exact fun _ _ => ih' _ _

def Relational (a : Translation) : Prop := NoArithmetic a.raw ∧ NoArithmetic a.positive ∧ NoArithmetic a.negative

 theorem atom_noArithmetic (v : IR.Structural.Layout k) (c : Context n)
    (a : IR.Behavioral.Atom k n) (fuel : Nat) (h : sizeOf a < fuel) : NoArithmetic (atom v c a fuel h) := by
  cases a <;> simp [atom]

theorem freezeChoice_relational (hg : NoArithmetic g) (ha : Relational a) (hb : Relational b) :
    Relational (freezeChoice g a b) := by
  simp_all [Relational, freezeChoice]

theorem freezeFrom_relational (aliases : List Rel) (value captured : Rel) (body : Rel → Translation)
    (hbody : ∀ r, Relational (body r)) : Relational (freezeFrom aliases value body captured) := by
  induction aliases generalizing captured with
  | nil => exact hbody _
  | cons x xs ih => exact freezeChoice_relational (noArithmetic_subset _ _) (ih _) (ih _)

theorem freeze_relational (aliases : List Rel) (value : Rel) (body : Rel → Translation)
    (hbody : ∀ r, Relational (body r)) : Relational (freeze aliases value body) :=
  freezeFrom_relational _ _ _ _ hbody

-- [proof->req~compiler-behavioral-correctness~1]
theorem formulaAt_relational (v : IR.Structural.Layout k) (fuel : Nat) {n : Nat}
    (c : Context n) (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    Relational (formulaAt v fuel c a h) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    have hr {n : Nat} (c : Context n) (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) := (ih c a h).1
    have hp {n : Nat} (c : Context n) (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) := (ih c a h).2.1
    have hn {n : Nat} (c : Context n) (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) := (ih c a h).2.2
    cases a with
    | letSet d a => exact freeze_relational _ _ _ (fun _ => ih _ _ _)
    | quant q d a =>
      cases q <;> simp [formulaAt_succ, formulaStep, Relational, Translation.atomic, hr, hp, hn]
    | _ => simp [formulaAt_succ, formulaStep, Relational, Translation.atomic, Translation.map,
        conjunction, disjunction, implication, equivalence, negation, atom_noArithmetic,
        next, eventually, always, strongUntil, weakUntil, Formula.weakUntil, initially, atEnd,
        Formula.birth, parentPresent, present, hr, hp, hn]

theorem formulaAt_defined (v : IR.Structural.Layout k) (fuel : Nat) (c : Context n)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) (p : Option Bool)
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat) :
    (part (formulaAt v fuel c a h) p).Defined s w τ e t := by
  have hb := formulaAt_built v fuel c a h
  have hr := formulaAt_relational v fuel c a h
  cases p with
  | none => exact noArithmetic_defined hb.raw hr.1 s w τ e t
  | some b => cases b with
    | false => exact noArithmetic_defined hb.negative hr.2.2 s w τ e t
    | true => exact noArithmetic_defined hb.positive hr.2.1 s w τ e t

end ClaferCompiler.Correctness.Behavioral
