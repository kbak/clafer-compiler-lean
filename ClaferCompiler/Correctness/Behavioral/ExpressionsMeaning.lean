module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsObservations
public import ClaferCompiler.Correctness.Behavioral.Operators

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral

namespace Encoding

@[simp] theorem holds_truth : Formula.truth.Holds s w τ e t ↔ True := Iff.rfl
@[simp] theorem holds_neg (hp : Formula.Built p) :
    (Formula.unary .neg p).Holds s w τ e t ↔ ¬ p.Holds s w τ e t := by
  simp only [Formula.Holds, Formula.fold_unary _ _ _ _ hp]
  rfl
@[simp] theorem holds_and (hp : Formula.Built p) (hq : Formula.Built q) :
    (Formula.binary .conj p q).Holds s w τ e t ↔ p.Holds s w τ e t ∧ q.Holds s w τ e t := by
  simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ hp hq]
  rfl
@[simp] theorem holds_or (hp : Formula.Built p) (hq : Formula.Built q) :
    (Formula.binary .disj p q).Holds s w τ e t ↔ p.Holds s w τ e t ∨ q.Holds s w τ e t := by
  simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ hp hq]
  rfl
@[simp] theorem holds_implies (hp : Formula.Built p) (hq : Formula.Built q) :
    (Formula.binary .implies p q).Holds s w τ e t ↔ (p.Holds s w τ e t → q.Holds s w τ e t) := by
  simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ hp hq]
  rfl
@[simp] theorem holds_all (hp : Formula.Built p) :
    (Formula.all r p).Holds s w τ e t ↔ ∀ x, [x] ∈ r.eval s w τ e t → p.Holds s w τ (x :: e) t := by
  simp only [Formula.Holds, Formula.fold_all _ _ _ hp]
  rfl
@[simp] theorem holds_exists (hp : Formula.Built p) :
    (Formula.exists_ r p).Holds s w τ e t ↔ ∃ x, [x] ∈ r.eval s w τ e t ∧ p.Holds s w τ (x :: e) t := by
  simp only [Formula.Holds, Formula.fold_exists _ _ _ hp]
  rfl

structure Built (a : Translation) : Prop where
  raw : a.raw.Built
  positive : a.positive.Built
  negative : a.negative.Built

theorem atomic_built (h : Formula.Built p) : Built (Translation.atomic p) :=
  ⟨h, h, .unary .neg h⟩
theorem conjunction_built (ha : Built a) (hb : Built b) : Built (conjunction a b) :=
  ⟨.binary .conj ha.raw hb.raw, .binary .conj ha.positive hb.positive, .binary .disj ha.negative hb.negative⟩
theorem disjunction_built (ha : Built a) (hb : Built b) : Built (disjunction a b) :=
  ⟨.binary .disj ha.raw hb.raw, .binary .disj ha.positive hb.positive, .binary .conj ha.negative hb.negative⟩
theorem negation_built (ha : Built a) : Built (negation a) :=
  ⟨.unary .neg ha.raw, ha.negative, ha.positive⟩
theorem implication_built (ha : Built a) (hb : Built b) : Built (implication a b) :=
  disjunction_built (negation_built ha) hb
theorem equivalence_built (ha : Built a) (hb : Built b) : Built (equivalence a b) :=
  conjunction_built (implication_built ha hb) (implication_built hb ha)
theorem next_built (hp : p.Built) (ha : a.Built) : (next p a).Built :=
  .unary .after (.binary .disj (.unary .neg hp) ha)
theorem eventually_built (hp : p.Built) (ha : a.Built) : (eventually p a).Built :=
  .unary .eventually (.binary .disj (.unary .neg hp) ha)
theorem always_built (hp : p.Built) (ha : a.Built) : (always p a).Built :=
  .binary .disj (.binary .until (.binary .conj hp ha) (.unary .neg hp)) (.unary .always (.binary .conj hp ha))
theorem until_built (hp : p.Built) (ha : a.Built) (hb : b.Built) : (strongUntil p a b).Built :=
  .binary .until (.binary .conj hp ha) (.binary .disj (.unary .neg hp) hb)
theorem weakUntil_built (hp : p.Built) (ha : a.Built) (hb : b.Built) : (weakUntil p a b).Built :=
  .binary .disj (always_built hp ha) (until_built hp ha hb)
theorem initially_built (hp : p.Built) (ha : a.Built) : (initially p a).Built :=
  .binary .implies (.binary .conj hp (.unary .neg (.unary .before hp))) ha
theorem atEnd_built (hp : p.Built) (ha : a.Built) : (atEnd p a).Built :=
  .binary .implies (.binary .conj hp (.unary .neg (.unary .after hp))) ha

theorem freezeChoice_built (hg : g.Built) (ha : Built a) (hb : Built b) : Built (freezeChoice g a b) := by
  constructor
  · exact .binary .disj (.binary .conj hg ha.raw) (.binary .conj (.unary .neg hg) hb.raw)
  · exact .binary .disj (.binary .conj hg ha.positive) (.binary .conj (.unary .neg hg) hb.positive)
  · exact .binary .disj (.binary .conj hg ha.negative) (.binary .conj (.unary .neg hg) hb.negative)

theorem freezeFrom_built (aliases : List Rel) (value captured : Rel) (body : Rel → Translation)
    (hbody : ∀ r, Built (body r)) : Built (freezeFrom aliases value body captured) := by
  induction aliases generalizing captured with
  | nil => exact hbody _
  | cons x xs ih => exact freezeChoice_built (.subset _ _) (ih _) (ih _)

theorem freeze_built (aliases : List Rel) (value : Rel) (body : Rel → Translation)
    (hbody : ∀ r, Built (body r)) : Built (freeze aliases value body) :=
  freezeFrom_built _ _ _ _ hbody

theorem present_built (v : IR.Structural.Layout k) (c : Context n) : (present v c).Built := .mult _ _
theorem parentPresent_built (v : IR.Structural.Layout k) (c : Context n) : (parentPresent v c).Built :=
  .binary .disj (.subset _ _) (.mult _ _)

theorem present_meaning {U : Type} (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat)
    (hp : PrimitiveAgreement v w σ τ f) (c : Context n) (ρ : Clafer.Behavioral.Environment U n)
    (e : Environment) (hc : ContextRep v w τ f c ρ e) (t : Nat) :
    (present v c).Holds (schema v) w τ e t ↔ ρ.this ∈ σ.live t := by
  have h := Relations.unary_some (Relations.unary_inter hp.injective hc.this.1
    (live_term v) (hc.this.2 t) (hp.live e t))
  simpa [present, Set.Nonempty] using h

theorem parentPresent_meaning {U : Type} (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat)
    (hp : PrimitiveAgreement v w σ τ f) (c : Context n) (ρ : Clafer.Behavioral.Environment U n)
    (e : Environment) (hc : ContextRep v w τ f c ρ e) (t : Nat) :
    (parentPresent v c).Holds (schema v) w τ e t ↔ σ.ParentPresent ρ.this t := by
  have hr := Relations.unary_subset hp.injective (hc.this.2 t) (hp.root e t)
  have hi := Relations.unary_image hp.injective hc.this.1 (step_term v .parent)
    (hc.this.2 t) (hp.step .parent e t)
  have hj := Relations.unary_some hi
  rw [parentPresent, holds_or (.subset _ _) (.mult _ _), hr, hj]
  simp [Clafer.Behavioral.Trace.ParentPresent, SemanticsBridge.Behavioral.step,
    Clafer.Behavioral.Step.relation, Set.Nonempty]

theorem initially_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a : Formula) (hp : p.Built) (ha : a.Built) (t : Nat) :
    (initially p a).Holds s w τ e t ↔
      ((p.Holds s w τ e t ∧ (t = 0 ∨ ∃ j, t = j + 1 ∧ ¬ p.Holds s w τ e j)) →
        a.Holds s w τ e t) := by
  have hbirth : p.birth.Built := .binary .conj hp (.unary .neg (.unary .before hp))
  rw [initially, holds_implies hbirth ha]
  cases t with
  | zero => simp [birth_initial s w τ e p hp]
  | succ t => simp [birth_succ s w τ e p hp]

theorem atEnd_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a : Formula) (hp : p.Built) (ha : a.Built) (t : Nat) :
    (atEnd p a).Holds s w τ e t ↔
      ((p.Holds s w τ e t ∧ ¬ p.Holds s w τ e (t + 1)) → a.Holds s w τ e t) := by
  rw [atEnd, holds_implies (.binary .conj hp (.unary .neg (.unary .after hp))) ha,
    holds_and hp (.unary .neg (.unary .after hp)), holds_neg (.unary .after hp)]
  simp only [Formula.Holds, Formula.fold_unary _ _ _ _ hp]
  rfl

theorem formulaAt_built (v : IR.Structural.Layout k) (fuel : Nat) {n : Nat}
    (c : Context n) (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    Built (formulaAt v fuel c a h) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    have hp := parentPresent_built v c
    have hl := present_built v c
    cases a with
    | truth =>
      exact atomic_built .truth
    | atom a =>
      exact atomic_built (atom_built _ _ _ _ _)
    | not a =>
      exact negation_built (ih _ _ _)
    | and a b =>
      exact conjunction_built (ih _ _ _) (ih _ _ _)
    | or a b =>
      exact disjunction_built (ih _ _ _) (ih _ _ _)
    | implies a b =>
      exact implication_built (ih _ _ _) (ih _ _ _)
    | iff a b =>
      exact equivalence_built (ih _ _ _) (ih _ _ _)
    | xor a b =>
      exact negation_built (equivalence_built (ih _ _ _) (ih _ _ _))
    | ite cond a b =>
      exact conjunction_built (implication_built (ih _ _ _) (ih _ _ _))
        (implication_built (negation_built (ih _ _ _)) (ih _ _ _))
    | next a =>
      exact ⟨next_built hp (ih _ _ _).raw, next_built hp (ih _ _ _).positive, next_built hp (ih _ _ _).negative⟩
    | eventually a =>
      exact ⟨eventually_built hp (ih _ _ _).raw, eventually_built hp (ih _ _ _).positive, always_built hp (ih _ _ _).negative⟩
    | always a =>
      exact ⟨always_built hp (ih _ _ _).raw, always_built hp (ih _ _ _).positive, eventually_built hp (ih _ _ _).negative⟩
    | strongUntil a b =>
      exact ⟨until_built hp (ih _ _ _).raw (ih _ _ _).raw,
        until_built hp (ih _ _ _).positive (ih _ _ _).positive,
        weakUntil_built hp (ih _ _ _).negative (.binary .conj (ih _ _ _).negative (ih _ _ _).negative)⟩
    | weakUntil a b =>
      exact ⟨weakUntil_built hp (ih _ _ _).raw (ih _ _ _).raw,
        weakUntil_built hp (ih _ _ _).positive (ih _ _ _).positive,
        until_built hp (ih _ _ _).negative (.binary .conj (ih _ _ _).negative (ih _ _ _).negative)⟩
    | initially a =>
      exact ⟨initially_built hl (ih _ _ _).raw, initially_built hl (ih _ _ _).positive, initially_built hl (ih _ _ _).negative⟩
    | «finally» a =>
      exact ⟨atEnd_built hl (ih _ _ _).raw, atEnd_built hl (ih _ _ _).positive, atEnd_built hl (ih _ _ _).negative⟩
    | letSet d a =>
      exact freeze_built _ _ _ (fun _ => ih _ _ _)
    | quant q d a =>
      cases q with
      | all =>
        exact ⟨.all _ (ih _ _ _).raw, .all _ (ih _ _ _).positive, .exists_ _ (ih _ _ _).negative⟩
      | some =>
        exact ⟨.exists_ _ (ih _ _ _).raw, .exists_ _ (ih _ _ _).positive, .all _ (ih _ _ _).negative⟩
      | no =>
        exact ⟨.all _ (.unary .neg (ih _ _ _).raw), .all _ (ih _ _ _).negative, .exists_ _ (ih _ _ _).positive⟩
      | one =>
        exact atomic_built (.exists_ _ (.binary .conj (ih _ _ _).raw (.all _ (.binary .implies (ih _ _ _).raw (.equal _ _)))))
      | lone =>
        exact atomic_built (.all _ (.binary .implies (ih _ _ _).raw (.all _ (.binary .implies (ih _ _ _).raw (.equal _ _)))))

end Encoding
end ClaferCompiler.Correctness.Behavioral
