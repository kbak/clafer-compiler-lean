module

public import ClaferCompiler.Backend.Alloy.Behavioral.Partial
public import ClaferCompiler.Correctness.Behavioral.ExpressionsCapture
public import Clafer.Behavioral.PartialObservation

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Partial
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Partial
open Encoding

/-- Shape is checked independently of all source and target truth. -/
structure Built (a : Translation) : Prop where
  truth : Encoding.Built a.truth
  defined : a.defined.Built

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The constant analysis proves truth for every trace, environment and time.
It does not inspect source satisfaction or a solver witness. -/
theorem knownTrue_sound (ha : a.Built) (h : knownTrue a = true) :
    ∀ (e : Environment) (t : Nat), a.Holds s w τ e t := by
  induction ha with
  | truth => intro _ _; trivial
  | falsity | equal | subset | mult | compare => cases h
  | unary op hp ih =>
    simp only [knownTrue, Formula.fold_unary _ _ _ _ hp] at h
    intro e t
    simp only [Formula.Holds, Formula.fold_unary _ _ _ _ hp]
    cases op with
    | neg | before => cases h
    | after => exact ih h e (t + 1)
    | always => exact fun j _ => ih h e j
    | eventually => exact ⟨t, le_refl _, ih h e t⟩
    | once => exact ⟨t, le_refl _, ih h e t⟩
    | historically => exact fun j _ => ih h e j
  | @binary op p q hp hq ihp ihq =>
    simp only [knownTrue, Formula.fold_binary _ _ _ _ _ hp hq] at h
    intro e t
    simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ hp hq]
    cases op with
    | conj =>
      have hh : knownTrue p = true ∧ knownTrue q = true := by simpa only [knownTrue, trueAlgebra, Bool.and_eq_true] using h
      exact ⟨ihp hh.1 e t, ihq hh.2 e t⟩
    | disj =>
      have hh : knownTrue p = true ∨ knownTrue q = true := by simpa only [knownTrue, trueAlgebra, Bool.or_eq_true] using h
      rcases hh with h | h
      · exact Or.inl (ihp h e t)
      · exact Or.inr (ihq h e t)
    | implies => exact fun _ => ihq h e t
    | «until» => exact ⟨t, le_refl _, ihq h e t, fun _ h₁ h₂ => False.elim (by omega)⟩
    | since => exact ⟨t, le_refl _, ihq h e t, fun _ h₁ h₂ => False.elim (by omega)⟩
    | releases | triggered => exact fun j _ _ => ihq h e j
  | all r hp ih =>
    simp only [knownTrue, Formula.fold_all _ _ _ hp] at h
    intro e t
    rw [holds_all hp]
    exact fun x _ => ih h (x :: e) t
  | exists_ r hp =>
    simp only [knownTrue, Formula.fold_exists _ _ _ hp] at h
    cases h

theorem totalAlways_built (hp : p.Built) (ha : a.Built) : (totalAlways p a).Built := by
  unfold totalAlways
  split
  · exact .truth
  · exact Encoding.always_built hp ha

theorem totalAlways_domain (hp : p.Built) (ha : a.Built) :
    (totalAlways p a).Holds s w τ e t ↔
      ∀ j, t ≤ j → Clafer.Behavioral.Lifetime.Through (fun i => p.Holds s w τ e i) t j →
        a.Holds s w τ e j := by
  unfold totalAlways
  split
  · rename_i h
    exact ⟨fun _ j _ _ => knownTrue_sound ha h e j, fun _ => True.intro⟩
  · exact Encoding.always_meaning s w τ e p a hp ha t

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem atom_built (hd : d.Built) (hp : p.Built) : Built (atom d p) :=
  ⟨atomic_built hp, hd⟩

theorem negation_built (ha : Built a) : Built (negation a) :=
  ⟨Encoding.negation_built ha.truth, ha.defined⟩

theorem conjunction_built (ha : Built a) (hb : Built b) : Built (conjunction a b) :=
  ⟨Encoding.conjunction_built ha.truth hb.truth, .binary .conj ha.defined hb.defined⟩

theorem disjunction_built (ha : Built a) (hb : Built b) : Built (disjunction a b) :=
  ⟨Encoding.disjunction_built ha.truth hb.truth, .binary .conj ha.defined hb.defined⟩

theorem conditional_built (hc : Built c) (ha : Built a) (hb : Built b) : Built (conditional c a b) :=
  ⟨Encoding.conjunction_built (Encoding.implication_built hc.truth ha.truth)
    (Encoding.implication_built (Encoding.negation_built hc.truth) hb.truth),
    .binary .conj hc.defined (.binary .conj ha.defined hb.defined)⟩

theorem next_built (hp : p.Built) (ha : Built a) : Built (next p a) :=
  ⟨⟨Encoding.next_built hp ha.truth.raw, Encoding.next_built hp ha.truth.positive,
      Encoding.next_built hp ha.truth.negative⟩, Encoding.next_built hp ha.defined⟩

theorem eventually_built (hp : p.Built) (ha : Built a) : Built (eventually p a) :=
  ⟨⟨Encoding.eventually_built hp ha.truth.raw, Encoding.eventually_built hp ha.truth.positive,
      Encoding.always_built hp ha.truth.negative⟩, totalAlways_built hp ha.defined⟩

theorem always_built (hp : p.Built) (ha : Built a) : Built (always p a) :=
  ⟨⟨Encoding.always_built hp ha.truth.raw, Encoding.always_built hp ha.truth.positive,
      Encoding.eventually_built hp ha.truth.negative⟩, totalAlways_built hp ha.defined⟩

theorem satisfaction_built (ha : Built a) (positive : Bool) :
    (satisfaction a positive).Built :=
  .binary .conj ha.defined (by cases positive; exact ha.truth.negative; exact ha.truth.positive)

theorem conjunction_domain (ha : Built a) (hb : Built b) :
    (conjunction a b).defined.Holds s w τ e t ↔
      a.defined.Holds s w τ e t ∧ b.defined.Holds s w τ e t :=
  holds_and ha.defined hb.defined

theorem disjunction_domain (ha : Built a) (hb : Built b) :
    (disjunction a b).defined.Holds s w τ e t ↔
      a.defined.Holds s w τ e t ∧ b.defined.Holds s w τ e t :=
  holds_and ha.defined hb.defined

theorem conditional_domain (hc : Built c) (ha : Built a) (hb : Built b) :
    (conditional c a b).defined.Holds s w τ e t ↔ c.defined.Holds s w τ e t ∧
      a.defined.Holds s w τ e t ∧ b.defined.Holds s w τ e t := by
  exact (holds_and hc.defined (.binary .conj ha.defined hb.defined)).trans
    (and_congr_right fun _ => holds_and ha.defined hb.defined)

theorem next_domain (hp : p.Built) (ha : Built a) :
    (next p a).defined.Holds s w τ e t ↔
      (p.Holds s w τ e (t + 1) → a.defined.Holds s w τ e (t + 1)) :=
  Encoding.next_meaning s w τ e p a.defined hp ha.defined t

/-- Both F and G inspect the original operand's domain through the whole
remaining parent interval, regardless of when a truth witness is found. -/
theorem eventually_domain (hp : p.Built) (ha : Built a) :
    (eventually p a).defined.Holds s w τ e t ↔
      ∀ j, t ≤ j → Clafer.Behavioral.Lifetime.Through (fun i => p.Holds s w τ e i) t j →
        a.defined.Holds s w τ e j :=
  totalAlways_domain hp ha.defined

theorem always_domain (hp : p.Built) (ha : Built a) :
    (always p a).defined.Holds s w τ e t ↔
      ∀ j, t ≤ j → Clafer.Behavioral.Lifetime.Through (fun i => p.Holds s w τ e i) t j →
        a.defined.Holds s w τ e j :=
  eventually_domain hp ha

theorem strongUntil_domain (hp : p.Built) (ha : Built a) (hb : Built b) :
    (strongUntil p a b).defined.Holds s w τ e t ↔
      ∀ j, t ≤ j → Clafer.Behavioral.Lifetime.Through (fun i => p.Holds s w τ e i) t j →
        a.defined.Holds s w τ e j ∧ b.defined.Holds s w τ e j := by
  change (totalAlways p (.binary .conj a.defined b.defined)).Holds _ _ _ _ _ ↔ _
  rw [totalAlways_domain hp (.binary .conj ha.defined hb.defined)]
  simp only [holds_and ha.defined hb.defined]

theorem weakUntil_domain (hp : p.Built) (ha : Built a) (hb : Built b) :
    (weakUntil p a b).defined.Holds s w τ e t ↔
      ∀ j, t ≤ j → Clafer.Behavioral.Lifetime.Through (fun i => p.Holds s w τ e i) t j →
        a.defined.Holds s w τ e j ∧ b.defined.Holds s w τ e j :=
  strongUntil_domain hp ha hb

theorem initially_domain (hp : p.Built) (ha : Built a) :
    (initially p a).defined.Holds s w τ e t ↔
      ((p.Holds s w τ e t ∧ (t = 0 ∨ ∃ j, t = j + 1 ∧ ¬ p.Holds s w τ e j)) →
        a.defined.Holds s w τ e t) :=
  Encoding.initially_meaning s w τ e p a.defined hp ha.defined t

theorem finally_domain (hp : p.Built) (ha : Built a) :
    («finally» p a).defined.Holds s w τ e t ↔
      ((p.Holds s w τ e t ∧ ¬ p.Holds s w τ e (t + 1)) → a.defined.Holds s w τ e t) :=
  Encoding.atEnd_meaning s w τ e p a.defined hp ha.defined t

/-- Selection is made at the capture time. The generated continuation uses the
selected syntax; frozen-alias representation discharges persistence separately. -/
def selected (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (aliases : List Rel) (domain captured : Rel) : Rel := by
  classical
  exact aliases.foldl (fun acc r => if (Formula.subset r domain).Holds s w τ e t
    then .union acc r else acc) captured

theorem freeze_selected (aliases : List Rel) (domain captured : Rel)
    (body : Rel → Backend.Alloy.Behavioral.Translation)
    (hb : ∀ r, Encoding.Built (body r)) (part : Option Bool) :
    (Encoding.part (Backend.Alloy.Behavioral.freezeFrom aliases domain body captured) part).Holds s w τ e t ↔
      (Encoding.part (body (selected s w τ e t aliases domain captured)) part).Holds s w τ e t := by
  classical
  induction aliases generalizing captured with
  | nil => rfl
  | cons r rs ih =>
    change (Encoding.part (Backend.Alloy.Behavioral.freezeChoice (.subset r domain)
      (Backend.Alloy.Behavioral.freezeFrom rs domain body (.union captured r))
      (Backend.Alloy.Behavioral.freezeFrom rs domain body captured)) part).Holds _ _ _ _ _ ↔ _
    rw [Encoding.freezeChoice_meaning (.subset _ _) (Encoding.freezeFrom_built _ _ _ _ hb)
      (Encoding.freezeFrom_built _ _ _ _ hb) part, ih, ih]
    by_cases h : (Formula.subset r domain).Holds s w τ e t <;>
      simp [selected, List.foldl_cons, h]

theorem capture_domain (aliases : List Rel) (domain : Rel) (domainDefined : Formula)
    (hd : domainDefined.Built) (body : Rel → Translation) (hb : ∀ r, Built (body r)) :
    (capture aliases domain domainDefined body).defined.Holds s w τ e t ↔
      domainDefined.Holds s w τ e t ∧
        (body (selected s w τ e t aliases domain (.empty .unary))).defined.Holds s w τ e t := by
  unfold capture
  rw [holds_and hd (Encoding.freeze_built _ _ _ (fun r => Encoding.atomic_built (hb r).defined)).raw]
  apply and_congr_right
  intro _
  exact freeze_selected aliases domain (.empty .unary)
    (fun r => .atomic (body r).defined) (fun r => Encoding.atomic_built (hb r).defined) none

theorem quantify_domain (q : IR.Behavioral.Quantifier) (domain : Rel)
    (domainDefined : Formula) (hd : domainDefined.Built) (one two : Translation)
    (ho : Built one) :
    (quantify q domain domainDefined one two).defined.Holds s w τ e t ↔
      domainDefined.Holds s w τ e t ∧
        ∀ x, [x] ∈ domain.eval s w τ e t → one.defined.Holds s w τ (x :: e) t := by
  change (Formula.binary .conj domainDefined (.all domain one.defined)).Holds _ _ _ _ _ ↔ _
  rw [holds_and hd (.all domain ho.defined), holds_all ho.defined]

/-- Assembly uses operand domain and truth lemmas; no agreement assumption is
hidden in `Translation`. Concrete leaf preservation remains a separate premise. -/
theorem satisfies_iff (ha : Built a) (positive : Bool)
    {A D : Nat → Type} {C U : Type} (σ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.PartialObservation A D U)
    (f : Clafer.Behavioral.Formula A D n) (ρ : Clafer.Behavioral.Environment U n)
    (hd : a.defined.Holds s w τ e t ↔ f.Defined σ O ρ t)
    (ht : (if positive then a.truth.positive else a.truth.negative).Holds s w τ e t ↔
      f.denote σ O.canonical positive ρ t) :
    (satisfaction a positive).Holds s w τ e t ↔ f.Satisfies σ O positive ρ t := by
  unfold satisfaction Clafer.Behavioral.Formula.Satisfies
  rw [holds_and ha.defined (by cases positive; exact ha.truth.negative; exact ha.truth.positive)]
  exact and_congr hd ht

/-- Failure is classical negation of the complete property, even if that
property fails because its original domain is undefined. -/
theorem counterexample_iff (hp : p.Built) :
    (counterexample p).Holds s w τ e t ↔ ¬ p.Holds s w τ e t := holds_neg hp

theorem undefined_is_counterexample (ha : Built a) (hd : ¬ a.defined.Holds s w τ e t) :
    (counterexample (satisfaction a true)).Holds s w τ e t ∧
    ¬ (satisfaction a false).Holds s w τ e t := by
  rw [counterexample_iff (satisfaction_built ha true)]
  simp only [satisfaction, Bool.false_eq_true, ↓reduceIte,
    holds_and ha.defined ha.truth.positive, holds_and ha.defined ha.truth.negative]
  exact ⟨fun h => hd h.1, fun h => hd h.1⟩

end ClaferCompiler.Correctness.Behavioral.Partial
