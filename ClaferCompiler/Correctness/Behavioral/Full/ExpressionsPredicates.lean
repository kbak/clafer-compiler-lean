module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaMap

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Encoding

namespace FormulaObservation
variable {A D : Nat → Type} {C U : Type} {s : Schema} {w : Nat} {τ : Trace}
  {e : Environment} {t : Nat} {σ : Clafer.Behavioral.Trace C U}
  {O : Clafer.Behavioral.PartialObservation A D U} {ρ : Clafer.Behavioral.Environment U n}
  {a : A n} {defined value : Formula}

theorem atom (hd : defined.Built) (hv : value.Built)
    (domain : defined.Holds s w τ e t ↔ (O.atom a ρ t).isSome = true)
    (truth : ∀ P, O.atom a ρ t = some P → (value.Holds s w τ e t ↔ P)) :
    FormulaObservation s w τ e t σ O ρ (.atom a)
      (Backend.Alloy.Behavioral.Partial.atom defined value) := by
  have meaning (h : (Clafer.Behavioral.Formula.atom a).Defined σ O ρ t) :
      value.Holds s w τ e t ↔ O.canonical.atom a ρ t := by
    obtain ⟨P, hp⟩ := h
    simpa [Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete, hp]
      using truth P hp
  refine ⟨Partial.atom_built hd hv, ?_, meaning, meaning, ?_⟩
  · exact domain.trans Option.isSome_iff_exists
  · intro h
    exact (holds_neg hv).trans (not_congr (meaning h))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem predicate (leaf : A n) (a : Backend.Alloy.Behavioral.Full.Value α) (p : α → Formula)
    (ha : Value.Built a) (hp : ∀ x, (p x).Built)
    (sound : ∀ x, Value.Meaning s w τ e t a x →
      ∃ P, O.atom leaf ρ t = some P ∧ ((p x).Holds s w τ e t ↔ P))
    (complete : ∀ P, O.atom leaf ρ t = some P → ∃ x, Value.Meaning s w τ e t a x) :
    FormulaObservation s w τ e t σ O ρ (.atom leaf) (a.predicate p) := by
  apply FormulaObservation.atom (Value.use_built a _ ha (fun _ => .truth)) (Value.use_built a p ha hp)
  · change a.defined.Holds s w τ e t ↔ _
    rw [Value.defined_meaning a ha, Option.isSome_iff_exists]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨P, hP, _⟩ := sound x hx
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      exact complete P hP
  · intro P hP
    rw [Value.use_meaning a p ha hp]
    constructor
    · rintro ⟨x, hx, hpx⟩
      obtain ⟨Q, hQ, he⟩ := sound x hx
      have same : Q = P := Option.some.inj (hQ.symm.trans hP)
      subst Q
      exact he.mp hpx
    · intro htruth
      obtain ⟨x, hx⟩ := complete P hP
      obtain ⟨Q, hQ, he⟩ := sound x hx
      have same : Q = P := Option.some.inj (hQ.symm.trans hP)
      subst Q
      exact ⟨x, hx, he.mpr htruth⟩

end FormulaObservation
end ClaferCompiler.Correctness.Behavioral.Full
