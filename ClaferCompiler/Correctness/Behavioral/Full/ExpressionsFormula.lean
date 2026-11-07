module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersValues
public import ClaferCompiler.Correctness.Behavioral.Partial

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Encoding

/-- The induction interface keeps the original strict domain separate from
raw and signed truth. Truth agreement is required only inside that domain. -/
structure FormulaObservation {A D : Nat → Type} {C U : Type}
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (σ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.PartialObservation A D U)
    (ρ : Clafer.Behavioral.Environment U n) (a : Clafer.Behavioral.Formula A D n)
    (target : Backend.Alloy.Behavioral.Partial.Translation) : Prop where
  built : Partial.Built target
  defined : target.defined.Holds s w τ e t ↔ a.Defined σ O ρ t
  raw : a.Defined σ O ρ t → (target.truth.raw.Holds s w τ e t ↔ a.raw σ O.canonical ρ t)
  positive : a.Defined σ O ρ t →
    (target.truth.positive.Holds s w τ e t ↔ a.denote σ O.canonical true ρ t)
  negative : a.Defined σ O ρ t →
    (target.truth.negative.Holds s w τ e t ↔ a.denote σ O.canonical false ρ t)

namespace FormulaObservation
open Backend.Alloy.Behavioral.Partial
variable {A D : Nat → Type} {C U : Type} {s : Schema} {w : Nat} {τ : Trace}
  {e : Environment} {t : Nat} {σ : Clafer.Behavioral.Trace C U}
  {O : Clafer.Behavioral.PartialObservation A D U} {ρ : Clafer.Behavioral.Environment U n}
  {a b c : Clafer.Behavioral.Formula A D n} {x y z : Translation}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem satisfaction (h : FormulaObservation s w τ e t σ O ρ a x) (sign : Bool) :
    (Backend.Alloy.Behavioral.Partial.satisfaction x sign).Holds s w τ e t ↔
      a.Satisfies σ O sign ρ t := by
  unfold Backend.Alloy.Behavioral.Partial.satisfaction Clafer.Behavioral.Formula.Satisfies
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [holds_and h.built.defined h.built.truth.negative, h.defined]
    exact and_congr_right h.negative
  · rw [holds_and h.built.defined h.built.truth.positive, h.defined]
    exact and_congr_right h.positive

theorem truth : FormulaObservation s w τ e t σ O ρ .truth truth := by
  refine ⟨Partial.atom_built .truth .truth, Iff.rfl, fun _ => Iff.rfl,
    fun _ => Iff.rfl, fun _ => ?_⟩
  exact holds_neg (.truth)

theorem negation (ha : FormulaObservation s w τ e t σ O ρ a x) :
    FormulaObservation s w τ e t σ O ρ (.not a) (negation x) := by
  refine ⟨Partial.negation_built ha.built, ha.defined, ?_, ha.negative, ha.positive⟩
  intro h
  exact (holds_neg ha.built.truth.raw).trans (not_congr (ha.raw h))

theorem conjunction (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.and a b) (conjunction x y) := by
  refine ⟨Partial.conjunction_built ha.built hb.built,
    (Partial.conjunction_domain ha.built hb.built).trans (and_congr ha.defined hb.defined), ?_, ?_, ?_⟩
  · intro h; exact (holds_and ha.built.truth.raw hb.built.truth.raw).trans (and_congr (ha.raw h.1) (hb.raw h.2))
  · intro h; exact (holds_and ha.built.truth.positive hb.built.truth.positive).trans (and_congr (ha.positive h.1) (hb.positive h.2))
  · intro h; exact (holds_or ha.built.truth.negative hb.built.truth.negative).trans (or_congr (ha.negative h.1) (hb.negative h.2))

theorem disjunction (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.or a b) (disjunction x y) := by
  refine ⟨Partial.disjunction_built ha.built hb.built,
    (Partial.disjunction_domain ha.built hb.built).trans (and_congr ha.defined hb.defined), ?_, ?_, ?_⟩
  · intro h; exact (holds_or ha.built.truth.raw hb.built.truth.raw).trans (or_congr (ha.raw h.1) (hb.raw h.2))
  · intro h; exact (holds_or ha.built.truth.positive hb.built.truth.positive).trans (or_congr (ha.positive h.1) (hb.positive h.2))
  · intro h; exact (holds_and ha.built.truth.negative hb.built.truth.negative).trans (and_congr (ha.negative h.1) (hb.negative h.2))

theorem implication (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.implies a b) (implication x y) := by
  have h := disjunction (negation ha) hb
  refine ⟨h.built, h.defined, ?_, h.positive, h.negative⟩
  intro hd
  exact (h.raw hd).trans (by simp only [Clafer.Behavioral.Formula.raw]; tauto)

theorem equivalence (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.iff a b) (equivalence x y) := by
  have h := conjunction (implication ha hb) (implication hb ha)
  refine ⟨⟨h.built.truth, .binary .conj ha.built.defined hb.built.defined⟩,
    (holds_and ha.built.defined hb.built.defined).trans (and_congr ha.defined hb.defined), ?_, ?_, ?_⟩
  · intro hd
    exact (h.raw ⟨hd, hd.symm⟩).trans (by simp only [Clafer.Behavioral.Formula.raw]; tauto)
  · intro hd; exact h.positive ⟨hd, hd.symm⟩
  · intro hd; exact h.negative ⟨hd, hd.symm⟩

theorem exclusiveOr (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.xor a b) (exclusiveOr x y) := by
  have h := negation (equivalence ha hb)
  refine ⟨h.built, h.defined, h.raw, ?_, ?_⟩
  · intro hd
    exact (h.positive hd).trans (by simp only [Clafer.Behavioral.Formula.denote]; dsimp; tauto)
  · intro hd
    exact (h.negative hd).trans (by simp only [Clafer.Behavioral.Formula.denote]; dsimp; tauto)

theorem conditional (hc : FormulaObservation s w τ e t σ O ρ c z)
    (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hb : FormulaObservation s w τ e t σ O ρ b y) :
    FormulaObservation s w τ e t σ O ρ (.ite c a b) (conditional z x y) := by
  have h := conjunction (implication hc ha) (implication (negation hc) hb)
  refine ⟨Partial.conditional_built hc.built ha.built hb.built,
    (Partial.conditional_domain hc.built ha.built hb.built).trans
      (and_congr hc.defined (and_congr ha.defined hb.defined)), ?_, ?_, ?_⟩
  · intro hd; exact h.raw ⟨⟨hd.1, hd.2.1⟩, ⟨hd.1, hd.2.2⟩⟩
  · intro hd; exact h.positive ⟨⟨hd.1, hd.2.1⟩, ⟨hd.1, hd.2.2⟩⟩
  · intro hd; exact h.negative ⟨⟨hd.1, hd.2.1⟩, ⟨hd.1, hd.2.2⟩⟩

end FormulaObservation
end ClaferCompiler.Correctness.Behavioral.Full
