module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormula
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
attribute [local instance] Classical.propDecidable

namespace Value
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

theorem conditional_meaning (a b : Backend.Alloy.Behavioral.Full.Value β)
    (ha : Built a) (hb : Built b) (hc : Partial.Built c) :
    Meaning s w τ e t (Backend.Alloy.Behavioral.Full.Value.conditional c a b) z ↔
      ∃ x y, Meaning s w τ e t a x ∧ Meaning s w τ e t b y ∧
        c.defined.Holds s w τ e t ∧
        ((c.truth.raw.Holds s w τ e t ∧ z = x) ∨ (¬ c.truth.raw.Holds s w τ e t ∧ z = y)) := by
  change Meaning s w τ e t ((a.pair b).bind (fun p => conditionalChoices c p.1 p.2)) z ↔ _
  rw [bind_meaning _ _ (pair_built a b ha hb)
    (fun p => conditionalChoices_built hc.defined hc.truth.raw p.1 p.2)]
  simp only [Prod.exists, pair_meaning a b ha hb, conditionalChoices_meaning hc.defined hc.truth.raw]
  aesop

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem conditional_observation {α β : Type} (rel : α → β → Prop)
    (left right : Option α) (a b : Backend.Alloy.Behavioral.Full.Value β)
    (ha : Built a) (hb : Built b) (hc : Partial.Built c) (defined raw : Prop)
    (hd : c.defined.Holds s w τ e t ↔ defined)
    (hr : defined → (c.truth.raw.Holds s w τ e t ↔ raw))
    (leftSound : ∀ x, Meaning s w τ e t a x → ∃ i, left = some i ∧ rel i x)
    (rightSound : ∀ y, Meaning s w τ e t b y → ∃ j, right = some j ∧ rel j y)
    (leftComplete : ∀ i, left = some i → ∃ x, Meaning s w τ e t a x)
    (rightComplete : ∀ j, right = some j → ∃ y, Meaning s w τ e t b y) :
    let source := IR.BehavioralArithmetic.conditional
      (if defined then some (decide raw) else none) left right
    (∀ z, Meaning s w τ e t (Backend.Alloy.Behavioral.Full.Value.conditional c a b) z →
      ∃ i, source = some i ∧ rel i z) ∧
    (∀ i, source = some i → ∃ z,
      Meaning s w τ e t (Backend.Alloy.Behavioral.Full.Value.conditional c a b) z) := by
  classical
  dsimp only
  constructor
  · intro z hz
    obtain ⟨x, y, hx, hy, hdef, hchoice⟩ := (conditional_meaning a b ha hb hc).mp hz
    obtain ⟨i, hi, hix⟩ := leftSound x hx
    obtain ⟨j, hj, hjy⟩ := rightSound y hy
    have hdefined := hd.mp hdef
    rcases hchoice with ⟨hraw, rfl⟩ | ⟨hraw, rfl⟩
    · exact ⟨i, by simp [hdefined, (hr hdefined).mp hraw, hi, hj, IR.BehavioralArithmetic.conditional], hix⟩
    · have hnot : ¬ raw := fun h => hraw ((hr hdefined).mpr h)
      exact ⟨j, by simp [hdefined, hnot, hi, hj, IR.BehavioralArithmetic.conditional], hjy⟩
  · intro i hi
    by_cases hdef : defined
    · cases hl : left with
      | none => simp [hl, IR.BehavioralArithmetic.conditional] at hi
      | some l =>
        cases hright : right with
        | none => simp [hright, IR.BehavioralArithmetic.conditional] at hi
        | some r =>
          obtain ⟨x, hx⟩ := leftComplete l hl
          obtain ⟨y, hy⟩ := rightComplete r hright
          by_cases hraw : raw
          · exact ⟨x, (conditional_meaning a b ha hb hc).mpr
              ⟨x, y, hx, hy, hd.mpr hdef, Or.inl ⟨(hr hdef).mpr hraw, rfl⟩⟩⟩
          · exact ⟨y, (conditional_meaning a b ha hb hc).mpr
              ⟨x, y, hx, hy, hd.mpr hdef, Or.inr ⟨fun h => hraw ((hr hdef).mp h), rfl⟩⟩⟩
    · simp [hdef, IR.BehavioralArithmetic.conditional] at hi

end Value

namespace CollectionObservation
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {σ : Clafer.Behavioral.Trace (Fin k) U} {ρ : Clafer.Behavioral.Environment U n}
  {c : SemanticsBridge.Behavioral.Expression.Meaning U n}
  {ct : Backend.Alloy.Behavioral.Partial.Translation}
  {f : U → Atom} {left right : Option (Set U)} {a b : Backend.Alloy.Behavioral.Full.Value Rel}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem conditional (hc : FormulaObservation s w τ e t σ
    SemanticsBridge.Behavioral.Expression.observation ρ c ct)
    (ha : CollectionObservation s w τ e t f left a)
    (hb : CollectionObservation s w τ e t f right b) :
    CollectionObservation s w τ e t f
      (IR.BehavioralArithmetic.conditional (SemanticsBridge.Behavioral.Expression.condition σ c ρ t) left right)
      (Backend.Alloy.Behavioral.Full.Value.conditional ct a b) := by
  have h := Value.conditional_observation
    (fun S r => r.Term ∧ Mixed.Unary f S (r.eval s w τ e t)) left right a b ha.built hb.built hc.built
    _ _ hc.defined hc.raw
    (fun x hx => by obtain ⟨S, hs, ht, hr⟩ := ha.sound x hx; exact ⟨S, hs, ht, hr⟩)
    (fun x hx => by obtain ⟨S, hs, ht, hr⟩ := hb.sound x hx; exact ⟨S, hs, ht, hr⟩)
    ha.complete hb.complete
  exact ⟨Value.conditional_built a b ha.built hb.built hc.built.defined hc.built.truth.raw,
    h.1, h.2⟩
end CollectionObservation

namespace IntegerObservation
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {σ : Clafer.Behavioral.Trace (Fin k) U} {ρ : Clafer.Behavioral.Environment U n}
  {c : SemanticsBridge.Behavioral.Expression.Meaning U n}
  {ct : Backend.Alloy.Behavioral.Partial.Translation}
  {left right : Option Int} {a b : Backend.Alloy.Behavioral.Full.Value Integer}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem conditional (hc : FormulaObservation s w τ e t σ
    SemanticsBridge.Behavioral.Expression.observation ρ c ct)
    (ha : IntegerObservation s w τ e t left a)
    (hb : IntegerObservation s w τ e t right b) :
    IntegerObservation s w τ e t
      (IR.BehavioralArithmetic.conditional (SemanticsBridge.Behavioral.Expression.condition σ c ρ t) left right)
      (Backend.Alloy.Behavioral.Full.Value.conditional ct a b) := by
  have h := Value.conditional_observation
    (fun z r => Arithmetic.Term r ∧ r.eval s w τ e t = some z) left right a b ha.built hb.built hc.built
    _ _ hc.defined hc.raw
    (fun x hx => by obtain ⟨z, hz, ht, he⟩ := ha.sound x hx; exact ⟨z, hz, ht, he⟩)
    (fun x hx => by obtain ⟨z, hz, ht, he⟩ := hb.sound x hx; exact ⟨z, hz, ht, he⟩)
    ha.complete hb.complete
  exact ⟨Value.conditional_built a b ha.built hb.built hc.built.defined hc.built.truth.raw,
    h.1, h.2⟩
end IntegerObservation
end ClaferCompiler.Correctness.Behavioral.Full
