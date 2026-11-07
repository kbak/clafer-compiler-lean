module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPreservation
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile
public import ClaferCompiler.SemanticsBridge.Behavioral.Modifiers

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open IR.Behavioral
open Backend.Alloy.Behavioral.Full

namespace ModifierExpansions
variable (m : Clafer.Semantics.EffectiveCore k) (σ : Clafer.Behavioral.Trace (Fin k) U)
  (R : Clafer.Constraints.IntegerRealization U)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem initial_agrees (d : Fin k) (ρ : Clafer.Behavioral.Environment U 0) (t : Nat) :
    (SemanticsBridge.Behavioral.Expression.formula m σ R (modifierInitial d)).Satisfies
      σ SemanticsBridge.Behavioral.Expression.observation true ρ t ↔
    (SemanticsBridge.Behavioral.formula (Surface.Modifiers.initialExpansion d)).denote
      σ (.sets m σ) true ρ t := by
  simp only [modifierInitial, Surface.Modifiers.initialExpansion,
    SemanticsBridge.Behavioral.Expression.formula, SemanticsBridge.Behavioral.formula,
    Clafer.Behavioral.Formula.Satisfies, Clafer.Behavioral.Formula.Defined,
    Clafer.Behavioral.Formula.denote, SemanticsBridge.Behavioral.Expression.observation,
    Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete,
    SemanticsBridge.Behavioral.atom, Clafer.Behavioral.Observation.sets,
    Clafer.Behavioral.SetAtom.eval, Clafer.Behavioral.polarity,
    Option.map_some, Option.getD_some, ↓reduceIte]
  constructor
  · exact And.right
  · intro holds
    exact ⟨fun _ => ⟨_, rfl⟩, holds⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem stable_agrees (d : Fin k) (view : Surface.Modifiers.View k)
    (ρ : Clafer.Behavioral.Environment U 0) (t : Nat) :
    (SemanticsBridge.Behavioral.Expression.formula m σ R
      (modifierStable (modifierView d view) (modifierView d view))).Satisfies
      σ SemanticsBridge.Behavioral.Expression.observation true ρ t ↔
    (SemanticsBridge.Behavioral.formula (Surface.Modifiers.stabilityExpansion
      (match view with | .heads _ => .heads d | .reference _ => .reference d | .targets _ => .targets d))).denote
      σ (.sets m σ) true ρ t := by
  cases view <;>
    simp [modifierStable, modifierView, Surface.Modifiers.stabilityExpansion,
      Surface.Modifiers.View.expression, SemanticsBridge.Behavioral.Expression.formula,
      SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.Satisfies,
      Clafer.Behavioral.Formula.Defined, Clafer.Behavioral.Formula.denote,
      SemanticsBridge.Behavioral.Expression.observation,
      Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete,
      SemanticsBridge.Behavioral.atom, Clafer.Behavioral.Observation.sets,
      Clafer.Behavioral.SetAtom.eval, Clafer.Behavioral.polarity,
      Clafer.Constraints.lift₂] <;>
    exact fun _ _ => ⟨⟨_, Iff.rfl⟩, ⟨_, Iff.rfl⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The full expression expansion retains every member of the accepted modifier
expansion. Its partial observations are total set observations in these bodies. -/
theorem expansions_agree (d : Fin k) (modifier : Surface.Modifiers.Modifier)
    (contexts : Surface.Modifiers.Placement k → Nat → Set U) :
    (∀ item ∈ modifierExpansions d modifier,
      (SemanticsBridge.Behavioral.Expression.formula m σ R item.2).PartialAttached
        σ SemanticsBridge.Behavioral.Expression.observation (contexts item.1)) ↔
    (∀ item ∈ Surface.Modifiers.expand d modifier,
      (SemanticsBridge.Behavioral.formula item.2).Attached σ (.sets m σ) (contexts item.1)) := by
  cases modifier <;>
    simp [modifierExpansions, Surface.Modifiers.expand,
      Clafer.Behavioral.Formula.PartialAttached,
      Clafer.Behavioral.Formula.Attached]
  · exact forall_congr' fun t => forall_congr' fun x => imp_congr_right fun _ =>
      imp_congr_right fun _ => initial_agrees m σ R d (.closed x) t
  · apply and_congr
    · exact forall_congr' fun t => forall_congr' fun x => imp_congr_right fun _ =>
        imp_congr_right fun _ => stable_agrees m σ R d (.heads d) (.closed x) t
    · exact forall_congr' fun t => forall_congr' fun x => imp_congr_right fun _ =>
        imp_congr_right fun _ => stable_agrees m σ R d (.reference d) (.closed x) t
  · exact forall_congr' fun t => forall_congr' fun x => imp_congr_right fun _ =>
      imp_congr_right fun _ => stable_agrees m σ R d (.reference d) (.closed x) t
  · exact forall_congr' fun t => forall_congr' fun x => imp_congr_right fun _ =>
      imp_congr_right fun _ => stable_agrees m σ R d (.targets d) (.closed x) t

end ModifierExpansions
end ClaferCompiler.Correctness.Behavioral.Full
