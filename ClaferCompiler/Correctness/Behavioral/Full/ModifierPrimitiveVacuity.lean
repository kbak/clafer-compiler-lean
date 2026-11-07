module

public import ClaferCompiler.Correctness.Behavioral.Full.ModifierExpansions
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open IR.Behavioral
open Backend.Alloy.Behavioral.Full

namespace ModifierPrimitive

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem stability_constant (m : Clafer.Semantics.EffectiveCore k)
    (σ : Clafer.Behavioral.Trace (Fin k) U)
    (view : Clafer.Behavioral.Modifiers.View (Fin k)) (owner : U) (S : Set U)
    (constant : ∀ t, (view.expression : Clafer.Behavioral.SetExpr (Fin k) 0).eval m σ (.closed owner) t = S)
    (t : Nat) :
    (Clafer.Behavioral.Modifiers.stabilityExpansion view).denote σ (.sets m σ) true (.closed owner) t := by
  have captured := Clafer.Behavioral.Modifiers.View.expression_capture (.closed owner) S m σ view (t + 1)
  simp only [Clafer.Behavioral.Modifiers.stabilityExpansion, Clafer.Behavioral.Formula.denote,
    Clafer.Behavioral.polarity, ↓reduceIte, Clafer.Behavioral.Observation.sets,
    Clafer.Behavioral.SetAtom.eval, constant]
  intro _
  apply Or.inr
  change S = (view.expression : Clafer.Behavioral.SetExpr (Fin k) 1).eval m σ
    ((Clafer.Behavioral.Environment.closed owner).push S) (t + 1)
  rw [captured, constant]

variable (v : IR.BehavioralStructural.Validated k) (p : Fin k) (source : ObservedLasso k o steps)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem contains_integer_parent (t : Nat) (d : Fin k) (z : Int) (y : Completion o) :
    ¬ ((completeTrace v p source).raw (Sets.model v) t).contains d (Sum.inr z) y := by
  intro h
  have parent := h.1.2.2
  cases y with
  | inl y =>
    change source.objects.identities.parent[y].map Sum.inl = some (Sum.inr z) at parent
    simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at parent
  | inr q =>
    change some (Sum.inl source.objects.identities.root) = some (Sum.inr z) at parent
    cases parent

theorem child_empty (t : Nat) (d : Fin k) (z : Int) :
    (Clafer.Behavioral.SetExpr.thisStep (.child d) : Clafer.Behavioral.SetExpr (Fin k) 0).eval
      (Sets.model v) (Clafer.Behavioral.Structural.observed
        (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
      (.closed (Sum.inr z)) t = ∅ := by
  ext y
  change (∃ x ∈ ({Sum.inr z} : Set (Completion o)),
    ((completeTrace v p source).raw (Sets.model v) t).contains d x y) ↔ False
  simp only [Set.mem_singleton_iff, exists_eq_left]
  exact iff_false_intro (contains_integer_parent v p source t d z y)

theorem deref_empty (t : Nat) (d : Fin k) (z : Int) :
    (Clafer.Behavioral.SetExpr.thisStep (.deref d) : Clafer.Behavioral.SetExpr (Fin k) 0).eval
      (Sets.model v) (Clafer.Behavioral.Structural.observed
        (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
      (.closed (Sum.inr z)) t = ∅ := by
  ext y
  change (∃ x ∈ ({Sum.inr z} : Set (Completion o)), _ ∧ _ ∧
    Clafer.Behavioral.InheritedReference.deref _ _ d x y) ↔ False
  simp only [Set.mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨_, _, owner, _, _, link⟩
    exact completeDeref_integer_source v p source t owner z y link
  · exact False.elim

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem view_empty (view : Clafer.Behavioral.Modifiers.View (Fin k)) (z : Int) (t : Nat) :
    (view.expression : Clafer.Behavioral.SetExpr (Fin k) 0).eval
      (Sets.model v) (Clafer.Behavioral.Structural.observed
        (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
      (.closed (Sum.inr z)) t = ∅ := by
  cases view with
  | heads d => exact child_empty v p source t d z
  | reference d => exact deref_empty v p source t d z
  | targets d =>
    change (Clafer.Behavioral.Step.deref d).image _ _ t
      ((Clafer.Behavioral.SetExpr.thisStep (.child d) : Clafer.Behavioral.SetExpr (Fin k) 0).eval _ _ _ _) = ∅
    rw [child_empty]
    ext y
    simp [Clafer.Behavioral.Step.image]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- All three modifier stability views are empty at primitive integer owners.
The completion therefore adds no modifier obligation at those owners. -/
theorem stable_integer (d : Fin k) (view : Surface.Modifiers.View k) (z : Int) (t : Nat) :
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) completeIntegers
      (modifierStable (modifierView d view) (modifierView d view))).Satisfies
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation true
      (.closed (Sum.inr z)) t := by
  apply (ModifierExpansions.stable_agrees _ _ _ d view _ t).mpr
  rw [SemanticsBridge.Behavioral.Surface.Modifiers.stability_interpret]
  apply stability_constant _ _ _ (Sum.inr z) ∅
  intro time
  exact view_empty v p source _ z time

end ModifierPrimitive
end ClaferCompiler.Correctness.Behavioral.Full
