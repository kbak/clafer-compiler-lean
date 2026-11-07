module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureSteps
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsSets

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Concrete primitive observations for expression induction. Structural
validity is independently derived by `target_structural_sound`; only table,
scalar range and source structural laws enter this bridge. -/
theorem primitiveRows (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16)
    (fits : ∀ t (x : Fin o), Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    Sets.PrimitiveRows v (schema v) w
      (Clafer.Behavioral.Structural.observed
        (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
      target.unfold rep.atoms (observedDomain w) := by
  refine {
    injective := rep.atoms.injective
    root := rep.root_completed p w
    root_inside := trivial
    live := rep.observedLive_completed p w positive small
    pool := fun d e t => rep.pool_completed p primitive shape ordinary w positive small e t d
    head := fun d ordinary e t => rep.head_completed p primitive w e t d ordinary
    head_inside := fun d ordinary t => head_inside p primitive w t d ordinary
    step_term := step_term v
    step := ?_
    step_inside := ?_ }
  · intro st finite e t
    cases st with
    | parent => exact rep.parent_completed p w positive small e t (valid.root_live t)
    | child d =>
      apply Mixed.binary_congr (rep.contains_completed p primitive w e t d finite)
      intro x y
      exact ⟨fun h => ⟨(contains_inside p primitive w t d finite h).1, h⟩, And.right⟩
    | deref d =>
      apply Mixed.binary_congr (rep.deref_completed p primitive w positive small e t (fits t) (facts t) d)
      intro x y
      change _ ↔ x ∈ observedDomain w ∧ x ∈ (completeTrace v p source).live t ∧
        y ∈ (completeTrace v p source).live t ∧ _
      constructor
      · intro h
        exact ⟨(deref_inside p w t d (fits t) h).1, h.choose_spec.2.1.1, valid.target_live h, h⟩
      · exact fun h => h.2.2.2
  · intro st finite t x y inside link
    cases st with
    | parent =>
      cases y with
      | inl y => trivial
      | inr z =>
        have hp := link.1
        cases x with
        | inl x =>
          change source.objects.identities.parent[x].map Sum.inl = some (Sum.inr z) at hp
          simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at hp
        | inr u =>
          change some (Sum.inl source.objects.identities.root) = some (Sum.inr z) at hp
          simp only [Option.some.injEq, reduceCtorEq] at hp
    | child d => exact (contains_inside p primitive w t d finite link).2
    | deref d => exact (deref_inside p w t d (fits t) link.2.2).2

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
