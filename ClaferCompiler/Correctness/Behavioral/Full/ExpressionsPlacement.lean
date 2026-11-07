module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsAttachments

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open IR.Behavioral

/-- Object placements observed by the executable modifier attachment. The
source modifier proof separately discharges primitive-owner vacuity. -/
def placementObjects (v : IR.BehavioralStructural.Validated k) (source : ObservedLasso k o steps) :
    Surface.Modifiers.Placement k → Nat → Set (Fin o)
  | .all, t => {x | (source.objects.at t).live[x] = true}
  | .heads d, t => ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d
  | .parents d, t => {x | ∃ p, (v.core.structural.get d).parent = some p ∧ x ∈
      ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head p}

def OrdinaryPlacement (v : IR.BehavioralStructural.Validated k) : Surface.Modifiers.Placement k → Prop
  | .heads d => integerDeclaration v d = false
  | _ => True

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem placement_meaning (rep : TraceRep v source target) (shape : PrimitiveShape v)
    (where_ : Surface.Modifiers.Placement k) (ordinary : OrdinaryPlacement v where_)
    (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label (placementObjects v source where_ t)
      ((placement v where_).eval (schema v) w target.unfold e t) := by
  cases where_ with
  | all => exact rep.live_meaning w e t
  | heads d => exact rep.head_source w e t d ordinary
  | parents d =>
    cases parent : (v.core.structural.get d).parent with
    | none =>
      have empty : placementObjects v source (.parents d) t = ∅ := by
        ext x
        simp [placementObjects, parent]
      rw [empty]
      simp only [placement, parent]
      change Relations.Unary _ ∅ []
      intro row; simp
    | some p =>
      have ordinary : integerDeclaration v p = false := by
        cases primitive : integerDeclaration v p with
        | false => rfl
        | true =>
          have origin : (v.core.structural.get p).origin = .integer := by
            simpa [integerDeclaration] using primitive
          exact False.elim ((shape p origin).2.2.2.2.2 d parent)
      simpa [placementObjects, placement, parent] using rep.head_source w e t p ordinary

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem placement_attached (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (capacity : o ≤ b.objects) (shape : PrimitiveShape v)
    (pass : Expressions.PassObservation v (estimates v b) (schema v) target.unfold σ rep.labels
      (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel))
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (where_ : Surface.Modifiers.Placement k) (ordinary : OrdinaryPlacement v where_)
    (a : Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel (placement v where_) a = .ok result) :
    result.Holds (schema v) b.bitwidth target.unfold [] 0 ↔
      ∀ t x, x ∈ placementObjects v source where_ t →
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a).Satisfies
          σ SemanticsBridge.Behavioral.Expression.observation true (.closed (Sum.inl x)) t :=
  rep.attached_meaning b fuel capacity pass (placement v where_) (placementObjects v source where_)
    (fun e t => rep.placement_meaning shape where_ ordinary b.bitwidth e t)
    (rep.owner_root b.bitwidth (placement v where_) (placementObjects v source where_)
      (fun e t => rep.placement_meaning shape where_ ordinary b.bitwidth e t) facts) a result success

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
