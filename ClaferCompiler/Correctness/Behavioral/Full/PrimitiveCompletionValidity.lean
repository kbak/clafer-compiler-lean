module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionCardinality
public import ClaferCompiler.Correctness.Behavioral.Full.StructureGroups
public import ClaferCompiler.Correctness.Behavioral.Full.StructureKeys
public import ClaferCompiler.Correctness.ExpressionScalarFacts

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Generated target facts imply the actual upstream rich structural contract
on the completed infinite integer carrier. Scalar bounds are explicit data
conditions; no source validity or formula-equivalence premise is assumed. -/
theorem complete_valid_of_values_fit (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (capacity : Nat)
    (fits : ∀ t (x : Fin o), Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (reach : ∀ t, (reachabilityFact v capacity).Holds (schema v) w target.unfold [] t) :
    Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) := by
  let m := SemanticsBridge.BehavioralStructural.interpret v.core
  let τ := completeTrace v p source
  have wf := SemanticsBridge.BehavioralStructural.validated_wellFormed v
  have finiteIds := rep.identities_valid w shape identity
  have ids := completeIdentities_valid v p primitive shape source finiteIds
  have rootLive := fun t => rep.root_live w t (states t)
  have parentLive := complete_parent_live v p source rootLive
    (fun t => rep.parent_live w t (states t))
  have ordinary : ∀ d : Fin k, d ≠ p → integerDeclaration v d = false := by
    intro d different
    exact Bool.eq_false_iff.mpr (fun hd => different ((integerDeclaration_eq v p primitive d).mp hd))
  refine ⟨ids, complete_root_live v p source rootLive, parentLive, ?_⟩
  intro t
  have objectTyped := rep.object_reference_typed w t (states t)
  refine {
    typed := ⟨raw_containment_typed m τ wf ids t,
      complete_reference_typed v p primitive source t objectTyped⟩
    root_head := complete_root_head v p primitive source t (rep.root_head w t identity (states t))
    root_separate := raw_root_separate m τ wf ids t
    inherits := raw_inherits m τ t
    abstracts := raw_abstracts m τ wf ids t
    parents := raw_parents m τ wf ids parentLive t
    references := complete_references v p primitive source t ?_
      (rep.object_references w t (states t))
    coherent := rep.coherent p primitive w positive small t (fits t) (states t)
    keys := rep.keys p primitive shape w positive small t (fits t) identity (states t)
    multiplicities := complete_multiplicities v p primitive shape source t ?_
    groups := complete_groups v p primitive shape source t finiteIds ?_
    disjoint := raw_disjoint m τ t
    reachable := complete_reachable v p primitive source t (rootLive t)
      (rep.reachable w t capacity shape identity (states t) (reach t))
  }
  · intro d x y link
    obtain ⟨c, target, ordinary, _, _⟩ := objectTyped d x y link
    exact ⟨c, target, ordinary⟩
  · intro d c parent ordinaryD ordinaryC
    exact rep.local_bounds w t (states t) d c parent (ordinary d ordinaryD) (ordinary c ordinaryC)
  · intro d concrete ordinaryD nonroot
    exact rep.group_bounds_nonroot w t shape identity (states t) d concrete (ordinary d ordinaryD) nonroot

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem values_fit (rep : TraceRep v source target) (w t : Nat)
    (fields : (target.unfold.state t).scalarFields w (schema v).declarations = true)
    (x : Fin o) : Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true := by
  have rows := ExpressionMeaning.scalar_field_rows (target.unfold.state t) w
    (schema v).declarations 0 { isAbstract := true, scalar := true } rfl rfl fields
  have member := (rep.values t (rep.label x, (source.valuesAt t)[x])).mpr ⟨x, rfl⟩
  exact (rows.1 _ member).2

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Scalar admission supplies bounded values, so structural soundness consumes
only the emitted facts and target declaration checks. -/
theorem complete_valid (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (capacity : Nat)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (reach : ∀ t, (reachabilityFact v capacity).Holds (schema v) w target.unfold [] t)
    (fields : ∀ t, (target.unfold.state t).scalarFields w (schema v).declarations = true) :
    Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) :=
  rep.complete_valid_of_values_fit p primitive shape w positive small capacity
    (fun t => rep.values_fit w t (fields t)) identity states reach

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
