module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationDeclarations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

/-- Structural realization bounds and finite-table conditions only. No source
validity, emitted-fact truth, or decoder success is assumed by this predicate. -/
structure StructuralFits (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (source : ObservedLasso k o steps) (width capacity : Nat) : Prop where
  widthPositive : 0 < width
  widthSmall : width ≤ 16
  capacity : o ≤ capacity
  unique : ∀ x y : Fin o, source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y
  references : ∀ t, (source.objects.at t).references.Nodup
  ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false
  scalars : ∀ t (x : Fin o), Backend.Alloy.fitsInt width (source.valuesAt t)[x] = true
  counts : StructuralCountFits v p source width

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completeIdentities_restrict (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (source : ObservedLasso k o steps)
    (valid : Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (SemanticsBridge.Behavioral.trace source.objects) := by
  refine ⟨valid.root_type, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Sum.inl.inj (valid.root_only (Sum.inl x) hx)
  · intro x
    exact valid.concrete (Sum.inl x)
  · exact Option.map_eq_none_iff.mp valid.root_parent
  · intro x ne
    obtain ⟨y, parent⟩ := valid.parent_exists (Sum.inl x) (fun eq => ne (Sum.inl.inj eq))
    change source.objects.identities.parent[x].map Sum.inl = some y at parent
    obtain ⟨a, ha, _⟩ := Option.map_eq_some_iff.mp parent
    exact ⟨a, ha⟩
  · intro x y parent
    exact valid.parent_typed (Sum.inl x) (Sum.inl y) ((complete_parent_object v p source x y).mpr parent)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The concrete encoder realizes every structurally valid finite observation
satisfying the explicit data/range budgets. All rich structure facts and target
declarations are conclusions. Scope and expression obligations are separate. -/
theorem encode_structural_complete (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (source : ObservedLasso k o steps) (width capacity : Nat)
    (fits : StructuralFits v p source width capacity)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    (encode source).unfold.Declarations (schema v) ∧
    (∀ t, ((encode source).unfold.state t).scalarFields width (schema v).declarations = true) ∧
    (∀ f ∈ identityFacts v, f.Holds (schema v) width (encode source).unfold [] 0) ∧
    (∀ t f, f ∈ stateFacts v → f.Holds (schema v) width (encode source).unfold [] t) ∧
    (∀ t, (reachabilityFact v capacity).Holds (schema v) width (encode source).unfold [] t) := by
  have ids := completeIdentities_restrict v p source valid.identities
  let rep := encode_rep v source fits.unique ids.root_type ids.root_only
  exact ⟨encode_declarations v source fits.unique fits.references,
    fun t => encode_scalarFields v source fits.unique width t (fits.scalars t),
    rep.identityFacts_complete width shape fits.ordinary ids,
    rep.stateFacts_complete p primitive shape fits.ordinary width fits.widthPositive fits.widthSmall fits.scalars fits.counts valid,
    fun t => rep.reachabilityFact_complete p width t capacity fits.capacity valid⟩

end ClaferCompiler.Correctness.Behavioral.Full
