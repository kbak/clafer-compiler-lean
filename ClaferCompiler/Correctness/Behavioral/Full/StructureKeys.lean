module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureReferences
public import ClaferCompiler.Correctness.Behavioral.ExpressionsMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Generated inherited set keys distinguish head occurrences sharing a parent
and referent. Bags remain separate occurrences even at equal scalar values. -/
theorem keys (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    Clafer.Behavioral.Structural.Keys
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t := by
  intro d owner ownerProof kind parent y x z containsX refX containsZ refZ
  have lookup := SemanticsBridge.BehavioralStructural.owner_complete v.checked.2.1 ownerProof
  have ordinaryD := owner_ordinary v p primitive d owner lookup
  obtain ⟨referenceTarget, refKind⟩ : ∃ c, (v.core.structural.get owner).reference = .set c := by
    cases hr : (v.core.structural.get owner).reference with
    | basic => simp [SemanticsBridge.BehavioralStructural.interpret,
        SemanticsBridge.Structural.interpret, SemanticsBridge.Structural.reference,
        hr, Clafer.MCS.ReferenceTo.kind] at kind
    | set c => exact ⟨c, rfl⟩
    | bag c => simp [SemanticsBridge.BehavioralStructural.interpret,
        SemanticsBridge.Structural.interpret, SemanticsBridge.Structural.reference,
        hr, Clafer.MCS.ReferenceTo.kind] at kind
  have ids := completeIdentities_valid v p primitive shape source (rep.identities_valid w shape identity)
  obtain ⟨_, c, parentDecl, parentHead⟩ := raw_containment_typed
    (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)
    (SemanticsBridge.BehavioralStructural.validated_wellFormed v) ids t d parent x containsX
  have parentDecl : (v.core.structural.get d).parent = some c := parentDecl
  have ordinaryC : integerDeclaration v c = false := by
    apply Bool.eq_false_iff.mpr
    intro integer
    have cp := (integerDeclaration_eq v p primitive c).mp integer
    exact (shape p primitive).2.2.2.2.2 d (cp ▸ parentDecl)
  have generated := facts (setKey v d c)
    (declaration_mem v d _ (by simp [declarationFacts, parentDecl, lookup, refKind]))
  have bodyBuilt : (Formula.binary .implies
      (.equal (.join (.var 1) (deref v d)) (.join (.var 0) (deref v d)))
      (.equal (.var 1) (.var 0))).Built := by repeat constructor
  have generated := (Encoding.holds_all (.all _ (.all _ bodyBuilt))).mp generated (rep.atoms parent)
    ((rep.head_completed p primitive w [] t c ordinaryC _).mpr ⟨parent, parentHead, rfl⟩)
  have childX := Mixed.unary_image rep.atoms.injective (.var 0) (contains_term v d)
    (Mixed.unary_singleton (f := rep.atoms) parent)
    (rep.contains_completed p primitive w [rep.atoms parent] t d ordinaryD)
  have generated := (Encoding.holds_all (.all _ bodyBuilt)).mp generated (rep.atoms x)
    ((childX _).mpr ⟨x, ⟨parent, rfl, containsX⟩, rfl⟩)
  have childZ := Mixed.unary_image rep.atoms.injective (.var 1) (contains_term v d)
    (show Mixed.Unary rep.atoms {parent}
      ((Rel.var 1).eval (schema v) w target.unfold [rep.atoms x, rep.atoms parent] t) from
        Mixed.unary_singleton parent)
    (rep.contains_completed p primitive w [rep.atoms x, rep.atoms parent] t d ordinaryD)
  have generated := (Encoding.holds_all bodyBuilt).mp generated (rep.atoms z)
    ((childZ _).mpr ⟨z, ⟨parent, rfl, containsZ⟩, rfl⟩)
  have coherent := rep.coherent p primitive w positive small t fits facts
  have sameTargets :
      {q | Clafer.Behavioral.InheritedReference.deref
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x q} =
      {q | Clafer.Behavioral.InheritedReference.deref
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d z q} := by
    ext q
    constructor
    · intro h
      have eq := coherent owner owner x q y
        ((Clafer.Behavioral.InheritedReference.deref_owner ownerProof x q).mp h).2
        ((Clafer.Behavioral.InheritedReference.deref_owner ownerProof x y).mp refX).2
      exact eq.symm ▸ refZ
    · intro h
      have eq := coherent owner owner z q y
        ((Clafer.Behavioral.InheritedReference.deref_owner ownerProof z q).mp h).2
        ((Clafer.Behavioral.InheritedReference.deref_owner ownerProof z y).mp refZ).2
      exact eq.symm ▸ refX
  let env := [rep.atoms z, rep.atoms x, rep.atoms parent]
  have left := Mixed.unary_image rep.atoms.injective (.var 1) (deref_term v d)
    (show Mixed.Unary rep.atoms {x} ((Rel.var 1).eval (schema v) w target.unfold env t) from
      Mixed.unary_singleton x)
    (rep.deref_completed p primitive w positive small env t fits facts d)
  have right := Mixed.unary_image rep.atoms.injective (.var 0) (deref_term v d)
    (show Mixed.Unary rep.atoms {z} ((Rel.var 0).eval (schema v) w target.unfold env t) from
      Mixed.unary_singleton z)
    (rep.deref_completed p primitive w positive small env t fits facts d)
  have equal : (Formula.equal (.join (.var 1) (deref v d)) (.join (.var 0) (deref v d))).Holds
      (schema v) w target.unfold env t := by
    apply (Mixed.unary_equal rep.atoms.injective left right).mpr
    simpa only [Set.mem_singleton_iff, exists_eq_left] using sameTargets
  have result := (Encoding.holds_implies (.equal _ _) (.equal _ _)).mp generated equal
  have singletonLeft : Mixed.Unary rep.atoms {x}
      ((Rel.var 1).eval (schema v) w target.unfold env t) := Mixed.unary_singleton x
  have singletonRight : Mixed.Unary rep.atoms {z}
      ((Rel.var 0).eval (schema v) w target.unfold env t) := Mixed.unary_singleton z
  exact Set.singleton_injective ((Mixed.unary_equal rep.atoms.injective singletonLeft singletonRight).mp result)

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
