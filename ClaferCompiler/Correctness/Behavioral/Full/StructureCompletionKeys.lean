module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem setKey_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
    (d c owner targetDecl : Fin k)
    (lookup : v.analysis.referenceOwners[d] = some owner)
    (kind : (v.core.structural.get owner).reference = .set targetDecl) :
    (setKey v d c).Holds (schema v) w target.unfold [] t := by
  have ownerProof := SemanticsBridge.BehavioralStructural.owner_sound v.checked.2.1
    v.checked.1.2.2.2.2.1 lookup
  have ordinaryD := owner_ordinary v p primitive d owner lookup
  have typed := object_typing_of_valid p primitive shape ordinary t (valid.states t)
  have bodyBuilt : (Formula.binary .implies
      (.equal (.join (.var 1) (deref v d)) (.join (.var 0) (deref v d)))
      (.equal (.var 1) (.var 0))).Built := by repeat constructor
  unfold setKey
  rw [Mixed.all_unary_complete (.all _ (.all _ bodyBuilt))
    (rep.bounded_head_completed p primitive shape ordinary w positive small [] t c)]
  intro parent _
  have children := Mixed.unary_image rep.atoms.injective (.var 0) (contains_term v d)
    (Mixed.unary_singleton (f := rep.atoms) parent)
    (rep.contains_completed p primitive w [rep.atoms parent] t d ordinaryD)
  rw [Mixed.all_unary_complete (.all _ bodyBuilt) children]
  rintro x ⟨a, ha, containsX⟩
  have ha : a = parent := ha
  subst a
  have siblings := Mixed.unary_image rep.atoms.injective (.var 1) (contains_term v d)
    (show Mixed.Unary rep.atoms {parent}
      ((Rel.var 1).eval (schema v) w target.unfold [rep.atoms x, rep.atoms parent] t) from
        Mixed.unary_singleton parent)
    (rep.contains_completed p primitive w [rep.atoms x, rep.atoms parent] t d ordinaryD)
  rw [Mixed.all_unary_complete bodyBuilt siblings]
  rintro z ⟨a, ha, containsZ⟩
  have ha : a = parent := ha
  subst a
  rw [Encoding.holds_implies (.equal _ _) (.equal _ _)]
  intro same
  let env := [rep.atoms z, rep.atoms x, rep.atoms parent]
  have left := Mixed.unary_image rep.atoms.injective (.var 1) (deref_term v d)
    (show Mixed.Unary rep.atoms {x} ((Rel.var 1).eval (schema v) w target.unfold env t) from
      Mixed.unary_singleton x)
    (rep.deref_completed_of_object_typing p primitive w positive small env t fits typed d)
  have right := Mixed.unary_image rep.atoms.injective (.var 0) (deref_term v d)
    (show Mixed.Unary rep.atoms {z} ((Rel.var 0).eval (schema v) w target.unfold env t) from
      Mixed.unary_singleton z)
    (rep.deref_completed_of_object_typing p primitive w positive small env t fits typed d)
  have eq := (Mixed.unary_equal rep.atoms.injective left right).mp same
  obtain ⟨y, refX, _⟩ := valid.inherited_reference ownerProof ⟨containsX.1.2.1, containsX.2.1⟩
  have refZ : Clafer.Behavioral.InheritedReference.deref
      (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d z y := by
    have member : y ∈ {q | ∃ a ∈ ({x} : Set (Completion o)),
        Clafer.Behavioral.InheritedReference.deref
          (SemanticsBridge.BehavioralStructural.interpret v.core).family
          ((completeTrace v p source).raw
            (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d a q} :=
      ⟨x, rfl, refX⟩
    rw [eq] at member
    simpa only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left] using member
  have sourceKind : ((SemanticsBridge.BehavioralStructural.interpret v.core).family.reference owner).kind = .referenceSet := by
    simp only [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret,
      kind, SemanticsBridge.Structural.reference, Clafer.MCS.ReferenceTo.kind]
  have sameObject := (valid.states t).keys d owner ownerProof sourceKind parent y x z containsX refX containsZ refZ
  apply (Mixed.unary_equal rep.atoms.injective
    (show Mixed.Unary rep.atoms {x} ((Rel.var 1).eval (schema v) w target.unfold env t) from Mixed.unary_singleton x)
    (show Mixed.Unary rep.atoms {z} ((Rel.var 0).eval (schema v) w target.unfold env t) from Mixed.unary_singleton z)).mpr
  exact congrArg Set.singleton sameObject

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
