module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureSteps
public import ClaferCompiler.Correctness.Behavioral.CompletionFacts

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Encoding

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Source identity laws discharge the emitted global facts. Primitive
occurrences are supplied by the separate integer carrier, not the finite pool. -/
theorem identityFacts_complete (rep : TraceRep v source target) (w : Nat)
    (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (valid : Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (SemanticsBridge.Behavioral.trace source.objects)) :
    ∀ fact ∈ identityFacts v, fact.Holds (schema v) w target.unfold [] 0 := by
  intro fact hf
  simp only [identityFacts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl) | hf
  · exact Relations.unary_one_of_singleton (rep.root_meaning w [] 0)
  · apply (Relations.unary_equal rep.label_injective
      (Relations.unary_image rep.label_injective (root_term v) (.field 0)
        (rep.root_meaning w [] 0) (rep.parent_meaning w [] 0)) Relations.unary_empty).mpr
    ext x
    have hroot : source.objects.identities.parent[source.objects.identities.root] = none := valid.root_parent
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      Set.mem_singleton_iff, exists_eq_left]
    change ¬ source.objects.identities.parent[source.objects.identities.root] = some x
    rw [hroot]
    simp
  · rw [all_unary (.mult _ _) (Relations.unary_diff rep.label_injective (.sig 0) (root_term v)
      (rep.objects_meaning w [] 0) (rep.root_meaning w [] 0))]
    intro x hx
    obtain ⟨p, hparent⟩ := valid.parent_exists x hx.2
    have hi := Relations.unary_image rep.label_injective (.var 0) (.field 0)
      (Relations.unary_singleton (f := rep.label) x)
      (rep.parent_meaning w [.object (rep.label x)] 0)
    have he : {y | ∃ z ∈ ({x} : Set (Fin o)), source.objects.identities.parent[z] = some y} = {p} := by
      ext y
      change (∃ z, z = x ∧ source.objects.identities.parent[z] = some y) ↔ y = p
      simp [show source.objects.identities.parent[x] = some p from hparent, eq_comm]
    rw [he] at hi
    exact Relations.unary_one_of_singleton hi
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hf
    by_cases ha : (v.core.authoredAbstract[d] || integerDeclaration v d) = true
    · simp only [ha, ↓reduceIte, List.mem_singleton] at hd
      subst fact
      apply (Relations.unary_equal rep.label_injective (rep.direct_meaning w [] 0 d)
        Relations.unary_empty).mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hc : v.core.authoredAbstract[source.objects.identities.directType[x]] = false := valid.concrete x
      change source.objects.identities.directType[x] = d at hx
      have ho := ordinary x
      subst d
      simp only [hc, ho, Bool.or_self, Bool.false_eq_true] at ha
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hd
      cases hp : (v.core.structural.get d).parent with
      | none => simp [hp] at hd
      | some p =>
        simp only [hp, List.mem_singleton] at hd
        subst fact
        have po : integerDeclaration v p = false := by
          apply Bool.eq_false_iff.mpr
          intro hi
          have origin : (v.core.structural.get p).origin = .integer := by
            simpa [integerDeclaration] using hi
          exact (shape p origin).2.2.2.2.2 d hp
        rw [all_unary (.subset _ _) (rep.direct_meaning w [] 0 d)]
        intro x hx
        apply (Relations.unary_subset rep.label_injective
          (Relations.unary_image rep.label_injective (.var 0) (.field 0)
            (Relations.unary_singleton (f := rep.label) x)
            (rep.parent_meaning w [.object (rep.label x)] 0))
          (rep.pool_meaning w [.object (rep.label x)] 0 p po)).mpr
        rintro y ⟨z, hz, hparent⟩
        have hz' : z = x := hz
        subst z
        obtain ⟨c, hc, htype⟩ := valid.parent_typed x y hparent
        have hc' : (v.core.structural.get d).parent = some c := by
          change (v.core.structural.get source.objects.identities.directType[x]).parent = some c at hc
          change source.objects.identities.directType[x] = d at hx
          simpa only [hx] using hc
        have he : c = p := Option.some.inj (hc'.symm.trans hp)
        subst c
        exact (ancestor_iff v _ _).mpr htype

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
