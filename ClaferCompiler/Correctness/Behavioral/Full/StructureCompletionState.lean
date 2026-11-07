module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionGroups

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

/-- Only signed-range obligations for emitted numeric comparisons. Source
structural validity is a separate hypothesis, never part of this fit predicate. -/
structure StructuralCountFits (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (source : ObservedLasso k o steps) (width : Nat) : Prop where
  localCounts : ∀ t d c, (v.core.structural.get d).parent = some c →
    ∀ x ∈ ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c,
      Structural.IntervalFits width (v.core.structural.get d).localBounds
        {y | ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y}.ncard
  group : ∀ t d, v.core.authoredAbstract[d] = false →
    ∀ x ∈ ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d,
      Structural.IntervalFits width (v.core.structural.get d).groupBounds
        {y | Clafer.Semantics.Groups.ChildObjects
          (SemanticsBridge.BehavioralStructural.interpret v.core).family
          ((completeTrace v p source).raw
            (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y}.ncard

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem declarationFacts_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (counts : StructuralCountFits v p source w)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
    (d : Fin k) : ∀ fact ∈ declarationFacts v d, fact.Holds (schema v) w target.unfold [] t := by
  intro fact member
  simp only [declarationFacts, List.mem_append] at member
  rcases member with (reference | group) | containment
  · exact rep.referenceFacts_complete p primitive shape ordinary w positive small t fits (valid.states t) d fact reference
  · cases concrete : v.core.authoredAbstract[d] with
    | true => simp only [concrete, ↓reduceIte, List.not_mem_nil] at group
    | false =>
      simp only [concrete, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at group
      subst fact
      exact rep.groupFact_complete p primitive shape ordinary w positive small t valid d concrete (counts.group t d concrete)
  · cases parent : (v.core.structural.get d).parent with
    | none => simp only [parent, List.not_mem_nil] at containment
    | some c =>
      simp only [parent, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at containment
      obtain ⟨typed, parents, localBounds⟩ := rep.containmentFacts_complete p primitive shape ordinary w positive small t valid d c parent (counts.localCounts t d c parent)
      rcases containment with (rfl | rfl | rfl) | key
      · exact typed
      · exact parents
      · exact localBounds
      · cases lookup : v.analysis.referenceOwners[d] with
        | none => simp only [lookup, List.not_mem_nil] at key
        | some owner =>
          cases kind : (v.core.structural.get owner).reference with
          | basic => simp only [lookup, kind, List.not_mem_nil] at key
          | bag targetDecl => simp only [lookup, kind, List.not_mem_nil] at key
          | set targetDecl =>
            simp only [lookup, kind, List.mem_singleton] at key
            subst fact
            exact rep.setKey_complete p primitive shape ordinary w positive small t fits valid d c owner targetDecl lookup kind

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Source validity and explicit numeric fits prove the actual emitted rich
state facts, including inherited groups, references, keys and parent views. -/
theorem stateFacts_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16)
    (fits : ∀ t (x : Fin o), Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (counts : StructuralCountFits v p source w)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    ∀ t fact, fact ∈ stateFacts v → fact.Holds (schema v) w target.unfold [] t := by
  intro t fact member
  simp only [stateFacts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl | rfl) | coherent) | declarations
  · intro row hr
    obtain ⟨x, y, ⟨rfl, _⟩, he⟩ := (rep.membership_meaning w [] t row).mp hr
    exact (Relations.binary_product (root_term v) (.sig 0)
      (rep.root_meaning w [] t) (rep.objects_meaning w [] t) row).mpr
        ⟨source.objects.identities.root, y, ⟨rfl, Set.mem_univ _⟩, he⟩
  · have rootOrdinary := ordinary source.objects.identities.root
    rw [rep.root_type] at rootOrdinary
    apply (Mixed.unary_equal rep.atoms.injective
      (rep.head_completed p primitive w [] t v.core.structural.root rootOrdinary)
      (rep.root_completed p w [] t)).mpr
    ext x
    exact (valid.states t).root_head x
  · apply (Relations.unary_subset rep.label_injective (rep.root_meaning w [] t) (rep.live_meaning w [] t)).mpr
    rintro x rfl
    exact valid.root_live t
  · apply (Relations.unary_subset rep.label_injective
      (Relations.unary_image rep.label_injective (live_term v) (.field 0)
        (rep.live_meaning w [] t) (rep.parent_meaning w [] t)) (rep.live_meaning w [] t)).mpr
    rintro y ⟨x, live, parent⟩
    exact valid.parent_live t (Sum.inl x) (Sum.inl y) live ((complete_parent_object v p source x y).mpr parent)
  · exact rep.coherentFacts_complete p primitive shape ordinary w positive small t (fits t) (valid.states t) fact coherent
  · obtain ⟨d, _, member⟩ := List.mem_flatMap.mp declarations
    exact rep.declarationFacts_complete p primitive shape ordinary w positive small t (fits t) counts valid d fact member

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
