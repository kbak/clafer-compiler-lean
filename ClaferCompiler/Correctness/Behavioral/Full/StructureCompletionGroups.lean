module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionContainment
public import ClaferCompiler.Correctness.Behavioral.Full.StructureGroups

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem bounded_childHeads_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (rootLive : (source.objects.at t).live[source.objects.identities.root] = true)
    (d : Fin k) (x : Completion o) (inside : x ∈ observedDomain w) :
    Mixed.Unary rep.atoms {y | Clafer.Semantics.Groups.ChildObjects
      (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y ∧ y ∈ observedDomain w}
      ((childHeads v d).eval (schema v) w target.unfold [rep.atoms x] t) := by
  intro row
  unfold childHeads union
  rw [union_rows _ (by
    intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    exact .join (.var 0) (contains_term v c)) _ (.empty _)]
  have empty : (Rel.empty .unary).eval (schema v) w target.unfold [rep.atoms x] t = [] := rfl
  rw [empty]
  simp only [List.not_mem_nil, false_or, List.mem_map]
  constructor
  · rintro ⟨r, ⟨c, hc, rfl⟩, hr⟩
    have image := Mixed.unary_image rep.atoms.injective (.var 0) (contains_term v c)
      (Mixed.unary_singleton (f := rep.atoms) x)
      (rep.bounded_contains_completed p primitive shape ordinary w positive small [rep.atoms x] t rootLive c)
    obtain ⟨y, ⟨a, ha, contained, _, bounded⟩, he⟩ := (image row).mp hr
    have ha : a = x := ha
    subst a
    exact ⟨y, ⟨(SemanticsBridge.BehavioralStructural.childObjects_iff v _ d x y).mpr
      ⟨c, hc, contained⟩, bounded⟩, he⟩
  · rintro ⟨y, ⟨child, bounded⟩, he⟩
    obtain ⟨c, hc, contained⟩ := (SemanticsBridge.BehavioralStructural.childObjects_iff v _ d x y).mp child
    have image := Mixed.unary_image rep.atoms.injective (.var 0) (contains_term v c)
      (Mixed.unary_singleton (f := rep.atoms) x)
      (rep.bounded_contains_completed p primitive shape ordinary w positive small [rep.atoms x] t rootLive c)
    exact ⟨_, ⟨c, hc, rfl⟩, (image row).mpr ⟨y, ⟨x, rfl, contained, inside, bounded⟩, he⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem groupFact_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
    (d : Fin k) (concrete : v.core.authoredAbstract[d] = false)
    (fits : ∀ x ∈ ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d,
      Structural.IntervalFits w (v.core.structural.get d).groupBounds
        {y | Clafer.Semantics.Groups.ChildObjects
          (SemanticsBridge.BehavioralStructural.interpret v.core).family
          ((completeTrace v p source).raw
            (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y}.ncard) :
    (Formula.all (head v d) (interval (v.core.structural.get d).groupBounds (childHeads v d))).Holds
      (schema v) w target.unfold [] t := by
  rw [Mixed.all_unary_complete (interval_built _ _) (rep.bounded_head_completed p primitive shape ordinary w positive small [] t d)]
  intro x hx
  by_cases unrestricted : (v.core.structural.get d).groupBounds = {}
  · rw [unrestricted]
    exact interval_unrestricted _ _ _ _ _ _
  · have nonroot : d ≠ v.core.structural.root := by
      intro eq
      exact unrestricted (eq ▸ (shape p primitive).2.2.2.1)
    have notRoot : x ≠ (completeTrace v p source).identities.root := by
      intro eq
      exact (valid.states t).root_separate d nonroot (eq ▸ hx.1)
    have bounded (y : Completion o) (h : Clafer.Semantics.Groups.ChildObjects
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y) : y ∈ observedDomain w := by
      cases y with
      | inl y => trivial
      | inr z =>
        obtain ⟨_, _, c, _, contained⟩ := h
        exact (notRoot ((completeContains_integer v p primitive source t c x z).mp contained).1).elim
    have rows := Mixed.unary_congr
      (rep.bounded_childHeads_completed p primitive shape ordinary w positive small t (valid.root_live t) d x hx.2)
      (fun y => show (_ ∧ y ∈ observedDomain w) ↔ _ from ⟨And.left, fun h => ⟨h, bounded y h⟩⟩)
    apply Mixed.interval_complete rep.atoms.injective rows _ (fits x hx.1)
    have range := (valid.states t).groups d concrete ⟨x, hx.1⟩
    have agrees := (SemanticsBridge.BehavioralStructural.validated_wellFormed v).group_agrees d
    rw [← agrees] at range
    exact range

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
