module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCardinality
public import ClaferCompiler.Correctness.Behavioral.Full.StructureReachability
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionStructure

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem childHeads_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) :
    (childHeads v d).Term := by
  apply union_term _ ?_ _ (.empty _)
  intro r hr
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
  exact .join (.var 0) (contains_term v c)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The target group relation denotes an effective union of original head
occurrences. The ordinary-child premise excludes the full primitive universe. -/
theorem childHeads_source (rep : TraceRep v source target) (w t : Nat) (d : Fin k)
    (p : Fin o)
    (ordinary : ∀ c ∈ IR.BehavioralStructural.childDeclarations v d,
      integerDeclaration v c = false) :
    Relations.Unary rep.label
      {x | Clafer.Semantics.Groups.ChildObjects
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((SemanticsBridge.Behavioral.trace source.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d p x}
      ((childHeads v d).eval (schema v) w target.unfold [.object (rep.label p)] t) := by
  intro row
  unfold childHeads union
  rw [union_rows _ (by
    intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    exact .join (.var 0) (contains_term v c)) _ (.empty _)]
  have empty : (Rel.empty .unary).eval (schema v) w target.unfold [.object (rep.label p)] t = [] := rfl
  rw [empty]
  simp only [List.not_mem_nil, false_or, List.mem_map]
  constructor
  · rintro ⟨r, ⟨c, hc, rfl⟩, hr⟩
    have image := Relations.unary_image rep.label_injective (.var 0) (contains_term v c)
      (Relations.unary_singleton (f := rep.label) p)
      (rep.contains_source w [.object (rep.label p)] t c (ordinary c hc))
    obtain ⟨x, ⟨y, hy, hxy⟩, he⟩ := (image row).mp hr
    have heq : y = p := hy
    subst y
    exact ⟨x, (SemanticsBridge.BehavioralStructural.childObjects_iff v _ d p x).mpr
      ⟨c, hc, hxy⟩, he⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨c, hc, hpx⟩ := (SemanticsBridge.BehavioralStructural.childObjects_iff v _ d p x).mp hx
    have image := Relations.unary_image rep.label_injective (.var 0) (contains_term v c)
      (Relations.unary_singleton (f := rep.label) p)
      (rep.contains_source w [.object (rep.label p)] t c (ordinary c hc))
    exact ⟨.join (.var 0) (contains v c), ⟨c, hc, rfl⟩,
      (image row).mpr ⟨x, ⟨p, rfl, hpx⟩, he⟩⟩

theorem local_bounds (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d c : Fin k) (hp : (v.core.structural.get d).parent = some c)
    (ordinaryD : integerDeclaration v d = false) (ordinaryC : integerDeclaration v c = false)
    (p : Fin o)
    (live : p ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c) :
    DPGraph.Predicates.InRange (SemanticsBridge.Structural.bounds (v.core.structural.get d).localBounds)
      {x : Fin o // ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d p x} := by
  classical
  have generated := facts (.all (head v c)
      (interval (v.core.structural.get d).localBounds (.join (.var 0) (contains v d))))
    (declaration_mem v d _ (by simp [declarationFacts, hp]))
  have body : (interval (v.core.structural.get d).localBounds (.join (.var 0) (contains v d))).Holds
      (schema v) w target.unfold [.object (rep.label p)] t := by
    rw [Encoding.holds_all (interval_built _ _)] at generated
    exact generated _ ((rep.head_source w [] t c ordinaryC _).mpr ⟨p, live, rfl⟩)
  have image := Relations.unary_image rep.label_injective (.var 0) (contains_term v d)
    (Relations.unary_singleton (f := rep.label) p)
    (rep.contains_source w [.object (rep.label p)] t d ordinaryD)
  have exactImage : Relations.Unary rep.label
      {x | ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d p x}
      ((Rel.join (.var 0) (contains v d)).eval (schema v) w target.unfold [.object (rep.label p)] t) := by
    simpa only [Set.mem_singleton_iff, exists_eq_left] using image
  exact ((interval_source _ rep.label rep.label_injective _ _ _ _ _ _ exactImage _).mp body).2

theorem group_bounds (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (concrete : v.core.authoredAbstract[d] = false)
    (ordinaryD : integerDeclaration v d = false)
    (ordinaryChildren : ∀ c ∈ IR.BehavioralStructural.childDeclarations v d,
      integerDeclaration v c = false) :
    Clafer.Semantics.Groups.Holds (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d := by
  classical
  intro p
  have generated := facts (.all (head v d)
      (interval (v.core.structural.get d).groupBounds (childHeads v d)))
    (declaration_mem v d _ (by simp [declarationFacts, concrete]))
  have body : (interval (v.core.structural.get d).groupBounds (childHeads v d)).Holds
      (schema v) w target.unfold [.object (rep.label p.val)] t := by
    rw [Encoding.holds_all (interval_built _ _)] at generated
    exact generated _ ((rep.head_source w [] t d ordinaryD _).mpr ⟨p.val, p.property, rfl⟩)
  have range := ((interval_source _ rep.label rep.label_injective _ _ _ _ _ _
    (rep.childHeads_source w t d p.val ordinaryChildren) _).mp body).2
  have agrees := (SemanticsBridge.BehavioralStructural.validated_wellFormed v).group_agrees d
  rw [← agrees]
  exact range

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- A nonroot group with a syntactically inherited primitive child has no live
owner. Root-head equality handles this rich-admission edge case explicitly. -/
theorem group_bounds_nonroot (rep : TraceRep v source target) (w t : Nat)
    (shape : PrimitiveShape v)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (concrete : v.core.authoredAbstract[d] = false)
    (ordinaryD : integerDeclaration v d = false) (nonroot : d ≠ v.core.structural.root) :
    Clafer.Semantics.Groups.Holds (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d := by
  classical
  by_cases ordinary : ∀ c ∈ IR.BehavioralStructural.childDeclarations v d,
      integerDeclaration v c = false
  · exact rep.group_bounds w t facts d concrete ordinaryD ordinary
  · push Not at ordinary
    obtain ⟨c, hc, primitive⟩ := ordinary
    have primitive : (v.core.structural.get c).origin = .integer := by
      simpa [integerDeclaration] using Bool.eq_true_of_not_eq_false primitive
    have parent := (v.checked.2.2.2.2.2.1 c primitive).1
    have ancestor : v.core.structural.root ∈ v.analysis.ancestors[d] := by
      simpa only [IR.BehavioralStructural.childDeclarations, List.mem_filter,
        List.mem_finRange, true_and, parent, Option.map_some, Option.getD_some,
        decide_eq_true_eq] using hc
    intro x
    have headRoot := (rep.root_head w t identity facts x.val).mp
      ⟨x.property.1, x.property.2.trans ((ancestor_iff v d _).mp ancestor)⟩
    have separate := raw_root_separate (SemanticsBridge.BehavioralStructural.interpret v.core)
      (SemanticsBridge.Behavioral.trace source.objects)
      (SemanticsBridge.BehavioralStructural.validated_wellFormed v)
      (rep.identities_valid w shape identity) t d nonroot
    apply False.elim
    apply separate
    change source.objects.identities.root ∈ _
    rw [← headRoot]
    exact x.property

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
