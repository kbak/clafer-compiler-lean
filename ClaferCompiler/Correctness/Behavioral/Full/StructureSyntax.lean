module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCardinality

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem setKey_built (v : IR.BehavioralStructural.Validated k) (d p : Fin k) :
    (setKey v d p).Built :=
  .all _ (.all _ (.all _ (.binary .implies (.equal _ _) (.equal _ _))))

theorem referenceFacts_built (v : IR.BehavioralStructural.Validated k)
    (d : Fin k) (f : Formula) (member : f ∈ referenceFacts v d) : f.Built := by
  unfold referenceFacts at member
  split at member
  · have eq := List.mem_singleton.mp member
    subst f
    exact .equal _ _
  · rcases List.mem_append.mp member with member | member
    · split at member
      · have eq := List.mem_singleton.mp member
        subst f
        exact .equal _ _
      · contradiction
    · rcases List.mem_cons.mp member with rfl | member
      · exact .subset _ _
      · have eq := List.mem_singleton.mp member
        subst f
        exact .all _ (.mult _ _)

theorem declarationFacts_built (v : IR.BehavioralStructural.Validated k)
    (d : Fin k) (f : Formula) (member : f ∈ declarationFacts v d) : f.Built := by
  unfold declarationFacts at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with reference | group
    · exact referenceFacts_built v d f reference
    · split at group
      · contradiction
      · have eq := List.mem_singleton.mp group
        subst f
        exact .all _ (interval_built _ _)
  · split at member
    · contradiction
    · rcases List.mem_append.mp member with containment | key
      · rcases List.mem_cons.mp containment with rfl | containment
        · exact .subset _ _
        · rcases List.mem_cons.mp containment with rfl | containment
          · exact .all _ (.mult _ _)
          · have eq := List.mem_singleton.mp containment
            subst f
            exact .all _ (interval_built _ _)
      · split at key
        · split at key
          · have eq := List.mem_singleton.mp key
            subst f
            exact setKey_built _ _ _
          · contradiction
        · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem stateFacts_built (v : IR.BehavioralStructural.Validated k)
    (f : Formula) (member : f ∈ stateFacts v) : f.Built := by
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact .subset _ _
      · exact .equal _ _
      · exact .subset _ _
      · exact .subset _ _
    · have eq := List.mem_singleton.mp member
      subst f
      exact .all _ (.mult _ _)
  · obtain ⟨d, _, member⟩ := List.mem_flatMap.mp member
    exact declarationFacts_built v d f member

theorem always_holds (built : f.Built) :
    (Formula.unary .always f).Holds s w τ e t ↔ ∀ u, t ≤ u → f.Holds s w τ e u := by
  unfold Formula.Holds
  rw [Formula.fold_unary _ _ _ _ built]
  rfl

end ClaferCompiler.Correctness.Behavioral.Full
