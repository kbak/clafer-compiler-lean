module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationScopes

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem compare_defined_of_holds (h : (Formula.compare op a b).Holds s w τ e t) :
    (Formula.compare op a b).Defined s w τ e t := by
  obtain ⟨x, y, hx, hy, _⟩ := h
  change (a.eval s w τ e t).isSome = true ∧ (b.eval s w τ e t).isSome = true
  simp only [hx, hy, Option.isSome_some, and_self]

theorem conj_defined_of_holds (hp : p.Built) (hq : q.Built)
    (left : p.Holds s w τ e t → p.Defined s w τ e t)
    (right : q.Holds s w τ e t → q.Defined s w τ e t)
    (h : (Formula.binary .conj p q).Holds s w τ e t) :
    (Formula.binary .conj p q).Defined s w τ e t := by
  obtain ⟨hl, hr⟩ := (Encoding.holds_and hp hq).mp h
  unfold Formula.Defined
  rw [Formula.fold_binary _ _ _ _ _ hp hq]
  exact ⟨left hl, right hr⟩

theorem all_defined_of_holds (hp : p.Built)
    (body : ∀ e, p.Holds s w τ e t → p.Defined s w τ e t)
    (h : (Formula.all r p).Holds s w τ e t) :
    (Formula.all r p).Defined s w τ e t := by
  rw [Encoding.holds_all hp] at h
  unfold Formula.Defined
  rw [Formula.fold_all _ _ _ hp]
  exact fun x hx => body _ (h x hx)

theorem always_defined_of_holds (hp : p.Built)
    (body : ∀ u, p.Holds s w τ e u → p.Defined s w τ e u)
    (h : (Formula.unary .always p).Holds s w τ e t) :
    (Formula.unary .always p).Defined s w τ e t := by
  rw [always_holds hp] at h
  unfold Formula.Defined
  rw [Formula.fold_unary _ _ _ _ hp]
  exact fun u hu => body u (h u hu)

theorem interval_defined_of_holds (b : IR.Structural.Bounds) (r : Rel)
    (h : (interval b r).Holds s w τ e t) : (interval b r).Defined s w τ e t := by
  cases zero : b.lower == 0 <;> cases upper : b.upper <;>
    simp only [interval, zero, upper, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · exact conj_defined_of_holds (.compare _ _ _) (.compare _ _ _) compare_defined_of_holds compare_defined_of_holds h
  · exact conj_defined_of_holds (.compare _ _ _) .truth compare_defined_of_holds (fun _ => trivial) h
  · exact conj_defined_of_holds .truth (.compare _ _ _) (fun _ => trivial) compare_defined_of_holds h
  · exact conj_defined_of_holds .truth .truth (fun _ => trivial) (fun _ => trivial) h

theorem setKey_defined (v : IR.BehavioralStructural.Validated k) (d p : Fin k) :
    (setKey v d p).Defined s w τ e t := by
  intro _ _ _ _ _ _
  exact ⟨True.intro, True.intro⟩

theorem referenceFacts_defined (v : IR.BehavioralStructural.Validated k)
    (d : Fin k) (f : Formula) (member : f ∈ referenceFacts v d) : f.Defined s w τ e t := by
  unfold referenceFacts at member
  split at member
  · have eq := List.mem_singleton.mp member
    subst f
    trivial
  · rcases List.mem_append.mp member with member | member
    · split at member
      · have eq := List.mem_singleton.mp member
        subst f
        trivial
      · contradiction
    · rcases List.mem_cons.mp member with rfl | member
      · trivial
      · have eq := List.mem_singleton.mp member
        subst f
        exact fun _ _ => True.intro

theorem declarationFacts_defined_of_holds (v : IR.BehavioralStructural.Validated k)
    (d : Fin k) (f : Formula) (member : f ∈ declarationFacts v d)
    (h : f.Holds s w τ e t) : f.Defined s w τ e t := by
  unfold declarationFacts at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with reference | group
    · exact referenceFacts_defined v d f reference
    · split at group
      · contradiction
      · have eq := List.mem_singleton.mp group
        subst f
        exact all_defined_of_holds (interval_built _ _) (fun _ => interval_defined_of_holds _ _) h
  · split at member
    · contradiction
    · rcases List.mem_append.mp member with containment | key
      · rcases List.mem_cons.mp containment with rfl | containment
        · trivial
        · rcases List.mem_cons.mp containment with rfl | containment
          · exact fun _ _ => True.intro
          · have eq := List.mem_singleton.mp containment
            subst f
            exact all_defined_of_holds (interval_built _ _) (fun _ => interval_defined_of_holds _ _) h
      · split at key
        · split at key
          · have eq := List.mem_singleton.mp key
            subst f
            exact setKey_defined _ _ _
          · contradiction
        · contradiction

theorem stateFacts_defined_of_holds (v : IR.BehavioralStructural.Validated k)
    (f : Formula) (member : f ∈ stateFacts v) (h : f.Holds s w τ e t) : f.Defined s w τ e t := by
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> trivial
    · have eq := List.mem_singleton.mp member
      subst f
      exact fun _ _ => True.intro
  · obtain ⟨d, _, member⟩ := List.mem_flatMap.mp member
    exact declarationFacts_defined_of_holds v d f member h

theorem identityFacts_defined (v : IR.BehavioralStructural.Validated k)
    (f : Formula) (member : f ∈ identityFacts v) : f.Defined s w τ e t := by
  rcases List.mem_append.mp member with member | member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · trivial
    · trivial
    · exact fun _ _ => True.intro
  · obtain ⟨d, _, member⟩ := List.mem_flatMap.mp member
    split at member
    · have eq := List.mem_singleton.mp member
      subst f
      trivial
    · split at member
      · contradiction
      · have eq := List.mem_singleton.mp member
        subst f
        exact fun _ _ => True.intro

theorem boundFacts_defined_of_holds (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (f : Formula) (member : f ∈ boundFacts v b)
    (h : f.Holds s w τ e t) : f.Defined s w τ e t := by
  rcases List.mem_cons.mp member with rfl | member
  · exact fun _ _ => True.intro
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp member
    cases exactness : (declaredScope v b d).exact <;>
      simp only [scopeFact, exactness, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
      exact compare_defined_of_holds h

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every satisfied structural clause is strictly defined. Arithmetic occurs
only in positive interval/scope checks, whose truth supplies defined operands. -/
theorem structuralFacts_defined_of_holds (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (f : Formula) (member : f ∈ identityFacts v ++ boundFacts v b ++
      (stateFacts v ++ [reachabilityFact v b.objects]).map (.unary .always))
    (h : f.Holds s w τ e t) : f.Defined s w τ e t := by
  simp only [List.mem_append] at member
  rcases member with (identity | bound) | state
  · exact identityFacts_defined v f identity
  · exact boundFacts_defined_of_holds v b f bound h
  · obtain ⟨inner, member, rfl⟩ := List.mem_map.mp state
    rcases List.mem_append.mp member with state | reach
    · exact always_defined_of_holds (stateFacts_built v inner state)
        (fun _ => stateFacts_defined_of_holds v inner state) h
    · have eq := List.mem_singleton.mp reach
      subst inner
      exact fun _ _ => True.intro

end ClaferCompiler.Correctness.Behavioral.Full
