module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionReachability
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsObservations
public import ClaferCompiler.Correctness.Behavioral.Full.StructureCardinality

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace Mixed
variable {U : Type} {f : U → Atom} {S : Set U} {s : Schema} {w : Nat}
  {τ : Trace} {e : Environment} {t : Nat} {r : Rel}

theorem interval_complete (hf : Function.Injective f)
    (rows : Unary f S (r.eval s w τ e t)) (b : IR.Structural.Bounds)
    (fits : Structural.IntervalFits w b S.ncard)
    (range : DPGraph.Predicates.InRange (SemanticsBridge.Structural.bounds b) S) :
    (interval b r).Holds s w τ e t := by
  classical
  have finite := unary_finite hf rows
  let := finite.fintype
  have count := (DPGraph.Predicates.inRange_card _ S).mp range
  rw [Set.fintypeCard_eq_ncard] at count
  have card : (r.eval s w τ e t).eraseDups.length = S.ncard := by
    rw [← List.toFinset_card_of_nodup (Structural.eraseDups_nodup _)]
    have dedup : (r.eval s w τ e t).eraseDups.toFinset = (r.eval s w τ e t).toFinset := by
      ext row
      simp only [List.mem_toFinset, List.mem_eraseDups]
    rw [dedup]
    exact unary_card hf rows
  exact (interval_holds w b r s τ e t).mpr (card ▸ ⟨fits, count⟩)

end Mixed

theorem interval_unrestricted (r : Rel) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (interval ({} : IR.Structural.Bounds) r).Holds s w τ e t := by
  exact (Encoding.holds_and .truth .truth).mpr ⟨True.intro, True.intro⟩

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem contains_parent_inside (p : Fin k) (w t : Nat) (d : Fin k) {x y : Completion o}
    (h : ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y) :
    x ∈ observedDomain w := by
  cases x with
  | inl x => trivial
  | inr z =>
    have hp := h.1.2.2
    cases y with
    | inl y =>
      change source.objects.identities.parent[y].map Sum.inl = some (Sum.inr z) at hp
      simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at hp
    | inr value =>
      change some (Sum.inl source.objects.identities.root) = some (Sum.inr z) at hp
      simp only [Option.some.injEq, reduceCtorEq] at hp

theorem bounded_contains_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (rootLive : (source.objects.at t).live[source.objects.identities.root] = true) (d : Fin k) :
    Mixed.Binary rep.atoms (fun x y =>
      ((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y ∧
        x ∈ observedDomain w ∧ y ∈ observedDomain w)
      ((contains v d).eval (schema v) w target.unfold e t) := by
  cases hd : integerDeclaration v d with
  | false =>
    apply Mixed.binary_congr (rep.contains_completed p primitive w e t d hd)
    intro x y
    exact ⟨fun h => ⟨h, contains_inside p primitive w t d hd h⟩, And.left⟩
  | true =>
    have dp := (integerDeclaration_eq v p primitive d).mp hd
    subst d
    have parent : (v.core.structural.get p).parent = some v.core.structural.root :=
      (v.checked.2.2.2.2.2.1 p primitive).1
    simp only [contains, parent, hd, ↓reduceIte]
    apply Mixed.binary_congr (Mixed.binary_product (root_term v) .ints
      (rep.root_completed p w e t) (rep.ints_completed w positive small e t))
    intro x y
    cases y with
    | inr z =>
      rw [completeContains_integer v p primitive source t p x z]
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, Sum.inr.injEq, observedDomain_integer]
      constructor
      · rintro ⟨rfl, u, rfl, fits⟩
        exact ⟨⟨rfl, rootLive, trivial⟩, trivial, fits⟩
      · rintro ⟨⟨rfl, _, _⟩, _, fits⟩
        exact ⟨rfl, z, rfl, fits⟩
    | inl y =>
      simp only [Set.mem_ofPred_eq, reduceCtorEq, false_and, exists_false, and_false, false_iff, not_and]
      intro contained
      have childHead := completeHead_primitive v p primitive shape source (fun a ha => by
        have ho := ordinary a
        rw [ha, hd] at ho
        contradiction) t
      have hy : Sum.inl y ∈ ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head p :=
        ⟨contained.1.2.1, contained.2.1⟩
      rw [childHead] at hy
      simp only [completeIntegers_domain, reduceCtorEq, exists_false] at hy

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem containmentFacts_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))
    (d c : Fin k) (parent : (v.core.structural.get d).parent = some c)
    (fits : ∀ x ∈ ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c,
      Structural.IntervalFits w (v.core.structural.get d).localBounds
        {y | ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y}.ncard) :
    (Formula.subset (contains v d) (.product (head v c) (head v d))).Holds (schema v) w target.unfold [] t ∧
    (Formula.all (head v d) (.mult .one (.join (.var 0) (.transpose (contains v d))))).Holds (schema v) w target.unfold [] t ∧
    (Formula.all (head v c) (interval (v.core.structural.get d).localBounds (.join (.var 0) (contains v d)))).Holds (schema v) w target.unfold [] t := by
  have sourceParent : (SemanticsBridge.BehavioralStructural.interpret v.core).family.parent d = some c := parent
  have row (e) := rep.bounded_contains_completed p primitive shape ordinary w positive small e t (valid.root_live t) d
  refine ⟨?_, ?_, ?_⟩
  · apply (Mixed.binary_subset rep.atoms.injective (row [])
      (Mixed.binary_product (head_term v c) (head_term v d)
        (rep.bounded_head_completed p primitive shape ordinary w positive small [] t c)
        (rep.bounded_head_completed p primitive shape ordinary w positive small [] t d))).mpr
    rintro x y ⟨h, xi, yi⟩
    obtain ⟨hy, c', parent', hx⟩ := (valid.states t).typed.1 d x y h
    have eq : c' = c := Option.some.inj (parent'.symm.trans sourceParent)
    subst c'
    exact ⟨⟨hx, xi⟩, hy, yi⟩
  · rw [Mixed.all_unary_complete (.mult _ _) (rep.bounded_head_completed p primitive shape ordinary w positive small [] t d)]
    intro x hx
    apply Mixed.unary_one_of_unique (Mixed.unary_image rep.atoms.injective (.var 0)
      (.transpose (contains_term v d)) (Mixed.unary_singleton (f := rep.atoms) x)
      (Mixed.binary_transpose (contains_term v d) (row [rep.atoms x])))
    obtain ⟨y, hy, one⟩ := (valid.states t).parents d c sourceParent x hx.1
    refine ⟨y, ⟨x, rfl, hy, contains_parent_inside p w t d hy, hx.2⟩, ?_⟩
    rintro z ⟨a, ha, h, _, _⟩
    have ha : a = x := ha
    subst a
    exact one z h
  · rw [Mixed.all_unary_complete (interval_built _ _) (rep.bounded_head_completed p primitive shape ordinary w positive small [] t c)]
    intro x hx
    cases hd : integerDeclaration v d with
    | true =>
      have dp := (integerDeclaration_eq v p primitive d).mp hd
      subst d
      rw [(shape p primitive).2.1]
      exact interval_unrestricted _ _ _ _ _ _
    | false =>
      have image := Mixed.unary_image rep.atoms.injective (.var 0) (contains_term v d)
        (Mixed.unary_singleton (f := rep.atoms) x)
        (rep.contains_completed p primitive w [rep.atoms x] t d hd)
      have exactImage : Mixed.Unary rep.atoms
          {y | ((completeTrace v p source).raw
            (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y}
          ((Rel.join (.var 0) (contains v d)).eval (schema v) w target.unfold [rep.atoms x] t) := by
        simpa only [Set.mem_singleton_iff, exists_eq_left] using image
      exact Mixed.interval_complete rep.atoms.injective exactImage _ (fits x hx.1)
        ((valid.states t).multiplicities d c sourceParent x hx.1)

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
