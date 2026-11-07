module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletion

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Clafer.Behavioral

universe u
variable {k : Nat} {U : Type u} (m : Structural.Core k) (τ : Trace (Fin k) U)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The source ancestry closure is single-parented, regardless of concrete or
authored abstract membership. This generalizes the existing static identity
configuration proof without importing its narrower layout/admission predicate. -/
theorem raw_inherits (t : Nat) : (τ.raw m.toEffectiveCore t).Inherits m.toEffectiveCore := by
  intro d c edge x hx
  exact ⟨hx.1, hx.2.tail edge⟩

theorem raw_disjoint (t : Nat) :
    (τ.raw m.toEffectiveCore t).DeclarationDisjoint m.toEffectiveCore := by
  intro d e x hd he
  exact Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)) hd.2 he.2

theorem source_ancestor_rank (rank : Fin k → Nat)
    (decrease : ∀ d e, m.family.super d = some e → rank e < rank d)
    {d e : Fin k} (path : m.toEffectiveCore.Ancestor d e) : rank e ≤ rank d := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail d e _ edge ih => exact (Nat.le_of_lt (decrease d e edge)).trans ih

theorem source_sibling_incomparable (wf : m.WellFormed) {a d e : Fin k}
    (hd : m.family.super d = some a) (he : m.family.super e = some a)
    (different : d ≠ e) : ¬ m.toEffectiveCore.Ancestor d e := by
  intro path
  obtain ⟨rank, decrease⟩ := wf.super_rank
  rcases path.cases_head with eq | ⟨c, edge, rest⟩
  · exact different eq
  · have eq : c = a := Option.some.inj (edge.symm.trans hd)
    subst c
    have le := source_ancestor_rank m rank decrease rest
    have lt := decrease e a he
    omega

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem raw_abstracts (wf : m.WellFormed) (ids : Structural.IdentitiesValid m τ) (t : Nat) :
    Structural.Abstracts m τ t := by
  intro d abstract
  constructor
  · intro x hx
    rcases hx.2.cases_tail with eq | ⟨c, path, edge⟩
    · have conflict : true = false := abstract.symm.trans (eq ▸ ids.concrete x)
      cases conflict
    · exact ⟨c, edge, hx.1, path⟩
  · intro c e hc he different x hboth
    rcases raw_disjoint m τ t c e x hboth.1 hboth.2 with ce | ec
    · exact source_sibling_incomparable m wf hc he different ce
    · exact source_sibling_incomparable m wf he hc different.symm ec

theorem source_root_ancestor (wf : m.WellFormed) {d : Fin k}
    (path : m.toEffectiveCore.Ancestor m.family.root d) : m.family.root = d := by
  rcases path.cases_head with eq | ⟨c, edge, _⟩
  · exact eq
  · rw [wf.root_shape.2.2.1] at edge
    contradiction

theorem raw_root_separate (wf : m.WellFormed) (ids : Structural.IdentitiesValid m τ)
    (t : Nat) : ∀ d, d ≠ m.family.root →
      τ.identities.root ∉ (τ.raw m.toEffectiveCore t).head d := by
  intro d different hx
  have path := hx.2
  rw [ids.root_type] at path
  exact different (source_root_ancestor m wf path).symm

theorem source_ancestor_parent (wf : m.WellFormed) {d e p : Fin k}
    (path : m.toEffectiveCore.Ancestor d e) (parent : m.family.parent e = some p) :
    ∃ q, m.family.parent d = some q ∧ m.toEffectiveCore.Ancestor q p := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨p, parent, .refl⟩
  | @head d s edge _ ih =>
    obtain ⟨q, hq, hqp⟩ := ih
    obtain ⟨r, hr, hrq⟩ := wf.refined_parent d s q edge hq
    exact ⟨r, hr, hrq.trans hqp⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Parent refinement follows actual object ownership along the super chain;
an inherited field is not assigned a second artificial parent. -/
theorem raw_containment_typed (wf : m.WellFormed) (ids : Structural.IdentitiesValid m τ)
    (t : Nat) : ∀ d p x, (τ.raw m.toEffectiveCore t).contains d p x →
      x ∈ (τ.raw m.toEffectiveCore t).head d ∧
        ∃ c, m.family.parent d = some c ∧ p ∈ (τ.raw m.toEffectiveCore t).head c := by
  rintro d p x ⟨⟨hp, hx, hpx⟩, ancestor, hasParent⟩
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hasParent
  obtain ⟨q, hq, hqc⟩ := source_ancestor_parent m wf ancestor hc
  obtain ⟨r, hr, hpr⟩ := ids.parent_typed x p hpx
  have eq : r = q := Option.some.inj (hr.symm.trans hq)
  subst r
  exact ⟨⟨hx, ancestor⟩, c, hc, hp, hpr.trans hqc⟩

theorem raw_parents (wf : m.WellFormed) (ids : Structural.IdentitiesValid m τ)
    (parentLive : ∀ t x p, x ∈ τ.live t → τ.identities.parent x = some p → p ∈ τ.live t)
    (t : Nat) : (τ.raw m.toEffectiveCore t).Parents m.toEffectiveCore := by
  intro d c hc x hx
  have nonroot : x ≠ τ.identities.root := by
    intro eq
    subst x
    have declaration : d ≠ m.family.root := by
      intro eq
      rw [eq, wf.root_shape.1] at hc
      contradiction
    exact raw_root_separate m τ wf ids t d declaration hx
  obtain ⟨p, hp⟩ := ids.parent_exists x nonroot
  refine ⟨p, ⟨⟨parentLive t x p hx.1 hp, hx.1, hp⟩, hx.2, by simp [hc]⟩, ?_⟩
  intro q hq
  exact Option.some.inj (hq.1.2.2.symm.trans hp)

open Backend.Alloy.Behavioral.Full IR.BehavioralStructural

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem complete_root_head (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat)
    (objects : ∀ x, x ∈ ((SemanticsBridge.Behavioral.trace l.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head
        v.core.structural.root ↔ x = l.objects.identities.root) :
    ∀ x, x ∈ ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head
        v.core.structural.root ↔ x = (completeTrace v p l).identities.root := by
  intro x
  cases x with
  | inl x =>
    change (_ ∧ _) ↔ Sum.inl x = Sum.inl l.objects.identities.root
    rw [Sum.inl.injEq]
    exact objects x
  | inr z =>
    rw [completeHead_integer v p primitive]
    exact ⟨fun h => (primitive_ne_root v p primitive h).elim, fun h => by cases h⟩

theorem complete_reaches_object (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (x : Fin o)
    (path : ((SemanticsBridge.Behavioral.trace l.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches
        (Sum.inl x) := by
  induction path with
  | refl => exact .refl
  | @tail x y _ edge ih =>
    obtain ⟨d, hd⟩ := edge
    exact ih.tail ⟨d, (completeContains_objects v p l t d x y).mpr hd⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every primitive is reached directly from root. Nonprimitive reachability
uses the original object path; scalar references cannot create containment. -/
theorem complete_reachable (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat)
    (rootLive : (l.objects.at t).live[l.objects.identities.root] = true)
    (objects : ∀ x, (l.objects.at t).live[x] = true →
      ((SemanticsBridge.Behavioral.trace l.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x) :
    ∀ x ∈ (completeTrace v p l).live t,
      ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x := by
  intro x live
  cases x with
  | inl x => exact complete_reaches_object v p l t x (objects x live)
  | inr z =>
    exact Relation.ReflTransGen.single ⟨p,
      (completeContains_integer v p primitive l t p _ z).mpr ⟨rfl, rootLive, rfl⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- A named nonprimitive extent only observes finite occurrence identities,
although the completed source carrier itself is infinite. -/
theorem completeHead_finite (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (ordinary : d ≠ p) :
    (((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d).Finite := by
  apply (Set.finite_range (Sum.inl : Fin o → Completion o)).subset
  intro x hx
  cases x with
  | inl x => exact ⟨x, rfl⟩
  | inr z =>
    exact (ordinary ((completeHead_integer v p primitive l t d z).mp hx).symm).elim

end ClaferCompiler.Correctness.Behavioral.Full
