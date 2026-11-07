module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem direct_pool_atom (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (x : Fin o) :
    [.object (rep.label x)] ∈ (directPool source.objects.identities.directType[x]).eval
      (schema v) w target.unfold e t :=
  (rep.direct_meaning w e t _ _).mpr ⟨x, rfl, rfl⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem ordinary_concrete (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x : Fin o) :
    v.core.authoredAbstract[source.objects.identities.directType[x]] = false ∧
      integerDeclaration v source.objects.identities.directType[x] = false := by
  let d := source.objects.identities.directType[x]
  have hfalse : (v.core.authoredAbstract[d] || integerDeclaration v d) = false := by
    cases ha : (v.core.authoredAbstract[d] || integerDeclaration v d) with
    | false => rfl
    | true =>
      have h := facts (.equal (directPool d) (.empty .unary)) (by
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨d, List.mem_finRange _, ?_⟩
        simp only [ha, ↓reduceIte, List.mem_singleton])
      have impossible := (h [.object (rep.label x)]).mp (rep.direct_pool_atom w [] 0 x)
      exact List.not_mem_nil impossible |>.elim
  exact Bool.or_eq_false_iff.mp hfalse

theorem root_type (rep : TraceRep v source target) :
    source.objects.identities.directType[source.objects.identities.root] = v.core.structural.root := by
  exact (rep.direct_type 0 _ _).mp ((rep.roots 0 _).mpr rfl)

theorem root_only (rep : TraceRep v source target) (x : Fin o)
    (hx : source.objects.identities.directType[x] = v.core.structural.root) :
    x = source.objects.identities.root := by
  exact rep.label_injective ((rep.roots 0 _).mp ((rep.direct_type 0 _ _).mpr hx))

theorem root_parent (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0) :
    source.objects.identities.parent[source.objects.identities.root] = none := by
  have h := facts (.equal (.join (root v) parent) (.empty .unary)) (by simp [identityFacts])
  have image := Relations.unary_image rep.label_injective (root_term v) (.field 0)
    (rep.root_meaning w [] 0) (rep.parent_meaning w [] 0)
  have he := (Relations.unary_equal rep.label_injective image Relations.unary_empty).mp h
  cases hp : source.objects.identities.parent[source.objects.identities.root] with
  | none => rfl
  | some p =>
    have : p ∈ (∅ : Set (Fin o)) := he ▸ ⟨source.objects.identities.root, rfl, hp⟩
    exact this.elim

theorem total_parent (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x : Fin o) (hx : x ≠ source.objects.identities.root) :
    ∃ p, source.objects.identities.parent[x] = some p := by
  have h := facts (.all (.diff (.sig 0) (root v)) (.mult .one (.join (.var 0) parent)))
    (by simp [identityFacts])
  have domain := Relations.unary_diff rep.label_injective (.sig 0) (root_term v)
    (rep.objects_meaning w [] 0) (rep.root_meaning w [] 0)
  have inDomain := (domain [.object (rep.label x)]).mpr ⟨x, ⟨Set.mem_univ _, hx⟩, rfl⟩
  have hx' : (Formula.mult .one (.join (.var 0) parent)).Holds (schema v) w
      target.unfold [.object (rep.label x)] 0 := by
    change ∀ atom, [atom] ∈ (Rel.diff (.sig 0) (root v)).eval (schema v) w target.unfold [] 0 → _ at h
    exact h _ inDomain
  have image := Relations.unary_image rep.label_injective (.var 0) (.field 0)
    (Relations.unary_singleton (f := rep.label) x)
    (rep.parent_meaning w [.object (rep.label x)] 0)
  have one : ((Rel.join (.var 0) parent).eval (schema v) w target.unfold
      [.object (rep.label x)] 0).eraseDups.length = 1 := by
    simpa [Formula.Holds, Formula.mult, Formula.fold, FormulaAlgebra.step,
      formulaAlgebra, Backend.Alloy.Multiplicity.holds] using hx'
  obtain ⟨row, hr⟩ := List.length_pos_iff_exists_mem.mp (show 0 <
      ((Rel.join (.var 0) parent).eval (schema v) w target.unfold [.object (rep.label x)] 0).eraseDups.length by omega)
  obtain ⟨p, ⟨y, hy, hp⟩, _⟩ := (image row).mp (List.mem_eraseDups.mp hr)
  exact ⟨p, hy ▸ hp⟩

theorem parent_typed (rep : TraceRep v source target) (w : Nat) (shape : PrimitiveShape v)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x p : Fin o) (hp : source.objects.identities.parent[x] = some p) :
    ∃ c : Fin k, (v.core.structural.get source.objects.identities.directType[x]).parent = some c ∧
      c ∈ v.analysis.ancestors[source.objects.identities.directType[p]] := by
  have concrete := rep.ordinary_concrete w facts x
  cases hc : (v.core.structural.get source.objects.identities.directType[x]).parent with
  | none =>
    have nonroot : source.objects.identities.directType[x] ≠ v.core.structural.root := by
      intro hr
      have hx := rep.root_only x hr
      have noParent := rep.root_parent w facts
      rw [hx, noParent] at hp
      cases hp
    have authored := v.checked.2.2.2.2.1 _ hc nonroot
    have impossible := concrete.1.symm.trans authored
    cases impossible
  | some c =>
    have ordinary : integerDeclaration v c = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hcint : (v.core.structural.get c).origin = .integer := by
        simpa [integerDeclaration] using h
      exact (shape c hcint).2.2.2.2.2 _ hc
    refine ⟨c, rfl, ?_⟩
    let d := source.objects.identities.directType[x]
    have h := facts (.all (directPool d) (.subset (.join (.var 0) parent) (pool v c))) (by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨d, List.mem_finRange _, ?_⟩
      have concrete' : v.core.authoredAbstract[d] = false := concrete.1
      have ordinary' : integerDeclaration v d = false := concrete.2
      have hc' : (v.core.structural.get d).parent = some c := hc
      simp only [concrete', ordinary', Bool.or_self, Bool.false_eq_true, ↓reduceIte, hc', List.mem_singleton])
    have body : (Formula.subset (.join (.var 0) parent) (pool v c)).Holds (schema v) w
        target.unfold [.object (rep.label x)] 0 := by
      change ∀ atom, [atom] ∈ (directPool d).eval (schema v) w target.unfold [] 0 → _ at h
      exact h _ (rep.direct_pool_atom w [] 0 x)
    have image := Relations.unary_image rep.label_injective (.var 0) (.field 0)
      (Relations.unary_singleton (f := rep.label) x)
      (rep.parent_meaning w [.object (rep.label x)] 0)
    have sub := (Relations.unary_subset rep.label_injective image
      (rep.pool_meaning w [.object (rep.label x)] 0 c ordinary)).mp body
    exact sub ⟨x, rfl, hp⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Concrete generated facts imply the rich source identity invariant on the
observed object carrier. This is not an assumed structural validity field. -/
theorem identities_valid (rep : TraceRep v source target) (w : Nat) (shape : PrimitiveShape v)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0) :
    Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core)
      (SemanticsBridge.Behavioral.trace source.objects) := by
  refine ⟨rep.root_type, rep.root_only, fun x => (rep.ordinary_concrete w facts x).1,
    rep.root_parent w facts, rep.total_parent w facts, ?_⟩
  intro x p hp
  obtain ⟨c, hc, ha⟩ := rep.parent_typed w shape facts x p hp
  exact ⟨c, hc, SemanticsBridge.BehavioralStructural.ancestor_sound
    v.checked.2.1 v.checked.1.2.2.2.2.1 ha⟩

theorem root_live (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    (source.objects.at t).live[source.objects.identities.root] = true := by
  have h := facts (.subset (root v) (live v)) (by simp [stateFacts])
  have hs := (Relations.unary_subset rep.label_injective
    (rep.root_meaning w [] t) (rep.live_meaning w [] t)).mp h
  exact hs (Set.mem_singleton _)

theorem parent_live (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (x p : Fin o) (hx : (source.objects.at t).live[x] = true)
    (hp : source.objects.identities.parent[x] = some p) : (source.objects.at t).live[p] = true := by
  have h := facts (.subset (.join (live v) parent) (live v)) (by simp [stateFacts])
  have image := Relations.unary_image rep.label_injective (live_term v) (.field 0)
    (rep.live_meaning w [] t) (rep.parent_meaning w [] t)
  exact ((Relations.unary_subset rep.label_injective image (rep.live_meaning w [] t)).mp h)
    ⟨x, hx, hp⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
