module

public import ClaferCompiler.Correctness.Behavioral.RepresentationRelations
public import ClaferCompiler.Correctness.StructuralCompletionDeclarations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

theorem poolUnion_term (v : IR.Structural.Layout k) (ds : List (Fin k))
    (initial : Rel) (hi : initial.Term) :
    ((ds.map (pool v)).foldl Rel.union initial).Term := by
  induction ds generalizing initial with
  | nil => exact hi
  | cons d ds ih => exact ih (initial.union (pool v d)) (.union hi (.sig _))

theorem poolUnion_rows (v : IR.Structural.Layout k) (ds : List (Fin k))
    (initial : Rel) (hi : initial.Term) (w : Nat) (τ : Trace) (e : Environment) (t : Nat) (row : List Atom) :
    row ∈ ((ds.map (pool v)).foldl Rel.union initial).eval (schema v) w τ e t ↔
      row ∈ initial.eval (schema v) w τ e t ∨
        ∃ d ∈ ds, row ∈ (pool v d).eval (schema v) w τ e t := by
  induction ds generalizing initial with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih (initial.union (pool v d)) (.union hi (show (pool v d).Term from .sig _))]
    rw [Rel.eval_union hi (show (pool v d).Term from .sig _)]
    simp only [List.mem_eraseDups, List.mem_append, List.mem_cons]
    aesop

theorem no_reverse_super (v : IR.Structural.Layout k) (d c : Fin k)
    (h : (v.core.get c).super = some d) :
    ¬ (SemanticsBridge.Structural.interpret v.core).Ancestor d c := by
  intro path
  have le := Structural.ancestor_rank v path
  have lt := v.coreChecked.2.2.2.2.1 c d h
  omega

namespace TraceRep

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Lasso}

theorem pool_atom (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) (x : Fin o) :
    [.object (rep.label x)] ∈ (pool v d).eval (schema v) w target.unfold e t ↔
      IR.Behavioral.ancestor v.core source.identities.directType[x] d = true := by
  rw [rep.pool_meaning w e t d]
  constructor
  · rintro ⟨y, hy, he⟩
    have he : x = y := rep.label_injective (by simpa using he)
    exact he ▸ hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem direct_pool_atom (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (x : Fin o) :
    [.object (rep.label x)] ∈ (directPool v source.identities.directType[x]).eval
      (schema v) w target.unfold e t := by
  rw [directPool, Rel.eval_diff (show (pool v source.identities.directType[x]).Term from .sig _)
    (poolUnion_term v _ _ (.empty _))]
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  refine ⟨(rep.pool_atom w e t _ x).mpr ((ancestor_agrees _ _ _).mpr .refl), ?_⟩
  intro h
  rcases (poolUnion_rows v _ _ (.empty _) w target.unfold e t _).mp h with hempty | ⟨c, hc, hp⟩
  · exact List.not_mem_nil hempty
  · exact no_reverse_super v _ c ((Backend.Alloy.Structural.subtype_inventory v.core _ c).mp hc)
      ((ancestor_agrees _ _ _).mp ((rep.pool_atom w e t c x).mp hp))

-- [proof->req~compiler-behavioral-correctness~1]
theorem concrete_type (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x : Fin o) : (v.core.get source.identities.directType[x]).isAbstract = false := by
  cases ha : (v.core.get source.identities.directType[x]).isAbstract with
  | false => rfl
  | true =>
    let d := source.identities.directType[x]
    have h := facts (.equal (pool v d) (((Backend.Alloy.Structural.subtypes v.core d).map (pool v)).foldl
      Rel.union (.empty .unary))) (by
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨d, List.mem_finRange _, ?_⟩
        have ha' : (v.core.get d).isAbstract = true := ha
        simp only [ha', ↓reduceIte, List.mem_singleton])
    have hm := (rep.pool_atom w [] 0 d x).mpr ((ancestor_agrees _ _ _).mpr .refl)
    have right := (h [.object (rep.label x)]).mp hm
    rcases (poolUnion_rows v _ _ (.empty _) w target.unfold [] 0 _).mp right with hempty | ⟨c, hc, hp⟩
    · exact (List.not_mem_nil hempty).elim
    · exact (no_reverse_super v d c ((Backend.Alloy.Structural.subtype_inventory v.core d c).mp hc)
        ((ancestor_agrees _ _ _).mp ((rep.pool_atom w [] 0 c x).mp hp))).elim

theorem root_type (rep : TraceRep v source target) :
    source.identities.directType[source.identities.root] = v.core.root := by
  apply (Structural.ancestor_root_iff v _).mp
  apply (ancestor_agrees v.core _ _).mp
  exact (rep.pool_label 0 v.core.root source.identities.root).mp ((rep.roots 0 _).mpr rfl)

theorem root_only (rep : TraceRep v source target) (x : Fin o)
    (hx : source.identities.directType[x] = v.core.root) : x = source.identities.root := by
  apply rep.label_injective
  apply (rep.roots 0 _).mp
  apply (rep.pool_label 0 v.core.root x).mpr
  apply (ancestor_agrees v.core _ _).mpr
  rw [hx]
  exact .refl

-- [proof->req~compiler-behavioral-correctness~1]
theorem root_live (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    (source.at t).live[source.identities.root] = true := by
  have h := facts (.subset (root v) (live v)) (by simp [stateFacts])
  have hs := (Relations.unary_subset rep.label_injective
    (rep.root_meaning w [] t) (rep.live_meaning w [] t)).mp h
  exact hs (Set.mem_singleton _)

theorem parent_live (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (x p : Fin o) (hx : (source.at t).live[x] = true)
    (hp : source.identities.parent[x] = some p) : (source.at t).live[p] = true := by
  have h := facts (.subset (.join (live v) parent) (live v)) (by simp [stateFacts])
  have image := Relations.unary_image rep.label_injective (live_term v) (.field 0)
    (rep.live_meaning w [] t) (rep.parent_meaning w [] t)
  exact ((Relations.unary_subset rep.label_injective image (rep.live_meaning w [] t)).mp h)
    ⟨x, hx, hp⟩

theorem root_parent (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0) :
    source.identities.parent[source.identities.root] = none := by
  have h := facts (.equal (.join (root v) parent) (.empty .unary)) (by simp [identityFacts])
  have image := Relations.unary_image rep.label_injective (root_term v) (.field 0)
    (rep.root_meaning w [] 0) (rep.parent_meaning w [] 0)
  have he := (Relations.unary_equal rep.label_injective image Relations.unary_empty).mp h
  cases hp : source.identities.parent[source.identities.root] with
  | none => rfl
  | some p =>
    have : p ∈ (∅ : Set (Fin o)) := he ▸ ⟨source.identities.root, rfl, hp⟩
    exact this.elim

theorem total_parent (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x : Fin o) (hx : x ≠ source.identities.root) :
    ∃ p, source.identities.parent[x] = some p := by
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

theorem parent_typed (rep : TraceRep v source target) (w : Nat)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (x p : Fin o) (hp : source.identities.parent[x] = some p) :
    ∃ c : Fin k, (v.core.get source.identities.directType[x]).parent = some c ∧
      IR.Behavioral.ancestor v.core source.identities.directType[p] c = true := by
  have concrete := rep.concrete_type w facts x
  cases hc : (v.core.get source.identities.directType[x]).parent with
  | none =>
    have nonroot : source.identities.directType[x] ≠ v.core.root := by
      intro hr
      have hx := rep.root_only x hr
      have noParent := rep.root_parent w facts
      rw [hx, noParent] at hp
      cases hp
    have hab := v.coreChecked.2.2.2.2.2.2 source.identities.directType[x] hc nonroot
    have impossible : false = true := concrete.symm.trans hab
    cases impossible
  | some c =>
    refine ⟨c, rfl, ?_⟩
    let d := source.identities.directType[x]
    have h := facts (.all (directPool v d) (.subset (.join (.var 0) parent) (pool v c))) (by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨d, List.mem_finRange _, ?_⟩
      have concrete' : (v.core.get d).isAbstract = false := concrete
      have hc' : (v.core.get d).parent = some c := hc
      simp only [concrete', Bool.false_eq_true, ↓reduceIte, hc', List.mem_singleton])
    have body : (Formula.subset (.join (.var 0) parent) (pool v c)).Holds (schema v) w
        target.unfold [.object (rep.label x)] 0 := by
      change ∀ atom, [atom] ∈ (directPool v d).eval (schema v) w target.unfold [] 0 → _ at h
      exact h _ (rep.direct_pool_atom w [] 0 x)
    have image := Relations.unary_image rep.label_injective (.var 0) (.field 0)
      (Relations.unary_singleton (f := rep.label) x)
      (rep.parent_meaning w [.object (rep.label x)] 0)
    have sub := (Relations.unary_subset rep.label_injective image
      (rep.pool_meaning w [.object (rep.label x)] 0 c)).mp body
    exact sub ⟨x, rfl, hp⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- Generated target facts derive the source identity invariants. Source label
uniqueness is supplied by the finite decoder's data check, not source validity. -/
theorem identity_checks (rep : TraceRep v source target) (w : Nat)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0) :
    IR.Behavioral.identityChecks v.core source.identities :=
  ⟨unique, rep.root_type, rep.root_only, rep.concrete_type w facts,
    rep.root_parent w facts, rep.total_parent w facts, rep.parent_typed w facts⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- The remaining premise is precisely the independently transported structural
snapshot contract; all fixed identity and lifetime invariants follow from facts. -/
theorem source_valid (rep : TraceRep v source target) (w : Nat)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (snapshots : ∀ t, (trace source).StateValid (SemanticsBridge.Structural.interpret v.core) t) :
    (trace source).Valid (SemanticsBridge.Structural.interpret v.core) :=
  ⟨identityChecks_valid v.core _ (rep.identity_checks w unique identity),
    fun t => rep.root_live w t (states t),
    fun t x p hx hp => rep.parent_live w t (states t) x p hx hp, snapshots⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral
