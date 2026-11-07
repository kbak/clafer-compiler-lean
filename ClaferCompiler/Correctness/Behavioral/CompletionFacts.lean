module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsAttachment
public import ClaferCompiler.Correctness.Behavioral.RepresentationInvariants

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open Encoding
open SemanticsBridge.Behavioral

namespace Relations

theorem unary_singleton_card {U : Type} {f : U → Nat} {x : U} {r : Relation}
    (h : Unary f {x} r) : r.eraseDups = [[.object (f x)]] := by
  have hm : ∀ row, row ∈ r.eraseDups ↔ row = [.object (f x)] := by
    intro row
    simpa only [List.mem_eraseDups, Set.mem_singleton_iff, exists_eq_left] using h row
  have hn := Structural.eraseDups_nodup r
  cases he : r.eraseDups with
  | nil => have := (hm [.object (f x)]).mpr rfl; simp [he] at this
  | cons row rows =>
    have hr : row = [.object (f x)] := (hm row).mp (by simp [he])
    have hrs : rows = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      have hyx := (hm y).mp (by simp [he, hy])
      simp only [he, List.nodup_cons] at hn
      exact hn.1 (hr.symm ▸ hyx ▸ hy)
    simp [hr, hrs]

theorem unary_one_of_singleton {U : Type} {f : U → Nat} {x : U}
    (h : Unary f {x} (r.eval s w τ e t)) : (Formula.mult .one r).Holds s w τ e t := by
  change ((_ : Relation).eraseDups.length == 1) = true
  rw [unary_singleton_card h]
  rfl

end Relations

-- [proof->req~compiler-behavioral-correctness~1]
theorem identityFacts_defined (v : IR.Structural.Layout k) (w : Nat) (τ : Trace)
    (e : Environment) (t : Nat) (fact : Formula) (hf : fact ∈ identityFacts v) :
    fact.Defined (schema v) w τ e t := by
  simp only [identityFacts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl) | hf
  · trivial
  · trivial
  · exact fun _ _ => trivial
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hf
    cases ha : (v.core.get d).isAbstract with
    | true =>
      simp only [ha, ↓reduceIte, List.mem_singleton] at hd
      subst fact
      trivial
    | false =>
      cases hp : (v.core.get d).parent with
      | none => simp [ha, hp] at hd
      | some p =>
        simp only [ha, Bool.false_eq_true, ↓reduceIte, hp, List.mem_singleton] at hd
        subst fact
        exact fun _ _ => trivial

namespace TraceRep
variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps} {target : Lasso}

-- [proof->req~compiler-behavioral-correctness~1]
theorem directPool_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) :
    Relations.Unary rep.label {x | source.identities.directType[x] = d}
      ((directPool v d).eval (schema v) w target.unfold e t) := by
  intro row
  rw [directPool, Rel.eval_diff (show (pool v d).Term from .sig _) (poolUnion_term v _ _ (.empty _))]
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro ⟨hr, hn⟩
    obtain ⟨x, hx, rfl⟩ := (rep.pool_meaning w e t d row).mp hr
    refine ⟨x, ?_, rfl⟩
    rcases ((ancestor_agrees _ _ _).mp hx).cases_tail with he | ⟨c, path, edge⟩
    · exact he.symm
    · exfalso
      apply hn
      apply (poolUnion_rows v _ _ (.empty _) w target.unfold e t _).mpr
      exact Or.inr ⟨c, (Backend.Alloy.Structural.subtype_inventory v.core d c).mpr edge,
        (rep.pool_atom w e t c x).mpr ((ancestor_agrees _ _ _).mpr path)⟩
  · rintro ⟨x, hx, rfl⟩
    have hm := rep.direct_pool_atom w e t x
    rw [hx, directPool, Rel.eval_diff (show (pool v d).Term from .sig _)
      (poolUnion_term v _ _ (.empty _))] at hm
    simpa using hm

theorem abstract_pool_complete (rep : TraceRep v source target) (w : Nat) (d : Fin k)
    (ha : (v.core.get d).isAbstract = true)
    (concrete : ∀ x : Fin o, (v.core.get source.identities.directType[x]).isAbstract = false) :
    (Formula.equal (pool v d) (((Backend.Alloy.Structural.subtypes v.core d).map (pool v)).foldl
      Rel.union (.empty .unary))).Holds (schema v) w target.unfold [] 0 := by
  intro row
  rw [poolUnion_rows v _ _ (.empty _) w target.unfold [] 0 row]
  constructor
  · intro hr
    obtain ⟨x, hx, rfl⟩ := (rep.pool_meaning w [] 0 d row).mp hr
    rcases ((ancestor_agrees _ _ _).mp hx).cases_tail with he | ⟨c, path, edge⟩
    · have impossible : true = false := ha.symm.trans (he ▸ concrete x)
      cases impossible
    · exact Or.inr ⟨c, (Backend.Alloy.Structural.subtype_inventory v.core d c).mpr edge,
        (rep.pool_atom w [] 0 c x).mpr ((ancestor_agrees _ _ _).mpr path)⟩
  · rintro (he | ⟨c, hc, hr⟩)
    · exact (List.not_mem_nil he).elim
    · obtain ⟨x, hx, rfl⟩ := (rep.pool_meaning w [] 0 c row).mp hr
      exact (rep.pool_atom w [] 0 d x).mpr ((ancestor_agrees _ _ _).mpr
        (((ancestor_agrees _ _ _).mp hx).tail ((Backend.Alloy.Structural.subtype_inventory v.core d c).mp hc)))

-- [proof->req~compiler-behavioral-correctness~1]
/-- Source identity validity discharges every emitted trace-wide identity fact. -/
theorem identityFacts_complete (rep : TraceRep v source target) (w : Nat)
    (valid : (trace source).identities.Valid (SemanticsBridge.Structural.interpret v.core)) :
    ∀ fact ∈ identityFacts v, fact.Holds (schema v) w target.unfold [] 0 := by
  intro fact hf
  simp only [identityFacts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl) | hf
  · exact Relations.unary_one_of_singleton (rep.root_meaning w [] 0)
  · apply (Relations.unary_equal rep.label_injective
      (Relations.unary_image rep.label_injective (root_term v) (.field 0)
        (rep.root_meaning w [] 0) (rep.parent_meaning w [] 0)) Relations.unary_empty).mpr
    ext x
    have hroot : source.identities.parent[source.identities.root] = none := valid.root_parent
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      Set.mem_singleton_iff, exists_eq_left]
    change ¬ source.identities.parent[source.identities.root] = some x
    rw [hroot]
    simp
  · rw [all_unary (.mult _ _) (Relations.unary_diff rep.label_injective (.sig 0) (root_term v)
      (rep.objects_meaning w [] 0) (rep.root_meaning w [] 0))]
    intro x hx
    obtain ⟨p, hparent⟩ := valid.parent_exists x hx.2
    have hi := Relations.unary_image rep.label_injective (.var 0) (.field 0)
      (Relations.unary_singleton (f := rep.label) x)
      (rep.parent_meaning w [.object (rep.label x)] 0)
    have he : {y | ∃ z ∈ ({x} : Set (Fin o)), source.identities.parent[z] = some y} = {p} := by
      ext y
      change (∃ z, z = x ∧ source.identities.parent[z] = some y) ↔ y = p
      simp [show source.identities.parent[x] = some p from hparent, eq_comm]
    rw [he] at hi
    exact Relations.unary_one_of_singleton hi
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hf
    cases ha : (v.core.get d).isAbstract with
    | true =>
      simp only [ha, ↓reduceIte, List.mem_singleton] at hd
      subst fact
      exact rep.abstract_pool_complete w d ha valid.concrete
    | false =>
      cases hp : (v.core.get d).parent with
      | none => simp [ha, hp] at hd
      | some p =>
        simp only [ha, Bool.false_eq_true, ↓reduceIte, hp, List.mem_singleton] at hd
        subst fact
        rw [all_unary (.subset _ _) (rep.directPool_meaning w [] 0 d)]
        intro x hx
        apply (Relations.unary_subset rep.label_injective
          (Relations.unary_image rep.label_injective (.var 0) (.field 0)
            (Relations.unary_singleton (f := rep.label) x)
            (rep.parent_meaning w [.object (rep.label x)] 0))
          (rep.pool_meaning w [.object (rep.label x)] 0 p)).mpr
        rintro y ⟨z, hz, hparent⟩
        have hz' : z = x := hz
        subst z
        obtain ⟨c, hc, htype⟩ := valid.parent_typed x y hparent
        have hc' : (v.core.get d).parent = some c := by
          change (v.core.get source.identities.directType[x]).parent = some c at hc
          change source.identities.directType[x] = d at hx
          simpa only [hx] using hc
        have he : c = p := Option.some.inj (hc'.symm.trans hp)
        subst c
        exact (ancestor_agrees _ _ _).mpr htype

end TraceRep
end ClaferCompiler.Correctness.Behavioral
