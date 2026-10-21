module

public import ClaferCompiler.Correctness.StructuralRelations
public import ClaferCompiler.SemanticsBridge.ExprFinite

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionRelations
open Backend.Alloy
open Clafer.Constraints (relationalImage relationalJoin)

/-- Exact tuple equations, including absence of junk tuples. No truth or compiler
correctness assumption is part of the representation relation. -/
def Unary (f : U → Nat) (S : Set U) (r : Relation) : Prop :=
  ∀ t, t ∈ r ↔ ∃ x ∈ S, t = [f x]

def Binary (f : U → Nat) (S : Set (U × U)) (r : Relation) : Prop :=
  ∀ t, t ∈ r ↔ ∃ x y, (x, y) ∈ S ∧ t = [f x, f y]

variable {U : Type} {f : U → Nat} {A B : Set U} {R T : Set (U × U)}
  {a b : Rel} {i : Instance} {env : List Nat}

theorem unary_singleton (x : U) : Unary f {x} [[f x]] := by
  intro t
  simp [eq_comm]

theorem unary_union (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval i env)) (hB : Unary f B (b.eval i env)) :
    Unary f (A ∪ B) ((a.union b).eval i env) := by
  dsimp only [Unary] at hA hB
  intro t
  rw [Rel.eval_union ha hb]
  simp only [List.mem_eraseDups, List.mem_append, hA, hB, Set.mem_union]
  aesop

theorem unary_inter (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval i env)) (hB : Unary f B (b.eval i env)) :
    Unary f (A ∩ B) ((a.inter b).eval i env) := by
  dsimp only [Unary] at hA hB
  intro t
  simp only [Rel.eval, Rel.fold_inter_term ha hb]
  change t ∈ (a.eval i env).filter (b.eval i env).contains ↔ _
  simp only [List.mem_filter, List.contains_iff_mem, hA, hB, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, y, hy, he⟩
    have : x = y := hf (by simpa using he)
    subst y
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, x, hy, rfl⟩

theorem unary_diff (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval i env)) (hB : Unary f B (b.eval i env)) :
    Unary f (A \ B) ((a.diff b).eval i env) := by
  dsimp only [Unary] at hA hB
  intro t
  simp only [Rel.eval, Rel.fold_diff_term ha hb]
  change t ∈ (a.eval i env).filter (fun t => !(b.eval i env).contains t) ↔ _
  constructor
  · intro h
    obtain ⟨hm, hn⟩ := List.mem_filter.mp h
    obtain ⟨x, hx, rfl⟩ := (hA t).mp hm
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hxB
    have hmem := List.contains_iff_mem.mpr ((hB _).mpr ⟨x, hxB, rfl⟩)
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hn
    exact hn (List.contains_iff_mem.mp hmem)
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨(hA _).mpr ⟨x, hx, rfl⟩, ?_⟩
    have hnot : [f x] ∉ b.eval i env := by
      intro hmem
      obtain ⟨y, hy, he⟩ := (hB _).mp hmem
      exact hn ((hf (by simpa using he)) ▸ hy)
    simpa using hnot

theorem unary_image (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval i env)) (hR : Binary f R (b.eval i env)) :
    Unary f (relationalImage A R) ((a.join b).eval i env) := by
  intro t
  rw [Rel.eval_join ha hb]
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨left, hl, right, ⟨hr, hj⟩, ht⟩
    obtain ⟨x, hx, rfl⟩ := (hA left).mp hl
    obtain ⟨y, z, hyz, rfl⟩ := (hR right).mp hr
    have he : x = y := hf (by simpa using hj)
    subst y
    exact ⟨z, ⟨x, hx, hyz⟩, by simpa using ht.symm⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨[f x], (hA _).mpr ⟨x, hx, rfl⟩,
      [f x, f z], ⟨(hR _).mpr ⟨x, z, hxz, rfl⟩, by simp⟩, by simp⟩

theorem binary_join (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hR : Binary f R (a.eval i env)) (hT : Binary f T (b.eval i env)) :
    Binary f (relationalJoin R T) ((a.join b).eval i env) := by
  intro t
  rw [Rel.eval_join ha hb]
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨left, hl, right, ⟨hr, hj⟩, ht⟩
    obtain ⟨x, y, hxy, rfl⟩ := (hR left).mp hl
    obtain ⟨z, w, hzw, rfl⟩ := (hT right).mp hr
    have he : y = z := hf (by simpa using hj)
    subst z
    exact ⟨x, w, ⟨y, hxy, hzw⟩, by simpa using ht.symm⟩
  · rintro ⟨x, z, ⟨y, hxy, hyz⟩, rfl⟩
    exact ⟨[f x, f y], (hR _).mpr ⟨x, y, hxy, rfl⟩,
      [f y, f z], ⟨(hT _).mpr ⟨y, z, hyz, rfl⟩, by simp⟩, by simp⟩

/-- Generic finite-set facts reused for both unary and binary tuple encodings. -/
def Represents (encode : V → Tuple) (S : Set V) (r : Relation) : Prop :=
  ∀ t, t ∈ r ↔ ∃ x ∈ S, t = encode x

theorem represents_union {V : Type} {g : V → Tuple} {S T : Set V}
    (ha : a.Term) (hb : b.Term)
    (hr : Represents g S (a.eval i env)) (hq : Represents g T (b.eval i env)) :
    Represents g (S ∪ T) ((a.union b).eval i env) := by
  dsimp only [Represents] at hr hq
  intro t
  rw [Rel.eval_union ha hb]
  simp only [List.mem_eraseDups, List.mem_append, hr, hq, Set.mem_union]
  aesop

theorem represents_inter {V : Type} {g : V → Tuple} (hg : Function.Injective g)
    {S T : Set V} (ha : a.Term) (hb : b.Term)
    (hr : Represents g S (a.eval i env)) (hq : Represents g T (b.eval i env)) :
    Represents g (S ∩ T) ((a.inter b).eval i env) := by
  dsimp only [Represents] at hr hq
  intro t
  simp only [Rel.eval, Rel.fold_inter_term ha hb]
  change t ∈ (a.eval i env).filter (b.eval i env).contains ↔ _
  simp only [List.mem_filter, List.contains_iff_mem, hr, hq, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, y, hy, he⟩
    have : x = y := hg he
    subst y
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, x, hy, rfl⟩

theorem represents_diff {V : Type} {g : V → Tuple} (hg : Function.Injective g)
    {S T : Set V} (ha : a.Term) (hb : b.Term)
    (hr : Represents g S (a.eval i env)) (hq : Represents g T (b.eval i env)) :
    Represents g (S \ T) ((a.diff b).eval i env) := by
  dsimp only [Represents] at hr hq
  intro t
  simp only [Rel.eval, Rel.fold_diff_term ha hb]
  change t ∈ (a.eval i env).filter (fun t => !(b.eval i env).contains t) ↔ _
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, hr, hq, Set.mem_sdiff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun ht => hn ⟨x, ht, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    exact hn ((hg he) ▸ hy)

theorem represented_singleton {V : Type} {g : V → Tuple} {x : V} {r : Relation}
    (hr : Represents g {x} r) : r.eraseDups = [g x] := by
  have hm : ∀ t, t ∈ r.eraseDups ↔ t = g x := by
    intro t
    simpa only [List.mem_eraseDups, Set.mem_singleton_iff, exists_eq_left] using hr t
  have hn := ClaferCompiler.Correctness.Structural.eraseDups_nodup r
  cases he : r.eraseDups with
  | nil => have := (hm (g x)).mpr rfl; simp [he] at this
  | cons t ts =>
    have ht : t = g x := (hm t).mp (by simp [he])
    have hts : ts = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      have hyx := (hm y).mp (by simp [he, hy])
      simp only [he, List.nodup_cons] at hn
      exact hn.1 (ht.symm ▸ hyx ▸ hy)
    simp [ht, hts]

theorem represented_subset {V : Type} {g : V → Tuple} (hg : Function.Injective g)
    {S T : Set V} {r q : Relation} (hr : Represents g S r) (hq : Represents g T q) :
    relationSubset r q = true ↔ S ⊆ T := by
  simp only [relationSubset, List.all_eq_true, List.contains_iff_mem]
  constructor
  · intro h x hx
    obtain ⟨y, hy, he⟩ := (hq _).mp (h (g x) ((hr _).mpr ⟨x, hx, rfl⟩))
    exact (hg he) ▸ hy
  · intro h t ht
    obtain ⟨x, hx, rfl⟩ := (hr t).mp ht
    exact (hq _).mpr ⟨x, h hx, rfl⟩

theorem represented_equal {V : Type} {g : V → Tuple} (hg : Function.Injective g)
    {S T : Set V} {r q : Relation} (hr : Represents g S r) (hq : Represents g T q) :
    (relationSubset r q && relationSubset q r) = true ↔ S = T := by
  rw [Bool.and_eq_true, represented_subset hg hr hq, represented_subset hg hq hr]
  exact Set.Subset.antisymm_iff.symm

theorem represented_card {V : Type} {g : V → Tuple} (hg : Function.Injective g)
    {S : Set V} {r : Relation} (hr : Represents g S r) :
    r.eraseDups.length = S.ncard := by
  classical
  have he : (r.toFinset : Set Tuple) = g '' S := by
    ext t
    simp only [Finset.mem_coe, List.mem_toFinset, Set.mem_image]
    exact (hr t).trans (by simp only [eq_comm])
  rw [ClaferCompiler.Correctness.Structural.eraseDups_card, ← Set.ncard_coe_finset, he]
  exact Set.ncard_image_of_injective S hg

theorem unary_rep {r : Relation} (h : Unary f A r) : Represents (fun x => [f x]) A r := h

theorem binary_rep {r : Relation} (h : Binary f R r) :
    Represents (fun x : U × U => [f x.1, f x.2]) R r := by
  intro t
  simpa only [Prod.exists] using h t

theorem unary_injective (hf : Function.Injective f) : Function.Injective (fun x => [f x]) := by
  intro x y h
  exact hf (by simpa using h)

theorem binary_injective (hf : Function.Injective f) :
    Function.Injective (fun x : U × U => [f x.1, f x.2]) := by
  intro x y h
  have h' : f x.1 = f y.1 ∧ f x.2 = f y.2 := by simpa using h
  exact Prod.ext (hf h'.1) (hf h'.2)

end ClaferCompiler.Correctness.ExpressionRelations
