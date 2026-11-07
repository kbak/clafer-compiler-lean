module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureState
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionReferences
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionRestriction

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
/- The existing object relation proofs generalized only at their atom map.
This handles mixed object/integer rows without changing the target algebra. -/
namespace Mixed
/-- Exact mixed rows retain object identities and mathematical integer values. -/
def Unary (f : U → Atom) (S : Set U) (r : Relation) : Prop :=
  ∀ row, row ∈ r ↔ ∃ x ∈ S, row = [f x]

def Binary (f : U → Atom) (R : U → U → Prop) (r : Relation) : Prop :=
  ∀ row, row ∈ r ↔ ∃ x y, R x y ∧ row = [f x, f y]

variable {U : Type} {f : U → Atom} {A B : Set U} {R : U → U → Prop}
  {a b : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

 theorem unary_singleton (x : U) : Unary f {x} [[f x]] := by
  intro row
  simp [eq_comm]

theorem unary_empty : Unary f ∅ [] := by intro row; simp

theorem unary_union (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    Unary f (A ∪ B) ((a.union b).eval s w τ e t) := by
  dsimp only [Unary] at hA hB
  intro row
  simp only [Rel.eval, Rel.fold_union ha hb]
  change row ∈ (a.eval s w τ e t ++ b.eval s w τ e t).eraseDups ↔ _
  simp only [List.mem_eraseDups, List.mem_append, hA, hB, Set.mem_union]
  aesop

theorem unary_inter (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    Unary f (A ∩ B) ((a.inter b).eval s w τ e t) := by
  dsimp only [Unary] at hA hB
  intro row
  simp only [Rel.eval, Rel.fold_inter ha hb]
  change row ∈ (a.eval s w τ e t).filter (b.eval s w τ e t).contains ↔ _
  simp only [List.mem_filter, List.contains_iff_mem, hA, hB, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, y, hy, he⟩
    have : x = y := hf (by simpa using he)
    subst y
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, x, hy, rfl⟩

theorem unary_diff (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    Unary f (A \ B) ((a.diff b).eval s w τ e t) := by
  dsimp only [Unary] at hA hB
  intro row
  simp only [Rel.eval, Rel.fold_diff ha hb]
  change row ∈ (a.eval s w τ e t).filter (fun row => !(b.eval s w τ e t).contains row) ↔ _
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, hA, hB, Set.mem_sdiff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun ht => hn ⟨x, ht, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    exact hn ((hf (by simpa using he)) ▸ hy)

theorem unary_image (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hR : Binary f R (b.eval s w τ e t)) :
    Unary f {y | ∃ x ∈ A, R x y} ((a.join b).eval s w τ e t) := by
  intro row
  simp only [Rel.eval, Rel.fold_join ha hb]
  change row ∈ ((a.eval s w τ e t).flatMap fun x =>
    ((b.eval s w τ e t).filter fun y => x.getLast? == y.head?).map
      fun y => x.dropLast ++ y.drop 1).eraseDups ↔ _
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

theorem unary_subset (hf : Function.Injective f)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    (Formula.subset a b).Holds s w τ e t ↔ A ⊆ B := by
  change (∀ row, row ∈ a.eval s w τ e t → row ∈ b.eval s w τ e t) ↔ _
  constructor
  · intro h x hx
    obtain ⟨y, hy, he⟩ := (hB _).mp (h _ ((hA _).mpr ⟨x, hx, rfl⟩))
    exact (hf (by simpa using he)) ▸ hy
  · rintro h row hr
    obtain ⟨x, hx, rfl⟩ := (hA _).mp hr
    exact (hB _).mpr ⟨x, h hx, rfl⟩

theorem unary_equal (hf : Function.Injective f)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    (Formula.equal a b).Holds s w τ e t ↔ A = B := by
  change (∀ row, row ∈ a.eval s w τ e t ↔ row ∈ b.eval s w τ e t) ↔ _
  constructor
  · intro h
    apply Set.Subset.antisymm
    · exact (unary_subset hf hA hB).mp (fun row hr => (h row).mp hr)
    · exact (unary_subset hf hB hA).mp (fun row hr => (h row).mpr hr)
  · intro h row
    subst B
    exact (hA row).trans (hB row).symm


variable {S : U → U → Prop}
theorem binary_union (ha : a.Term) (hb : b.Term)
    (hR : Binary f R (a.eval s w τ e t)) (hS : Binary f S (b.eval s w τ e t)) :
    Binary f (fun x y => R x y ∨ S x y) ((a.union b).eval s w τ e t) := by
  intro row
  rw [Rel.eval_union ha hb]
  simp only [List.mem_eraseDups, List.mem_append, hR row, hS row]
  aesop

theorem binary_congr {r : Relation} (hr : Binary f R r) (he : ∀ x y, R x y ↔ S x y) :
    Binary f S r := by
  intro row
  rw [hr row]
  simp only [he]

theorem binary_product (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    Binary f (fun x y => x ∈ A ∧ y ∈ B) ((a.product b).eval s w τ e t) := by
  intro row
  rw [Rel.eval_product ha hb]
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨left, hl, right, hr, he⟩
    obtain ⟨x, hx, rfl⟩ := (hA left).mp hl
    obtain ⟨y, hy, rfl⟩ := (hB right).mp hr
    exact ⟨x, y, ⟨hx, hy⟩, he.symm⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨[f x], (hA _).mpr ⟨x, hx, rfl⟩,
      [f y], (hB _).mpr ⟨y, hy, rfl⟩, rfl⟩

theorem binary_inter (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hR : Binary f R (a.eval s w τ e t)) (hS : Binary f S (b.eval s w τ e t)) :
    Binary f (fun x y => R x y ∧ S x y) ((a.inter b).eval s w τ e t) := by
  intro row
  rw [Rel.eval_inter ha hb]
  simp only [List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨x, y, hxy, rfl⟩ := (hR _).mp hr
    obtain ⟨z, q, hs, he⟩ := (hS _).mp hs
    have hz : x = z := hf (by simpa using (List.cons.inj he).1)
    have hq : y = q := hf (by simpa using (List.cons.inj (List.cons.inj he).2).1)
    subst z q
    exact ⟨x, y, ⟨hxy, hs⟩, rfl⟩
  · rintro ⟨x, y, ⟨hr, hs⟩, rfl⟩
    exact ⟨(hR _).mpr ⟨x, y, hr, rfl⟩, (hS _).mpr ⟨x, y, hs, rfl⟩⟩

theorem binary_transpose (ha : a.Term)
    (hR : Binary f R (a.eval s w τ e t)) :
    Binary f (fun x y => R y x) (a.transpose.eval s w τ e t) := by
  intro row
  rw [Rel.eval_transpose ha]
  simp only [List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨source, hs, he⟩
    obtain ⟨x, y, hr, rfl⟩ := (hR _).mp hs
    exact ⟨y, x, hr, by simpa using he.symm⟩
  · rintro ⟨x, y, hr, rfl⟩
    exact ⟨[f y, f x], (hR _).mpr ⟨y, x, hr, rfl⟩, by simp⟩


end Mixed
end ClaferCompiler.Correctness.Behavioral.Full
