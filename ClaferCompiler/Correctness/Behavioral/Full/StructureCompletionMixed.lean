module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletion
public import ClaferCompiler.Correctness.Behavioral.Full.StructureReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace Mixed
variable {U : Type} {f : U → Atom} {A : Set U} {R S : U → U → Prop}
  {a b : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

theorem binary_subset (hf : Function.Injective f)
    (hr : Binary f R (a.eval s w τ e t)) (hs : Binary f S (b.eval s w τ e t)) :
    (Formula.subset a b).Holds s w τ e t ↔ ∀ x y, R x y → S x y := by
  constructor
  · intro h x y r
    obtain ⟨z, q, hsq, he⟩ := (hs _).mp (h _ ((hr _).mpr ⟨x, y, r, rfl⟩))
    have hz : x = z := hf (List.cons.inj he).1
    have hq : y = q := hf (List.cons.inj (List.cons.inj he).2).1
    exact hz ▸ hq ▸ hsq
  · intro h row hm
    obtain ⟨x, y, hr, he⟩ := (hr _).mp hm
    exact (hs _).mpr ⟨x, y, h x y hr, he⟩

theorem all_unary_complete (built : body.Built) (h : Unary f A (a.eval s w τ e t)) :
    (Formula.all a body).Holds s w τ e t ↔ ∀ x ∈ A, body.Holds s w τ (f x :: e) t := by
  rw [Encoding.holds_all built]
  constructor
  · intro hp x hx
    exact hp (f x) ((h _).mpr ⟨x, hx, rfl⟩)
  · intro hp atom ha
    obtain ⟨x, hx, he⟩ := (h _).mp ha
    have eq := List.singleton_inj.mp he
    exact eq ▸ hp x hx

theorem unary_singleton_card {x : U} {r : Relation}
    (h : Unary f {x} r) : r.eraseDups = [[f x]] := by
  have hm : ∀ row, row ∈ r.eraseDups ↔ row = [f x] := by
    intro row
    simpa only [List.mem_eraseDups, Set.mem_singleton_iff, exists_eq_left] using h row
  have hn := Structural.eraseDups_nodup r
  cases he : r.eraseDups with
  | nil => have := (hm [f x]).mpr rfl; simp [he] at this
  | cons row rows =>
    have hr : row = [f x] := (hm row).mp (by simp [he])
    have hrs : rows = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      have hyx := (hm y).mp (by simp [he, hy])
      simp only [he, List.nodup_cons] at hn
      exact hn.1 (hr.symm ▸ hyx ▸ hy)
    simp [hr, hrs]

theorem unary_one_of_singleton {x : U} (h : Unary f {x} (a.eval s w τ e t)) :
    (Formula.mult .one a).Holds s w τ e t := by
  change ((_ : Relation).eraseDups.length == 1) = true
  rw [unary_singleton_card h]
  rfl

theorem unary_one_of_unique (h : Unary f A (a.eval s w τ e t)) (unique : ∃! x, x ∈ A) :
    (Formula.mult .one a).Holds s w τ e t := by
  obtain ⟨x, hx, one⟩ := unique
  apply unary_one_of_singleton (x := x)
  apply unary_congr h
  exact fun y => ⟨fun hy => one y hy, fun he => he ▸ hx⟩

theorem unary_lone (h : Unary f A (a.eval s w τ e t))
    (unique : ∀ x ∈ A, ∀ y ∈ A, x = y) : (Formula.mult .lone a).Holds s w τ e t := by
  by_cases nonempty : A.Nonempty
  · obtain ⟨x, hx⟩ := nonempty
    have singleton := unary_congr h (fun y =>
      show y ∈ A ↔ y ∈ ({x} : Set U) from ⟨fun hy => unique y hy x hx, fun he => he ▸ hx⟩)
    change decide (((_ : Relation).eraseDups.length) ≤ 1) = true
    rw [unary_singleton_card singleton]
    rfl
  · have empty : (a.eval s w τ e t).eraseDups = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row hm
      obtain ⟨x, hx, _⟩ := (h _).mp (List.mem_eraseDups.mp hm)
      exact nonempty ⟨x, hx⟩
    change decide (((_ : Relation).eraseDups.length) ≤ 1) = true
    rw [empty]
    rfl

end Mixed
end ClaferCompiler.Correctness.Behavioral.Full
