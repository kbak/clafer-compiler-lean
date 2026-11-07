module

public import ClaferCompiler.Backend.Alloy.Behavioral.Expressions
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics
public import ClaferCompiler.SemanticsBridge.Behavioral.Trace

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Temporal

deriving instance ReflBEq, LawfulBEq for Atom

-- [proof->req~compiler-behavioral-correctness~1]
/-- The static backend's stack-safety construction witness, extended by the
ordinary temporal relation constructors. This states shape, not denotation. -/
inductive Rel.Term : Rel → Prop where
  | empty (a) : Term (.empty a)
  | sig (i) : Term (.sig i)
  | field (i) : Term (.field i)
  | var (i) : Term (.var i)
  | univ : Term .univ
  | iden : Term .iden
  | ints : Term .ints
  | integer (n) : Term (.integer n)
  | values (owner) : Term (.values owner)
  | union : Term a → Term b → Term (.union a b)
  | inter : Term a → Term b → Term (.inter a b)
  | diff : Term a → Term b → Term (.diff a b)
  | product : Term a → Term b → Term (.product a b)
  | join : Term a → Term b → Term (.join a b)
  | transpose : Term a → Term (.transpose a)
  | prime : Term a → Term (.prime a)

theorem Rel.Term.stack (h : Rel.Term r) (alg : RelAlgebra α) :
    ∃ x, ∀ stack, r.code.foldl alg.step (some stack) = some (x :: stack) := by
  induction h with
  | empty a => exact ⟨alg.empty a, fun _ => rfl⟩
  | sig i => exact ⟨alg.sig i, fun _ => rfl⟩
  | field i => exact ⟨alg.field i, fun _ => rfl⟩
  | var i => exact ⟨alg.var i, fun _ => rfl⟩
  | univ => exact ⟨alg.univ, fun _ => rfl⟩
  | iden => exact ⟨alg.iden, fun _ => rfl⟩
  | ints => exact ⟨alg.ints, fun _ => rfl⟩
  | integer n => exact ⟨alg.integer n, fun _ => rfl⟩
  | values owner => exact ⟨alg.values owner, fun _ => rfl⟩
  | union ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.union a b, fun _ => by simp [Rel.union, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | inter ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.inter a b, fun _ => by simp [Rel.inter, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | diff ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.diff a b, fun _ => by simp [Rel.diff, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | product ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.product a b, fun _ => by simp [Rel.product, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | join ha hb ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨alg.join a b, fun _ => by simp [Rel.join, List.foldl_append, ha, hb, RelAlgebra.step]⟩
  | transpose ha ia =>
    obtain ⟨a, ha⟩ := ia
    exact ⟨alg.transpose a, fun _ => by simp [Rel.transpose, List.foldl_append, ha, RelAlgebra.step]⟩
  | prime ha ia =>
    obtain ⟨a, ha⟩ := ia
    exact ⟨alg.prime a, fun _ => by simp [Rel.prime, List.foldl_append, ha, RelAlgebra.step]⟩

theorem Rel.Term.run (h : Rel.Term r) (alg : RelAlgebra α) (fallback : α) (stack : List α) :
    r.code.foldl alg.step (some stack) = some (r.fold alg fallback :: stack) := by
  obtain ⟨x, hx⟩ := h.stack alg
  simp [Rel.fold, hx]

theorem Rel.fold_union (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.union b).fold alg z = alg.union (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.union, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_inter (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.inter b).fold alg z = alg.inter (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.inter, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_diff (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.diff b).fold alg z = alg.diff (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.diff, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_product (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.product b).fold alg z = alg.product (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.product, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_join (ha : Rel.Term a) (hb : Rel.Term b) (alg : RelAlgebra α) (z : α) :
    (a.join b).fold alg z = alg.join (a.fold alg z) (b.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.join, List.foldl_append, ha.run alg z, hb.run alg z]
  rfl

theorem Rel.fold_transpose (ha : Rel.Term a) (alg : RelAlgebra α) (z : α) :
    (a.transpose).fold alg z = alg.transpose (a.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.transpose, List.foldl_append, ha.run alg z]
  rfl

theorem Rel.fold_prime (ha : Rel.Term a) (alg : RelAlgebra α) (z : α) :
    (a.prime).fold alg z = alg.prime (a.fold alg z) := by
  unfold Rel.fold
  simp only [Rel.prime, List.foldl_append, ha.run alg z]
  rfl


variable {a b : Rel}

@[simp] theorem Rel.eval_union (ha : a.Term) (hb : b.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (a.union b).eval s w τ e t = (a.eval s w τ e t ++ b.eval s w τ e t).eraseDups := by
  simp only [Rel.eval, Rel.fold_union ha hb]
  rfl

@[simp] theorem Rel.eval_inter (ha : a.Term) (hb : b.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (a.inter b).eval s w τ e t = (a.eval s w τ e t).filter (b.eval s w τ e t).contains := by
  simp only [Rel.eval, Rel.fold_inter ha hb]
  rfl

@[simp] theorem Rel.eval_diff (ha : a.Term) (hb : b.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (a.diff b).eval s w τ e t = (a.eval s w τ e t).filter fun row => !(b.eval s w τ e t).contains row := by
  simp only [Rel.eval, Rel.fold_diff ha hb]
  rfl

@[simp] theorem Rel.eval_product (ha : a.Term) (hb : b.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (a.product b).eval s w τ e t = ((a.eval s w τ e t).flatMap fun x => (b.eval s w τ e t).map (x ++ ·)).eraseDups := by
  simp only [Rel.eval, Rel.fold_product ha hb]
  rfl

@[simp] theorem Rel.eval_join (ha : a.Term) (hb : b.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    (a.join b).eval s w τ e t = ((a.eval s w τ e t).flatMap fun x => ((b.eval s w τ e t).filter fun y => x.getLast? == y.head?).map fun y => x.dropLast ++ y.drop 1).eraseDups := by
  simp only [Rel.eval, Rel.fold_join ha hb]
  rfl

@[simp] theorem Rel.eval_transpose (ha : a.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    a.transpose.eval s w τ e t = ((a.eval s w τ e t).map List.reverse).eraseDups := by
  simp only [Rel.eval, Rel.fold_transpose ha]
  rfl

@[simp] theorem Rel.eval_prime (ha : a.Term) (s : Schema) (w : Nat)
    (τ : Trace) (e : Environment) (t : Nat) :
    a.prime.eval s w τ e t = a.eval s w τ e (t + 1) := by
  simp only [Rel.eval, Rel.fold_prime ha]
  rfl

theorem Formula.fold_all (alg : FormulaAlgebra α) (z : α) (r : Rel)
    (hp : p.Built) : (Formula.all r p).fold alg z = alg.all r (p.fold alg z) := by
  obtain ⟨x, hx⟩ := hp.stack alg
  simp [Formula.fold, Formula.all, List.foldl_append, hx, FormulaAlgebra.step]

theorem Formula.fold_exists (alg : FormulaAlgebra α) (z : α) (r : Rel)
    (hp : p.Built) : (Formula.exists_ r p).fold alg z = alg.exists_ r (p.fold alg z) := by
  obtain ⟨x, hx⟩ := hp.stack alg
  simp [Formula.fold, Formula.exists_, List.foldl_append, hx, FormulaAlgebra.step]

end ClaferCompiler.Backend.Alloy.Temporal

namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral


@[simp] theorem shift_empty (n : Nat) (a : Backend.Alloy.Arity) :
    shift n (Rel.empty a) = Rel.empty a := rfl

@[simp] theorem shift_sig (n : Nat) (i : Nat) :
    shift n (Rel.sig i) = Rel.sig i := rfl

@[simp] theorem shift_field (n : Nat) (i : Nat) :
    shift n (Rel.field i) = Rel.field i := rfl

@[simp] theorem shift_var (n : Nat) (i : Nat) :
    shift n (Rel.var i) = Rel.var (i + n) := rfl

@[simp] theorem shift_univ (n : Nat) : shift n Rel.univ = Rel.univ := rfl

@[simp] theorem shift_iden (n : Nat) : shift n Rel.iden = Rel.iden := rfl

@[simp] theorem shift_ints (n : Nat) : shift n Rel.ints = Rel.ints := rfl

@[simp] theorem shift_union (n : Nat) (a b : Rel) :
    shift n (a.union b) = (shift n a).union (shift n b) := by
  simp [shift, Rel.union]

@[simp] theorem shift_inter (n : Nat) (a b : Rel) :
    shift n (a.inter b) = (shift n a).inter (shift n b) := by
  simp [shift, Rel.inter]

@[simp] theorem shift_diff (n : Nat) (a b : Rel) :
    shift n (a.diff b) = (shift n a).diff (shift n b) := by
  simp [shift, Rel.diff]

@[simp] theorem shift_product (n : Nat) (a b : Rel) :
    shift n (a.product b) = (shift n a).product (shift n b) := by
  simp [shift, Rel.product]

@[simp] theorem shift_join (n : Nat) (a b : Rel) :
    shift n (a.join b) = (shift n a).join (shift n b) := by
  simp [shift, Rel.join]

@[simp] theorem shift_transpose (n : Nat) (a : Rel) :
    shift n a.transpose = (shift n a).transpose := by simp [shift, Rel.transpose]

@[simp] theorem shift_prime (n : Nat) (a : Rel) :
    shift n a.prime = (shift n a).prime := by simp [shift, Rel.prime]

@[simp] theorem shift_integer (n : Nat) (i : Int) : shift n (.integer i) = .integer i := rfl
@[simp] theorem shift_values (n owner : Nat) : shift n (.values owner) = .values owner := rfl

theorem shift_term (h : Rel.Term r) (n : Nat) : (shift n r).Term := by
  induction h <;> simp only [shift_empty, shift_sig, shift_field, shift_var,
    shift_univ, shift_iden, shift_ints, shift_integer, shift_values, shift_union, shift_inter, shift_diff,
    shift_product, shift_join, shift_transpose, shift_prime] <;> constructor <;> assumption

theorem shift_eval (h : Rel.Term r) (s : Schema) (w : Nat) (τ : Trace)
    (pre e : Environment) (t : Nat) :
    (shift pre.length r).eval s w τ (pre ++ e) t = r.eval s w τ e t := by
  induction h generalizing t with
  | empty a => rfl
  | sig i => rfl
  | field i => rfl
  | var i =>
    change ((pre ++ e)[i + pre.length]?).toList.map (fun x => [x]) =
      (e[i]?).toList.map (fun x => [x])
    rw [List.getElem?_append_right (by omega)]
    simp
  | univ => rfl
  | iden => rfl
  | ints => rfl
  | integer _ => rfl
  | values _ => rfl
  | union ha hb ia ib => simp only [shift_union, Rel.eval_union (shift_term ha _) (shift_term hb _), Rel.eval_union ha hb, ia, ib]
  | inter ha hb ia ib => simp only [shift_inter, Rel.eval_inter (shift_term ha _) (shift_term hb _), Rel.eval_inter ha hb, ia, ib]
  | diff ha hb ia ib => simp only [shift_diff, Rel.eval_diff (shift_term ha _) (shift_term hb _), Rel.eval_diff ha hb, ia, ib]
  | product ha hb ia ib => simp only [shift_product, Rel.eval_product (shift_term ha _) (shift_term hb _), Rel.eval_product ha hb, ia, ib]
  | join ha hb ia ib => simp only [shift_join, Rel.eval_join (shift_term ha _) (shift_term hb _), Rel.eval_join ha hb, ia, ib]
  | transpose ha ia => simp only [shift_transpose, Rel.eval_transpose (shift_term ha _), Rel.eval_transpose ha, ia]
  | prime ha ia => simp only [shift_prime, Rel.eval_prime (shift_term ha _), Rel.eval_prime ha, ia]

namespace Relations

/-- Exact row equations exclude integer atoms, malformed tuples and junk IDs. -/
def Unary (f : U → Nat) (S : Set U) (r : Relation) : Prop :=
  ∀ row, row ∈ r ↔ ∃ x ∈ S, row = [Atom.object (f x)]

def Binary (f : U → Nat) (R : U → U → Prop) (r : Relation) : Prop :=
  ∀ row, row ∈ r ↔ ∃ x y, R x y ∧ row = [Atom.object (f x), Atom.object (f y)]

variable {U : Type} {f : U → Nat} {A B : Set U} {R : U → U → Prop}
  {a b : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

 theorem unary_singleton (x : U) : Unary f {x} [[.object (f x)]] := by
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
    exact ⟨[.object (f x)], (hA _).mpr ⟨x, hx, rfl⟩,
      [.object (f x), .object (f z)], ⟨(hR _).mpr ⟨x, z, hxz, rfl⟩, by simp⟩, by simp⟩

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

theorem unary_some (hA : Unary f A (a.eval s w τ e t)) :
    (Formula.mult .some a).Holds s w τ e t ↔ A.Nonempty := by
  change (decide (0 < (a.eval s w τ e t).eraseDups.length) = true) ↔ _
  rw [decide_eq_true_eq, List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨row, hr⟩
    obtain ⟨x, hx, _⟩ := (hA row).mp (List.mem_eraseDups.mp hr)
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨[.object (f x)], List.mem_eraseDups.mpr ((hA _).mpr ⟨x, hx, rfl⟩)⟩

end Relations
end ClaferCompiler.Correctness.Behavioral
