module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionAggregates
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Forall2

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Occurrences
open scoped BigOperators
open Clafer.Behavioral.Aggregate

universe u
variable {U : Type u}

/-- Standard list indexing supplies occurrence identities. Equal objects in
different source domains retain different indices. -/
def indexedFrom (start : Nat) (lists : List (List U)) : List (Nat × U) :=
  (lists.zipIdx start).flatMap fun (xs, i) => xs.map (i, ·)

@[simp] theorem indexedFrom_nil (start : Nat) : indexedFrom start ([] : List (List U)) = [] := rfl

@[simp] theorem indexedFrom_cons (start : Nat) (xs : List U) (lists : List (List U)) :
    indexedFrom start (xs :: lists) = xs.map (start, ·) ++ indexedFrom (start + 1) lists := by
  simp only [indexedFrom, List.zipIdx_cons, List.flatMap_cons]

theorem indexedFrom_snd (start : Nat) (lists : List (List U)) :
    (indexedFrom start lists).map Prod.snd = lists.flatten := by
  induction lists generalizing start with
  | nil => rfl
  | cons xs lists ih => simp [ih, List.map_map]

theorem indexedFrom_lower {start : Nat} {lists : List (List U)} {ix : Nat × U}
    (member : ix ∈ indexedFrom start lists) : start ≤ ix.1 := by
  obtain ⟨⟨xs, i⟩, hi, member⟩ := List.mem_flatMap.mp member
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
  exact List.le_snd_of_mem_zipIdx hi

theorem indexedFrom_nodup (start : Nat) (lists : List (List U))
    (distinct : ∀ xs ∈ lists, xs.Nodup) : (indexedFrom start lists).Nodup := by
  induction lists generalizing start with
  | nil => exact List.nodup_nil
  | cons xs lists ih =>
    rw [indexedFrom_cons, List.nodup_append]
    refine ⟨(distinct xs List.mem_cons_self).map (fun _ _ he => congrArg Prod.snd he),
      ih _ (fun ys hy => distinct ys (List.mem_cons_of_mem _ hy)), ?_⟩
    intro ix left jx right equal
    subst jx
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp left
    have lower := indexedFrom_lower right
    simp only at lower
    omega

theorem indexedFrom_zero_member (lists : List (List U)) (i : Nat) (x : U) :
    (i, x) ∈ indexedFrom 0 lists ↔ ∃ hi : i < lists.length, x ∈ lists[i] := by
  constructor
  · intro member
    obtain ⟨⟨xs, j⟩, hj, member⟩ := List.mem_flatMap.mp member
    obtain ⟨y, hy, eq⟩ := List.mem_map.mp member
    have ji : j = i := congrArg Prod.fst eq
    have yx : y = x := congrArg Prod.snd eq
    subst j
    subst y
    obtain ⟨hi, eq⟩ := List.mem_zipIdx' hj
    exact ⟨hi, eq ▸ hy⟩
  · rintro ⟨hi, hx⟩
    apply List.mem_flatMap.mpr
    refine ⟨(lists[i], i), (List.mk_mem_zipIdx_iff_getElem?).mpr (List.getElem?_eq_getElem hi), ?_⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

def indexEmbedding (sets : List (Set U)) : Fin sets.length × U ↪ Nat × U where
  toFun ix := (ix.1.val, ix.2)
  inj' := by
    intro x y eq
    exact Prod.ext (Fin.ext (congrArg Prod.fst eq)) (congrArg (fun z : Nat × U => z.2) eq)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem occurrences_indexed {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists) :
    indexEmbedding sets '' Clafer.Behavioral.PrimitiveExpression.occurrences sets =
      {ix | ix ∈ indexedFrom 0 lists} := by
  ext ix
  rcases ix with ⟨i, x⟩
  rw [Set.mem_ofPred_eq, indexedFrom_zero_member]
  constructor
  · rintro ⟨⟨j, y⟩, hy, eq⟩
    have ji : j.val = i := congrArg Prod.fst eq
    have yx : y = x := congrArg Prod.snd eq
    subst i
    subst y
    refine ⟨by simpa only [← represented.length_eq] using j.isLt, ?_⟩
    exact ((represented.get j.isLt (by simpa only [← represented.length_eq] using j.isLt)).2 x).mpr hy
  · rintro ⟨hi, hx⟩
    have hs : i < sets.length := by simpa only [represented.length_eq] using hi
    refine ⟨(⟨i, hs⟩, x), ?_, rfl⟩
    exact ((represented.get hs hi).2 x).mp hx

theorem represented_nodup {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists) :
    (indexedFrom 0 lists).Nodup := by
  apply indexedFrom_nodup
  intro xs member
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp member
  rw [← eq]
  exact (represented.get (by simpa only [represented.length_eq] using hi) hi).1

theorem occurrences_length {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists) :
    (Clafer.Behavioral.PrimitiveExpression.occurrences sets).ncard = lists.flatten.length := by
  classical
  rw [← Set.ncard_image_of_injective _ (indexEmbedding sets).injective, occurrences_indexed represented]
  have setEq : {ix | ix ∈ indexedFrom 0 lists} = ((indexedFrom 0 lists).toFinset : Set (Nat × U)) := by
    ext; simp
  rw [setEq, Set.ncard_coe_finset, List.toFinset_card_of_nodup (represented_nodup represented)]
  simpa only [List.length_map] using congrArg List.length (indexedFrom_snd 0 lists)

theorem fold_list (op : Fold) (xs : List U) (distinct : xs.Nodup) (body : U → Option Int) :
    op.eval {x | x ∈ xs} body =
      if ∀ x ∈ xs, (body x).isSome then
        some (match op with
          | .sum => (xs.map fun x => (body x).getD 0).sum
          | .product => (xs.map fun x => (body x).getD 0).prod)
      else none := by
  classical
  have finite : ({x | x ∈ xs} : Set U).Finite := xs.finite_toSet
  by_cases defined : ∀ x ∈ xs, (body x).isSome
  · rw [ite_eq_left defined, Clafer.Behavioral.Aggregate.fold_finite op finite body defined]
    have finset : finite.toFinset = xs.toFinset := by ext; simp
    rw [finset]
    cases op with
    | sum => rw [List.sum_toFinset _ distinct]
    | product => rw [List.prod_toFinset _ distinct]
  · rw [ite_eq_right defined]
    push Not at defined
    obtain ⟨x, hx, bad⟩ := defined
    apply Clafer.Behavioral.Aggregate.fold_missing op body hx
    cases eq : body x with
    | none => rfl
    | some value => simp [eq] at bad

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem fold_occurrences {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists)
    (op : Fold) (body : U → Option Int) :
    op.eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets) (fun ix => body ix.2) =
      if ∀ x ∈ lists.flatten, (body x).isSome then
        some (match op with
          | .sum => (lists.flatten.map fun x => (body x).getD 0).sum
          | .product => (lists.flatten.map fun x => (body x).getD 0).prod)
      else none := by
  classical
  rw [← fold_image (indexEmbedding sets) op _ (fun ix => body ix.2) (fun ix => body ix.2) (fun _ _ => rfl),
    occurrences_indexed represented, fold_list op _ (represented_nodup represented)]
  have mapped : ((indexedFrom 0 lists).map fun ix => (body ix.2).getD 0) =
      lists.flatten.map (fun x => (body x).getD 0) := by
    rw [← indexedFrom_snd 0 lists, List.map_map]
    rfl
  have defined : (∀ ix ∈ indexedFrom 0 lists, (body ix.2).isSome) ↔
      ∀ x ∈ lists.flatten, (body x).isSome := by
    rw [← indexedFrom_snd 0 lists, List.forall_mem_map]
  simp only [defined, mapped]

theorem values_observed {xs : List U} {values : List Int} {body : U → Option Int}
    (observed : List.Forall₂ (fun x z => body x = some z) xs values) :
    (∀ x ∈ xs, (body x).isSome) ∧ xs.map (fun x => (body x).getD 0) = values := by
  induction observed with
  | nil => exact ⟨by simp, rfl⟩
  | cons head tail ih =>
    refine ⟨?_, ?_⟩
    · intro x member
      rcases List.mem_cons.mp member with rfl | member
      · simp [head]
      · exact ih.1 x member
    · simp only [List.map_cons, head, Option.getD_some, ih.2]

theorem fold_occurrences_defined {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists)
    (op : Fold) (body : U → Option Int) {values : List Int}
    (observed : List.Forall₂ (fun x z => body x = some z) lists.flatten values) :
    op.eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets) (fun ix => body ix.2) =
      some (match op with | .sum => values.sum | .product => values.prod) := by
  obtain ⟨defined, values⟩ := values_observed observed
  rw [fold_occurrences represented op body, ite_eq_left defined, values]

theorem fold_occurrences_missing {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists)
    (op : Fold) (body : U → Option Int) {x : U}
    (member : x ∈ lists.flatten) (missing : body x = none) :
    op.eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets) (fun ix => body ix.2) = none := by
  rw [fold_occurrences represented op body, ite_eq_right]
  intro defined
  have hx := defined x member
  simp [missing] at hx

end ClaferCompiler.Correctness.Behavioral.Full.Occurrences
