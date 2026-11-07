module

public import ClaferCompiler.Correctness.Behavioral.Full.RangesSets
public import ClaferCompiler.Correctness.Behavioral.Full.RangesFolds
public import Mathlib.Data.List.OfFn

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Ranges
open IR.Behavioral.Expression.Ranges
open scoped BigOperators

variable {U : Type} {R : Clafer.Constraints.IntegerRealization U}

theorem EnvironmentBound.push (h : EnvironmentBound b Γ R ρ)
    (hs : CollectionBound R r S) : EnvironmentBound b (push Γ r) R (ρ.push S) := by
  refine ⟨h.this, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [IR.Behavioral.Expression.Ranges.push] using hs
  · simpa [IR.Behavioral.Expression.Ranges.push, Clafer.Behavioral.Environment.push]
      using h.lookup j

def unionSets (sets : List (Set U)) : Set U := {x | ∃ S ∈ sets, x ∈ S}

theorem family_fold (h : CollectionBound R acc S)
    (hs : List.Forall₂ (CollectionBound R) rs sets) :
    CollectionBound R (rs.foldl union acc) (sets.foldl (· ∪ ·) S) := by
  induction hs generalizing acc S with
  | nil => exact h
  | cons ha _ ih => exact ih (h.union ha)

theorem unionSets_fold (sets : List (Set U)) (S : Set U) :
    sets.foldl (· ∪ ·) S = S ∪ unionSets sets := by
  induction sets generalizing S with
  | nil => ext x; simp [unionSets]
  | cons a rest ih =>
    rw [List.foldl_cons, ih]
    ext x
    simp [unionSets, or_assoc]

theorem unionSets_cons (S : Set U) (sets : List (Set U)) :
    unionSets (S :: sets) = S ∪ unionSets sets := by ext x; simp [unionSets]

theorem family_bound (hs : List.Forall₂ (CollectionBound R) rs sets) :
    CollectionBound R (family rs) (unionSets sets) := by
  cases hs with
  | nil => simpa [family, unionSets] using (CollectionBound.empty (R := R))
  | cons ha hs =>
    have bound := family_fold ha hs
    rw [unionSets_fold] at bound
    rw [unionSets_cons]
    exact bound

theorem family_budget (rs : List CollectionEstimate) :
    (family rs).budget = (rs.map CollectionEstimate.budget).sum := by
  have fold (rs : List CollectionEstimate) (a : CollectionEstimate) :
      (rs.foldl union a).budget = a.budget + (rs.map CollectionEstimate.budget).sum := by
    induction rs generalizing a with
    | nil => simp
    | cons a rest ih => simp [List.foldl_cons, ih, union, Nat.add_assoc]
  cases rs with
  | nil => rfl
  | cons a rest => simpa [family] using fold rest a

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem occurrences_bound (hs : List.Forall₂ (CollectionBound R) rs sets) :
    (Clafer.Behavioral.PrimitiveExpression.occurrences sets).Finite ∧
    (Clafer.Behavioral.PrimitiveExpression.occurrences sets).ncard ≤ (family rs).budget := by
  have finite : ∀ S ∈ sets, S.Finite := by
    induction hs with
    | nil => simp
    | cons ha _ ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro ha.finite ih
  have each : ∀ i : Fin sets.length, sets[i].Finite := fun i => finite _ (List.getElem_mem _)
  refine ⟨Clafer.Behavioral.PrimitiveExpression.occurrences_finite sets each, ?_⟩
  rw [occurrences_card sets each, family_budget, ← List.sum_ofFn,
    show (List.ofFn fun i : Fin sets.length => (sets[i]).ncard) = sets.map Set.ncard from
      List.ofFn_getElem_eq_map sets Set.ncard]
  clear finite each
  induction hs with
  | nil => exact le_refl _
  | cons ha _ ih => simpa using Nat.add_le_add ha.card ih

end ClaferCompiler.Correctness.Behavioral.Full.Ranges
