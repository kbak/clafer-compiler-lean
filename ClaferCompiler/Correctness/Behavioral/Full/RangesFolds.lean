module

public import ClaferCompiler.Correctness.Behavioral.Full.RangesValues
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.Card

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Ranges
open IR.Behavioral.Expression.Ranges
open IR.Expr IR.BehavioralArithmetic
open scoped BigOperators

universe u
variable {U : Type u}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The fold budget counts indexed occurrences, including equal values and
repeated operands. Every finite prefix is bounded by the same conservative range. -/
theorem fold_range (op : Fold) {S : Set U} (finite : S.Finite)
    (count : S.ncard ≤ budget) (value : U → Option Int)
    (bounded : ∀ x ∈ S, ∀ z, value x = some z → r.Contains z)
    (result : (SemanticsBridge.BehavioralArithmetic.fold op).eval S value = some z) :
    (foldRange op budget r).Contains z := by
  classical
  have defined := ((Clafer.Behavioral.Aggregate.fold_defined_iff
    (SemanticsBridge.BehavioralArithmetic.fold op) S value).mp ⟨z, result⟩).2
  rw [Clafer.Behavioral.Aggregate.fold_finite _ finite value defined] at result
  let values := finite.toFinset.toList.map (fun x => (value x).getD 0)
  have size : values.length ≤ budget := by
    simpa only [values, List.length_map, Finset.length_toList,
      ← Set.ncard_eq_toFinset_card S finite] using count
  have members : ∀ x ∈ values, r.Contains x := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hn
    have hx : x ∈ S := by simpa using hx
    have hxdef := defined x hx
    cases hval : value x with
    | none => simp [hval] at hxdef
    | some z => simpa [hval] using bounded x hx z hval
  cases op with
  | sum =>
    have eq : z = values.sum := by
      simpa [SemanticsBridge.BehavioralArithmetic.fold, values] using (Option.some.inj result).symm
    rw [eq]
    exact SemanticsBridge.BehavioralArithmetic.fold_sum_range size members
  | product =>
    have eq : z = values.prod := by
      simpa [SemanticsBridge.BehavioralArithmetic.fold, values] using (Option.some.inj result).symm
    rw [eq]
    exact SemanticsBridge.BehavioralArithmetic.fold_product_range size members

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem occurrences_card (domains : List (Set U))
    (finite : ∀ i : Fin domains.length, domains[i].Finite) :
    (Clafer.Behavioral.PrimitiveExpression.occurrences domains).ncard =
      ∑ i : Fin domains.length, (domains[i]).ncard := by
  classical
  let : ∀ i : Fin domains.length, Fintype (domains[i]) := fun i => (finite i).fintype
  let eq : (Clafer.Behavioral.PrimitiveExpression.occurrences domains) ≃
      (Σ i : Fin domains.length, domains[i]) :=
    Equiv.subtypeProdEquivSigmaSubtype fun (i : Fin domains.length) (x : U) => x ∈ domains[i]
  rw [← Nat.card_coe_set_eq, Nat.card_congr eq, Nat.card_eq_fintype_card, Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => Set.fintypeCard_eq_ncard (domains[i]))

end ClaferCompiler.Correctness.Behavioral.Full.Ranges
