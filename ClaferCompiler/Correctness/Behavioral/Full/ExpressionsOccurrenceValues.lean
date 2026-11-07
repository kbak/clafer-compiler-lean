module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsOccurrences
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersFoldValues
public import ClaferCompiler.Correctness.Behavioral.Full.RangesEnvironments

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Occurrences
variable {U : Type}

theorem sourceValue_list (op : IR.BehavioralArithmetic.Fold) (xs : List U) (body : U → Option Int) :
    IntegerFold.sourceValue op (xs.map body) =
      if ∀ x ∈ xs, (body x).isSome then
        some (match SemanticsBridge.BehavioralArithmetic.fold op with
          | .sum => (xs.map fun x => (body x).getD 0).sum
          | .product => (xs.map fun x => (body x).getD 0).prod)
      else none := by
  classical
  cases result : (xs.map body).mapM id with
  | some values =>
    have mapped := (IntegerFold.mapM_id_eq _ _).mp result
    have defined : ∀ x ∈ xs, (body x).isSome := by
      intro x hx
      have member : body x ∈ values.map some := mapped ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
      obtain ⟨z, _, hz⟩ := List.mem_map.mp member
      simp [← hz]
    have valuesEq := congrArg (List.map (fun z : Option Int => z.getD 0)) mapped
    simp only [List.map_map, Function.comp_def, Option.getD_some] at valuesEq
    rw [IntegerFold.sourceValue, result, Option.map_some, ite_eq_left defined, valuesEq]
    cases op <;> simp [IntegerFold.initial, SemanticsBridge.BehavioralArithmetic.fold,
      List.sum_eq_foldl, List.prod_eq_foldl] <;> rfl
  | none =>
    have undefined : ¬ ∀ x ∈ xs, (body x).isSome := by
      intro defined
      have mapped : xs.map body = (xs.map fun x => (body x).getD 0).map some := by
        rw [List.map_map]
        apply List.map_congr_left
        intro x hx
        have hd := defined x hx
        cases value : body x with
        | none => simp [value] at hd
        | some z => simp [value]
      have success := (IntegerFold.mapM_id_eq _ _).mpr mapped
      rw [result] at success
      contradiction
    simp only [IntegerFold.sourceValue, result, Option.map_none, ite_eq_right undefined]

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem fold_occurrences_sourceValue {sets : List (Set U)} {lists : List (List U)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists)
    (op : IR.BehavioralArithmetic.Fold) (body : U → Option Int) :
    (SemanticsBridge.BehavioralArithmetic.fold op).eval
      (Clafer.Behavioral.PrimitiveExpression.occurrences sets) (fun ix => body ix.2) =
        IntegerFold.sourceValue op (lists.flatten.map body) := by
  rw [fold_occurrences represented, sourceValue_list]
  rfl

theorem flatten_length_bound {sets : List (Set U)} {lists : List (List U)}
    {R : Clafer.Constraints.IntegerRealization U}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists)
    (bounded : List.Forall₂ (Ranges.CollectionBound R) estimates sets) :
    lists.flatten.length ≤ (IR.Behavioral.Expression.Ranges.family estimates).budget := by
  rw [← occurrences_length represented]
  exact (Ranges.occurrences_bound bounded).2

end ClaferCompiler.Correctness.Behavioral.Full.Occurrences
