module

public import ClaferCompiler.SemanticsBridge.Behavioral.Grouped
public import ClaferCompiler.SemanticsBridge.Behavioral.GenericSurface
public import tests.BehavioralPrimitiveNative

public section
namespace ClaferCompiler.Tests.BehavioralPrimitive
open ClaferCompiler.SemanticsBridge.Behavioral

-- [utest->req~compiler-behavioral-elaboration~1]
/-- The three admissible ordered pairs do not satisfy grouped uniqueness. -/
theorem joint_one_rejects_three_pairs :
    ¬ Clafer.Behavioral.Quantifier.eval .one
      (Grouped.assignments 2 false (Set.univ : Set (Fin 2)))
      (fun a => a 0 = 0 ∨ a 1 = 0) := by
  simp only [Clafer.Behavioral.Quantifier.eval, Grouped.assignments,
    Set.mem_ofPred_eq, Set.mem_univ, forall_const, Bool.false_eq_true,
    false_implies, and_self, true_and, ExistsUnique]
  decide

/-- Disjointness preserves both permutations; it does not form an unordered set. -/
theorem disjoint_pairs_are_ordered :
    ¬ Clafer.Behavioral.Quantifier.eval .one
      (Grouped.assignments 2 true (Set.univ : Set (Fin 2))) (fun _ => True) := by
  simp only [Clafer.Behavioral.Quantifier.eval, Grouped.assignments,
    Set.mem_ofPred_eq, Set.mem_univ, forall_const, true_and, and_true, ExistsUnique]
  decide

/-- A true disjunct cannot hide a missing result in the other disjunct. -/
theorem strict_undefined_branch (τ : Clafer.Behavioral.Trace Unit Nat)
    (ρ : Clafer.Behavioral.Environment Nat 0) (positive : Bool) (t : Nat) :
    ¬ (Primitive.formula partialBody).Satisfies τ
      ⟨fun _ _ _ => none, fun _ _ _ => some ∅⟩ positive ρ t := by
  simp [Primitive.formula, Generic.interpret, partialBody,
    Clafer.Behavioral.Formula.Satisfies, Clafer.Behavioral.Formula.Defined]

end ClaferCompiler.Tests.BehavioralPrimitive
