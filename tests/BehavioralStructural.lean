module

public import tests.BehavioralStructuralNative
public import ClaferCompiler.SemanticsBridge.BehavioralResolution
public import ClaferCompiler.SemanticsBridge.BehavioralSupport
public import ClaferCompiler.SemanticsBridge.BehavioralArithmetic

public section
namespace ClaferCompiler.Tests.BehavioralStructural
open IR.BehavioralStructural IR.BehavioralSupport
open SemanticsBridge.BehavioralStructural

-- [utest->req~compiler-behavioral-structural-bridge~1]
theorem rich_wellFormed : (interpret core).WellFormed := validated_wellFormed validated

theorem exact_hierarchy : (analyze core).Valid core := by decide

theorem inherited_owner : validated.analysis.referenceOwners[5] = some 3 := by decide

theorem own_and_inherited : childDeclarations validated 4 = [3, 5] := by decide
theorem ordinary_inherited_field : childDeclarations validated 5 = [6] := by decide

/-- Counting this union counts the same object once even when both declaration
views contain it; equal targets of different heads do not merge those heads. -/
theorem group_head_union (s : Clafer.Semantics.Configuration (Fin 7) U) (p x : U) :
    Clafer.Semantics.Groups.ChildObjects (interpret core).family s 4 p x ↔
      s.contains 3 p x ∨ s.contains 5 p x := by
  exact (childObjects_iff validated s 4 p x).trans (by
    rw [own_and_inherited]
    simp)

theorem refined_reference_roles :
    role validated 5 5 1 .dereference ∧ role validated 5 4 1 .target ∧
    role validated 5 5 4 .parent ∧ ¬ role validated 5 5 2 .parent := by decide

theorem inherited_semantic_role :
    Clafer.Behavioral.StructuralBinding.Role (interpret core) 5 5 1 .dereference :=
  (SemanticsBridge.BehavioralSupport.role_iff validated 5 5 1 .dereference).mp
    refined_reference_roles.1

theorem static_guard_unchanged : ¬ IR.Structural.supportChecks core.structural certificate := by decide

theorem occurrence_vs_target_sum :
    IR.BehavioralArithmetic.Fold.sum.eval [[some 3, some 3]] = some 6 ∧
    IR.BehavioralArithmetic.coerce [3, 3] = 3 := by decide

theorem strict_zero_product :
    IR.BehavioralArithmetic.Fold.product.eval [[some 0, none]] = none := by decide

theorem empty_extrema_defined :
    IR.BehavioralArithmetic.minimum [] = [] ∧ IR.BehavioralArithmetic.coerce [] = 0 ∧
    IR.BehavioralArithmetic.extract [] = none := by decide

theorem signed_quotient : IR.BehavioralArithmetic.Binary.divide.eval (some (-7)) (some 3) = some (-2) ∧
    IR.BehavioralArithmetic.Binary.remainder.eval (some (-7)) (some 3) = some (-1) := by decide

end ClaferCompiler.Tests.BehavioralStructural
