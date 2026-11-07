module

public import ClaferCompiler.Correctness.Behavioral.Full.ModifierExpansions
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open IR.Behavioral
open Backend.Alloy.Behavioral.Full

theorem observed_formula_denote {U : Type} {A D : Nat → Type}
    (m : Clafer.Behavioral.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (O : Clafer.Behavioral.Observation A D U) (a : Clafer.Behavioral.Formula A D n)
    (positive : Bool) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    a.denote (Clafer.Behavioral.Structural.observed m τ) O positive ρ t ↔
      a.denote τ O positive ρ t := by
  rw [← Clafer.Behavioral.Formula.normalize_agrees, ← Clafer.Behavioral.Formula.normalize_agrees]
  exact observed_formula_raw m τ O (a.normalize positive) ρ t

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Full expression modifiers agree with the accepted model-wide inherited
modifier contract. Every direct/inherited expansion remains conjunctive. -/
theorem modifierExpansions_source {U : Type} (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List Surface.Modifiers.Modifier) k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ) :
    (∀ item ∈ (List.finRange k).flatMap (fun d =>
        (IR.Behavioral.Modifiers.effective v table d).flatMap (modifierExpansions d)),
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        R item.2).PartialAttached
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        SemanticsBridge.Behavioral.Expression.observation
        ((SemanticsBridge.Behavioral.Surface.Modifiers.placement item.1).contexts
          (SemanticsBridge.BehavioralStructural.interpret v.core) τ)) ↔
    Clafer.Behavioral.Modifiers.Holds (SemanticsBridge.BehavioralStructural.interpret v.core) τ
      (SemanticsBridge.Behavioral.Modifiers.declared table) := by
  rw [← SemanticsBridge.Behavioral.Modifiers.expansions_agree v table τ valid]
  simp only [IR.Behavioral.Modifiers.expansions, List.forall_mem_flatMap,
    List.mem_finRange, forall_const]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro modifier
  apply imp_congr_right
  intro _
  apply (ModifierExpansions.expansions_agree (Sets.model v)
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
    R d modifier (fun place => (SemanticsBridge.Behavioral.Surface.Modifiers.placement place).contexts
      (SemanticsBridge.BehavioralStructural.interpret v.core) τ)).trans
  apply forall_congr'
  intro item
  apply imp_congr_right
  intro _
  unfold Clafer.Behavioral.Formula.Attached
  apply forall_congr'
  intro t
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  exact observed_formula_denote _ _ _ _ _ _ _

end ClaferCompiler.Correctness.Behavioral.Full
