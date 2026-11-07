module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsDefinedPartial
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsAttachments

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

theorem existsMany_pure (n : Nat) (r : Rel) (h : FormulaPure p) :
    FormulaPure (Nat.repeat (Formula.exists_ r) n p) := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih => exact (pure_exists _ _).mpr (ih h)

theorem coverPool_pure (n : Nat) (h : FormulaPure p) :
    FormulaPure (Backend.Alloy.Behavioral.coverPool n p) :=
  existsMany_pure n _ ((pure_binary .conj _ _).mpr ⟨pure_equal _ _, h⟩)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem attached_pure_of_pass (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (pass : ∀ (ctx : Expressions.Context 0) a body,
      (Expressions.lowerAt v (estimates v b) fuel fuel).formula ctx a = .ok body → PartialPure body)
    (owners : Rel) (a : IR.Behavioral.Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result) : FormulaPure result := by
  have property : SyntaxBuilt.Success FormulaPure (attached v b fuel owners a) := by
    unfold attached
    apply SyntaxBuilt.bind_any (Q := FormulaPure)
    intro _
    apply SyntaxBuilt.bind (Q := FormulaPure) (P := PartialPure) (pass _ a)
    intro body hp
    exact SyntaxBuilt.pure (coverPool_pure _ ((pure_unary _ _).mpr
      ((pure_all _ _).mpr (partial_satisfaction hp true))))
  exact property result success

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem attached_defined_of_pass (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (pass : ∀ (ctx : Expressions.Context 0) a body,
      (Expressions.lowerAt v (estimates v b) fuel fuel).formula ctx a = .ok body → PartialPure body)
    (owners : Rel) (a : IR.Behavioral.Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result)
    (m : Module) (safe : result.safe m = true) (τ : Trace) (e : Environment) (t : Nat) :
    result.Defined m.schema m.command.bitwidth τ e t :=
  formula_defined (attached_built v b fuel owners a result success)
    (attached_pure_of_pass v b fuel pass owners a result success) safe τ e t

end ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
