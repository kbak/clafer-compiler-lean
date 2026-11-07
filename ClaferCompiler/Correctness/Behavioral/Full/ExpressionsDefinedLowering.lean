module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsCountFree
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsDefinedAttachments

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem attached_pure (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (owners : Rel) (a : IR.Behavioral.Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result) : FormulaPure result :=
  attached_pure_of_pass v b fuel ((CountFree.lowerAt v (estimates v b) fuel fuel).formula)
    owners a result success

theorem constraint_pure (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (a : Constraint k) (result : Formula)
    (success : constraint v b fuel a = .ok result) : FormulaPure result := by
  cases ordinary : integerDeclaration v a.owner with
  | true =>
    change (if integerDeclaration v a.owner = true then Except.error (error "behavioral.infinite-attachment")
      else attached v b fuel (head v a.owner) a.body) = .ok result at success
    rw [ordinary] at success
    contradiction
  | false =>
    apply attached_pure v b fuel (head v a.owner) a.body result
    simpa only [constraint, ordinary, Bool.false_eq_true, ↓reduceIte] using success

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Original source undefinedness remains representable: all arithmetic in the
emitted target property is defined even in inactive alternatives and under a
check command's negation. Admission supplies the numerical certificates. -/
theorem attached_defined (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (owners : Rel) (a : IR.Behavioral.Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result)
    (m : Module) (safe : result.safe m = true) (τ : Trace) (e : Environment) (t : Nat) :
    result.Defined m.schema m.command.bitwidth τ e t :=
  formula_defined (attached_built v b fuel owners a result success)
    (attached_pure v b fuel owners a result success) safe τ e t

theorem constraint_defined (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (a : Constraint k) (result : Formula)
    (success : constraint v b fuel a = .ok result)
    (m : Module) (safe : result.safe m = true) (τ : Trace) (e : Environment) (t : Nat) :
    result.Defined m.schema m.command.bitwidth τ e t :=
  formula_defined (constraint_built v b fuel a result success)
    (constraint_pure v b fuel a result success) safe τ e t

end ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
