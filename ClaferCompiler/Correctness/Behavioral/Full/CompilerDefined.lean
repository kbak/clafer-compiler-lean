module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCommands
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsDefinedLowering

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full
open TargetDefined

theorem all_list_pure (fs : List Formula) (pure : ∀ f ∈ fs, FormulaPure f) :
    FormulaPure (Backend.Alloy.Behavioral.Full.Expressions.all fs) := by
  induction fs with
  | nil => exact pure_truth
  | cons f fs ih =>
    exact (pure_binary _ _ _).mpr ⟨pure f (by simp),
      ih (fun f member => pure f (List.mem_cons_of_mem _ member))⟩

theorem command_syntax (r : Request k) (b : Bounds) (fuel : Nat)
    (kind : Backend.Alloy.CommandKind) (body : Formula)
    (success : commandResult r b fuel = .ok (kind, body)) : body.Built ∧ FormulaPure body := by
  cases cmd : r.command with
  | check index =>
    cases result : constraint r.model.structural b fuel r.model.assertions[index] with
    | error err => simp only [commandResult, cmd, result, bind, Except.bind] at success; contradiction
    | ok formula =>
      have pair : (Backend.Alloy.CommandKind.check, formula) = (kind, body) := by
        simpa only [commandResult, cmd, result, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success
      cases pair
      exact ⟨constraint_built _ b fuel _ _ result, TargetDefined.constraint_pure _ b fuel _ _ result⟩
  | run scenario =>
    cases result : scenario.mapM (constraint r.model.structural b fuel) with
    | error err => simp [commandResult, cmd, result, bind, Except.bind] at success
    | ok formulas =>
      have pair : (Backend.Alloy.CommandKind.run, Backend.Alloy.Behavioral.Full.Expressions.all formulas) = (kind, body) := by
        simpa only [commandResult, cmd, result, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success
      cases pair
      have syntactic : ∀ f ∈ formulas, f.Built ∧ FormulaPure f :=
        (paired_forall (P := fun _ => True) (Q := fun f => f.Built ∧ FormulaPure f)
          (Expressions.mapM_ok _ _ _ result) (fun a f success => iff_true_intro
            ⟨constraint_built _ b fuel _ _ success, TargetDefined.constraint_pure _ b fuel _ _ success⟩)).mpr
              (fun _ _ => True.intro)
      exact ⟨all_list_built formulas (fun f member => (syntactic f member).1),
        all_list_pure formulas (fun f member => (syntactic f member).2)⟩

theorem checked_fact_safe (m : CheckedModule) (f : Formula) (member : f ∈ m.raw.facts) :
    f.safe m.raw = true := by
  have bounded := m.bounded
  simp only [Module.safeBounds, Bool.and_eq_true] at bounded
  exact List.all_eq_true.mp bounded.1.2 f member

theorem checked_command_safe (m : CheckedModule) : m.raw.command.body.safe m.raw = true := by
  have bounded := m.bounded
  simp only [Module.safeBounds, Bool.and_eq_true] at bounded
  exact bounded.2

namespace CompileOutput
variable {r : Request k} {b : Bounds} {fuel : Nat} {c : Compiled}

theorem behavioral_safe (out : CompileOutput r b fuel c)
    (f : Formula) (member : f ∈ out.constraints ++ out.modifiers) :
    f.safe c.module.raw = true := by
  apply checked_fact_safe c.module f
  rw [out.module_eq]
  rcases List.mem_append.mp member with member | member
  · exact List.mem_append_left _ (List.mem_append_right _ member)
  · exact List.mem_append_right _ member

theorem behavioral_built (out : CompileOutput r b fuel c)
    (f : Formula) (member : f ∈ out.constraints ++ out.modifiers) : f.Built := by
  rcases List.mem_append.mp member with member | member
  · have all := (paired_forall (P := fun _ => True) (Q := Formula.Built)
      (Expressions.mapM_ok _ _ _ out.constraints_lowered)
      (fun a formula run => iff_true_intro (constraint_built _ b fuel a formula run))).mpr
        (fun _ _ => True.intro)
    exact all f member
  · have all := (paired_forall (P := fun _ => True) (Q := Formula.Built)
      (Expressions.mapM_ok _ _ _ out.modifiers_lowered)
      (fun item formula run => iff_true_intro (attached_built _ b fuel (placement _ item.1) item.2 formula run))).mpr
        (fun _ _ => True.intro)
    exact all f member

theorem behavioral_pure (out : CompileOutput r b fuel c)
    (f : Formula) (member : f ∈ out.constraints ++ out.modifiers) : FormulaPure f := by
  rcases List.mem_append.mp member with member | member
  · have all := (paired_forall (P := fun _ => True) (Q := FormulaPure)
      (Expressions.mapM_ok _ _ _ out.constraints_lowered)
      (fun a formula run => iff_true_intro (TargetDefined.constraint_pure _ b fuel a formula run))).mpr
        (fun _ _ => True.intro)
    exact all f member
  · have all := (paired_forall (P := fun _ => True) (Q := FormulaPure)
      (Expressions.mapM_ok _ _ _ out.modifiers_lowered)
      (fun item formula run => iff_true_intro (TargetDefined.attached_pure _ b fuel
        (placement _ item.1) item.2 formula run))).mpr (fun _ _ => True.intro)
    exact all f member

theorem command_safe (out : CompileOutput r b fuel c) : out.body.safe c.module.raw = true := by
  have safe := checked_command_safe c.module
  rw [out.module_eq] at safe ⊢
  exact safe

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem behavioral_defined (out : CompileOutput r b fuel c)
    (τ : Trace) (e : Environment) (t : Nat)
    (f : Formula) (member : f ∈ out.constraints ++ out.modifiers) :
    f.Defined (schema r.model.structural) b.bitwidth τ e t := by
  have defined := TargetDefined.formula_defined (out.behavioral_built f member)
    (out.behavioral_pure f member) (out.behavioral_safe f member) τ e t
  rw [out.module_eq] at defined
  exact defined

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem command_defined (out : CompileOutput r b fuel c)
    (τ : Trace) (e : Environment) (t : Nat) :
    out.body.Defined (schema r.model.structural) b.bitwidth τ e t := by
  have syntactic := command_syntax r b fuel out.kind out.body out.command_lowered
  have defined := TargetDefined.formula_defined syntactic.1 syntactic.2 out.command_safe τ e t
  rw [out.module_eq] at defined
  exact defined

end CompileOutput
end ClaferCompiler.Correctness.Behavioral.Full
