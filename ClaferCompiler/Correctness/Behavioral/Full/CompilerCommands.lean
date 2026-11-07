module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerRows
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

theorem paired_forall {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    {xs : List α} {ys : List β} (paired : List.Forall₂ R xs ys)
    (meaning : ∀ x y, R x y → (Q y ↔ P x)) :
    (∀ y ∈ ys, Q y) ↔ ∀ x ∈ xs, P x := by
  induction paired with
  | nil => simp
  | @cons x y xs ys related _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_congr (meaning x y related) ih

theorem all_list_built (fs : List Formula) (built : ∀ f ∈ fs, f.Built) :
    (Backend.Alloy.Behavioral.Full.Expressions.all fs).Built := by
  induction fs with
  | nil => exact .truth
  | cons f fs ih =>
    exact .binary .conj (built f (by simp))
      (ih (fun f member => built f (List.mem_cons_of_mem _ member)))

theorem all_list_holds (fs : List Formula) (built : ∀ f ∈ fs, f.Built) :
    (Backend.Alloy.Behavioral.Full.Expressions.all fs).Holds s w τ e t ↔
      ∀ f ∈ fs, f.Holds s w τ e t := by
  induction fs with
  | nil => exact ⟨fun _ f member => (List.not_mem_nil member).elim, fun _ => True.intro⟩
  | cons f fs ih =>
    have first := built f (by simp)
    have rest := fun f member => built f (List.mem_cons_of_mem _ member)
    change (Formula.binary .conj f (Backend.Alloy.Behavioral.Full.Expressions.all fs)).Holds _ _ _ _ _ ↔ _
    rw [Encoding.holds_and first (all_list_built fs rest), ih rest]
    simp only [List.mem_cons, forall_eq_or_imp]

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem constraints_source (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (capacity : o ≤ b.objects)
    (model : Expressions.ModelRows v (estimates v b) (schema v) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) rep.labels)
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source))
    (as : List (Constraint k)) (results : List Formula)
    (success : as.mapM (constraint v b fuel) = .ok results) :
    (∀ f ∈ results, f.Holds (schema v) b.bitwidth target.unfold [] 0) ↔
      ∀ a ∈ as, (sourceConstraint v a).Holds (completeTrace v p source)
        (sourceObservation v completeIntegers (completeTrace v p source)) := by
  exact paired_forall (Expressions.mapM_ok _ _ _ success) fun a result success =>
    rep.constraint_source b fuel p primitive capacity (Expressions.lowerAt_preserves model fuel fuel)
      facts valid a result success

end TraceRep

def commandHolds (kind : Backend.Alloy.CommandKind) (body : Formula)
    (s : Schema) (w : Nat) (τ : Trace) : Prop :=
  match kind with
  | .run => body.Holds s w τ [] 0
  | .check => ¬ body.Holds s w τ [] 0

-- [proof->req~compiler-full-behavioral-correctness~1]
-- [proof->req~compiler-behavioral-property-commands~1]
theorem command_source (r : Request k) (b : Bounds) (fuel : Nat)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (target : Lasso)
    (rep : TraceRep r.model.structural source target) (capacity : o ≤ b.objects)
    (model : Expressions.ModelRows r.model.structural (estimates r.model.structural b)
      (schema r.model.structural) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
        (completeTrace r.model.structural p source)) rep.labels)
    (facts : ∀ t f, f ∈ stateFacts r.model.structural →
      f.Holds (schema r.model.structural) b.bitwidth target.unfold [] t)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
      (completeTrace r.model.structural p source))
    (kind : Backend.Alloy.CommandKind) (body : Formula)
    (success : commandResult r b fuel = .ok (kind, body)) :
    commandHolds kind body (schema r.model.structural) b.bitwidth target.unfold ↔
    SourceCommand r completeIntegers (completeTrace r.model.structural p source) := by
  have pass := Expressions.lowerAt_preserves model fuel fuel
  cases cmd : r.command with
  | check index =>
    cases result : constraint r.model.structural b fuel r.model.assertions[index] with
    | error err => simp only [commandResult, cmd, result, bind, Except.bind] at success; contradiction
    | ok formula =>
      have pair : (Backend.Alloy.CommandKind.check, formula) = (kind, body) := by
        simpa only [commandResult, cmd, result, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success
      cases pair
      simp only [SourceCommand, cmd, commandHolds]
      exact not_congr (rep.constraint_source b fuel p primitive capacity pass facts valid _ _ result)
  | run scenario =>
    cases result : scenario.mapM (constraint r.model.structural b fuel) with
    | error err => simp [commandResult, cmd, result, bind, Except.bind] at success
    | ok formulas =>
      have pair : (Backend.Alloy.CommandKind.run, Backend.Alloy.Behavioral.Full.Expressions.all formulas) = (kind, body) := by
        simpa only [commandResult, cmd, result, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success
      cases pair
      have paired := Expressions.mapM_ok _ _ _ result
      have built : ∀ formula ∈ formulas, formula.Built := by
        exact (paired_forall (P := fun _ => True) (Q := Formula.Built) paired
          (fun a formula run => iff_true_intro (constraint_built _ b fuel a formula run))).mpr
          (fun _ _ => True.intro)
      simp only [SourceCommand, cmd, commandHolds]
      exact (all_list_holds formulas built).trans
        (rep.constraints_source b fuel p primitive capacity model facts valid scenario formulas result)

end ClaferCompiler.Correctness.Behavioral.Full
