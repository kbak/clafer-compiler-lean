module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsValuesPreservation
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsIntegerStep
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFoldStep
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPredicateStep
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsCountStep
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaStep

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral

variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment}

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Every successful executable pass preserves the original source expression,
including its strict domain, raw truth and both source signs. Only primitive
observations, finite identity labels and checked numerical bounds are premises. -/
theorem lowerAt_preserves (model : ModelRows v b s τ σ labels) (fuel depth : Nat) :
    PassObservation v b s τ σ labels (lowerAt v b fuel depth) := by
  induction depth with
  | zero =>
    constructor <;> intros <;> contradiction
  | succ depth ih =>
    have built := SyntaxBuilt.lowerAt v b fuel depth
    refine {
      set := ?_
      collection := ?_
      integer := ?_
      collections := ?_
      predicate := ?_
      atom := ?_
      formula := ?_ }
    · intro n c ρ e hc t a result success
      have h := Sets.lowerAt_set (t := t) model.primitive hc.context b fuel (depth + 1) a success
      exact ⟨h.1, h.2.1⟩
    · intro n c ρ e hc t a result estimate bound success
      exact lowerStep_collection model ih hc bound success
    · intro n c ρ e hc t a result range bound success
      exact integerStep_of_fold model ih hc
        (fun _ _ _ _ _ bound success => foldStep model ih built hc bound success) bound success
    · intro n c ρ e hc t a result estimates bound success
      exact lowerStep_collections ih hc bound success
    · intro n c ρ e hc t a result bound success
      exact predicateStep model ih hc bound success
    · intro n c ρ e hc t a result bound success
      cases a with
      | primitive a =>
        cases bound with
        | primitive bound => exact ih.predicate hc t a result bound success
      | count q arity disjoint d a => exact countStep model ih built hc bound success
    · intro n c ρ e hc t a result bound success
      exact formulaStep model ih built hc bound success

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The public checked lowering obtains its entire range derivation from the
actual admission result, without assuming any source satisfaction. -/
theorem lower_preserves (model : ModelRows v b s τ σ labels)
    (lexical : LexicalRows b s τ labels c ρ e) (a : Expression.Formula k n)
    (fuel : Nat) (enough : sizeOf a < fuel)
    (success : lower v b c a fuel enough = .ok result) (t : Nat) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) result := by
  cases analyzed : Expression.Ranges.analyze b fuel a c.estimates with
  | error error => simp [lower, analyzed, bind, Except.bind] at success
  | ok checked =>
    have success : (lowerAt v b fuel fuel).formula c a = .ok result := by
      simpa [lower, analyzed, bind, Except.bind] using success
    exact (lowerAt_preserves model fuel fuel).formula lexical t a result checked.property success

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
