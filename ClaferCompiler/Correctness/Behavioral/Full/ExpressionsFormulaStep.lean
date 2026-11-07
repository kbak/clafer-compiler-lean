module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaBinders
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaTemporal
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPresence

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open IR.Behavioral
open Backend.Alloy.Behavioral.Full.Expressions

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem formulaStep (model : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (built : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.FormulaBound b c.estimates a)
    (success : (lowerStep v b fuel next).formula c a = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) result := by
  cases a with
  | truth =>
    have same := Except.ok.inj success
    subst result
    exact FormulaObservation.truth
  | atom a =>
    cases bound with
    | atom bound => exact ih.atom hc t a result bound success
  | not a =>
    cases bound with
    | not bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.negation body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.negation (ih.formula hc t a body bound hs)
  | next a =>
    cases bound with
    | next bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.next (parentPresent v c) body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.next (fun j => ih.formula hc j a body bound hs)
          Sets.parentPresent_built (Sets.parentPresent_meaning model.primitive hc.context)
  | eventually a =>
    cases bound with
    | eventually bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.eventually (parentPresent v c) body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.eventually (fun j => ih.formula hc j a body bound hs)
          Sets.parentPresent_built (Sets.parentPresent_meaning model.primitive hc.context)
  | always a =>
    cases bound with
    | always bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.always (parentPresent v c) body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.always (fun j => ih.formula hc j a body bound hs)
          Sets.parentPresent_built (Sets.parentPresent_meaning model.primitive hc.context)
  | initially a =>
    cases bound with
    | initially bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.initially (present v c) body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.initially (ih.formula hc t a body bound hs)
          Sets.present_built (Sets.present_meaning model.primitive hc.context)
  | «finally» a =>
    cases bound with
    | «finally» bound =>
      change (do let body ← next.formula c a; pure (Backend.Alloy.Behavioral.Partial.«finally» (present v c) body)) = .ok result at success
      cases hs : next.formula c a with
      | error error => rw [hs] at success; contradiction
      | ok body =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        exact FormulaObservation.«finally» (ih.formula hc t a body bound hs)
          Sets.present_built (Sets.present_meaning model.primitive hc.context)
  | and a d =>
    cases bound with
    | and left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.conjunction x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.conjunction (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | or a d =>
    cases bound with
    | or left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.disjunction x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.disjunction (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | implies a d =>
    cases bound with
    | implies left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.implication x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.implication (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | iff a d =>
    cases bound with
    | iff left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.equivalence x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.equivalence (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | xor a d =>
    cases bound with
    | xor left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.exclusiveOr x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.exclusiveOr (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | strongUntil a d =>
    cases bound with
    | strongUntil left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.strongUntil (parentPresent v c) x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.strongUntil (fun j => ih.formula hc j a x left hx)
            (fun j => ih.formula hc j d y right hy)
            Sets.parentPresent_built (Sets.parentPresent_meaning model.primitive hc.context)
  | weakUntil a d =>
    cases bound with
    | weakUntil left right =>
      change (do let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.weakUntil (parentPresent v c) x y)) = .ok result at success
      cases hx : next.formula c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.formula c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          exact FormulaObservation.weakUntil (fun j => ih.formula hc j a x left hx)
            (fun j => ih.formula hc j d y right hy)
            Sets.parentPresent_built (Sets.parentPresent_meaning model.primitive hc.context)
  | ite cond a d =>
    cases bound with
    | ite condition left right =>
      change (do let z ← next.formula c cond; let x ← next.formula c a; let y ← next.formula c d; pure (Backend.Alloy.Behavioral.Partial.conditional z x y)) = .ok result at success
      cases hz : next.formula c cond with
      | error error => rw [hz] at success; contradiction
      | ok z =>
        cases hx : next.formula c a with
        | error error => rw [hz, hx] at success; contradiction
        | ok x =>
          cases hy : next.formula c d with
          | error error => rw [hz, hx, hy] at success; contradiction
          | ok y =>
            rw [hz, hx, hy] at success
            have same := Except.ok.inj success
            subst result
            exact FormulaObservation.conditional (ih.formula hc t cond z condition hz)
              (ih.formula hc t a x left hx) (ih.formula hc t d y right hy)
  | quant q d a =>
    cases bound with
    | quant domain body => exact formula_quantStep model ih built hc domain body success
  | letSet d a =>
    cases bound with
    | letSet domain body => exact formula_letStep model ih built hc domain body success

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
