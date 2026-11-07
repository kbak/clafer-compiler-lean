module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsQuantifiers
public import ClaferCompiler.Correctness.Behavioral.RepresentationRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open Encoding
variable {U : Type}

/-- Raw truth and the two independent source polarities are proved together. -/
def sourcePart (v : IR.Structural.Layout k) (σ : Clafer.Behavioral.Trace (Fin k) U)
    (a : IR.Behavioral.Formula k n) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    Option Bool → Prop
  | none => (SemanticsBridge.Behavioral.formula a).raw σ
      (.sets (SemanticsBridge.Structural.interpret v.core) σ) ρ t
  | some b => (SemanticsBridge.Behavioral.formula a).denote σ
      (.sets (SemanticsBridge.Structural.interpret v.core) σ) b ρ t

theorem formulaAt_succ (v : IR.Structural.Layout k) (fuel : Nat) (c : Context n)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel + 1) :
    formulaAt v (fuel + 1) c a h = formulaStep v fuel (formulaAt v fuel) c a h := rfl

@[simp] theorem formulaAt_raw_built (v : IR.Structural.Layout k) (fuel : Nat) (c : Context n)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).raw.Built := (formulaAt_built v fuel c a h).raw
@[simp] theorem formulaAt_positive_built (v : IR.Structural.Layout k) (fuel : Nat) (c : Context n)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).positive.Built := (formulaAt_built v fuel c a h).positive
@[simp] theorem formulaAt_negative_built (v : IR.Structural.Layout k) (fuel : Nat) (c : Context n)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).negative.Built := (formulaAt_built v fuel c a h).negative

attribute [local simp] Formula.Built.truth Formula.Built.unary Formula.Built.binary
  Formula.Built.all Formula.Built.exists_ Formula.Built.mult Formula.Built.equal Formula.Built.subset
  atom_built parentPresent_built present_built

-- [proof->req~compiler-behavioral-correctness~1]
/-- Every admitted formula constructor preserves both signed meanings and the
classical counting barrier. PrimitiveAgreement is supplied by TraceRep's exact
row equations; ContextRep records frozen identities and set captures only. -/
theorem formulaAt_meaning (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat)
    (hp : PrimitiveAgreement v w σ τ f) (fuel : Nat) {n : Nat}
    (c : Context n) (ρ : Clafer.Behavioral.Environment U n) (e : Environment)
    (hc : ContextRep v w τ f c ρ e) (t : Nat)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) (p : Option Bool) :
    (part (formulaAt v fuel c a h) p).Holds (schema v) w τ e t ↔ sourcePart v σ a ρ t p := by
  classical
  induction fuel generalizing n c ρ e t a p with
  | zero => omega
  | succ fuel ih =>
    have ir (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) (t : Nat) :=
      ih c ρ e hc t a h none
    have ip (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) (t : Nat) :=
      ih c ρ e hc t a h (some true)
    have im (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) (t : Nat) :=
      ih c ρ e hc t a h (some false)
    dsimp only [part, sourcePart] at ir ip im
    cases a with
    | truth =>
      cases p with
      | none => rfl
      | some b => cases b <;> rfl
    | atom a =>
      have ha := atom_meaning v w σ τ f hp c ρ e hc t fuel a (by simp_all; omega)
      cases p with
      | none => exact ha
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.atomic,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          Clafer.Behavioral.polarity, Clafer.Behavioral.Observation.sets, ha]
    | not a =>
      cases p with
      | none =>
        simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw] using not_congr (ir a _ t)
      | some b =>
        cases b <;> simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote] using
          (show _ from (by first | exact ip a _ t | exact im a _ t))
    | and a b =>
      cases p with
      | none =>
        simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, conjunction,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw] using and_congr (ir a _ t) (ir b _ t)
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, conjunction,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im]
    | or a b =>
      cases p with
      | none =>
        simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, disjunction,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw] using or_congr (ir a _ t) (ir b _ t)
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, disjunction,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im]
    | implies a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, ir, imp_iff_not_or]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im]
    | iff a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, equivalence, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, ir, imp_iff_not_or, iff_iff_implies_and_implies]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, equivalence, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im]
    | xor a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, equivalence, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, ir, imp_iff_not_or, iff_iff_implies_and_implies]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, equivalence, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im, and_comm, or_comm]
    | ite cond a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, ir, imp_iff_not_or]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, conjunction, implication, disjunction, negation,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, ip, im]
    | next a =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map,
          next_meaning, SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map,
          next_meaning, SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ip, im]
    | eventually a =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, eventually_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, eventually_meaning, always_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ip, im]
    | always a =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, always_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, eventually_meaning, always_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ip, im]
    | strongUntil a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, until_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, until_meaning, Encoding.weakUntil_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ip, im]
    | weakUntil a b =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Encoding.weakUntil_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, until_meaning, Encoding.weakUntil_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote,
          parentPresent_meaning v w σ τ f hp c ρ e hc, ip, im]
    | initially a =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map, initially_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, Clafer.Behavioral.Trace.Starts,
          present_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map, initially_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, Clafer.Behavioral.Trace.Starts,
          present_meaning v w σ τ f hp c ρ e hc, ip, im]
    | «finally» a =>
      cases p with
      | none =>
        simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map, atEnd_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.raw, Clafer.Behavioral.Trace.Ends,
          present_meaning v w σ τ f hp c ρ e hc, ir]
      | some b =>
        cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.map, atEnd_meaning,
          SemanticsBridge.Behavioral.formula, Clafer.Behavioral.Formula.denote, Clafer.Behavioral.Trace.Ends,
          present_meaning v w σ τ f hp c ρ e hc, ip, im]
    | letSet d a =>
      have hd : sizeOf d < fuel := by simp_all; omega
      have ha : sizeOf a < fuel := by simp_all; omega
      have hh := freeze_meaning v w τ f hp.injective e t c.aliases (setAt v c fuel d hd)
        ((SemanticsBridge.Behavioral.setExpr d).eval (SemanticsBridge.Structural.interpret v.core) σ ρ t)
        (setAt_meaning v w σ τ f hp c ρ e hc t fuel d hd) hc.aliases hc.covers
        (fun r => formulaAt v fuel (c.push r) a ha) (fun _ => formulaAt_built _ _ _ _ _)
        (fun S => sourcePart v σ a (ρ.push S) t p) p
        (fun r S hr => ih _ _ _ (hc.push hr) t a ha p)
      cases p with
      | none => exact hh
      | some b => exact hh
    | quant q d a =>
      have hd : sizeOf d < fuel := by simp_all; omega
      have ha : sizeOf a < fuel := by simp_all; omega
      have hD := setAt_meaning v w σ τ f hp c ρ e hc t fuel d hd
      have hdt := setAt_term v c hc.this.1 (fun i => (hc.lookup i).1) fuel d hd
      have h1 := formulaAt_built v fuel ((c.shift 1).push (.var 0)) a ha
      have h2 := formulaAt_built v fuel ((c.shift 2).push (.var 0)) a ha
      have hr (x : U) := ih _ _ _ (hc.bind x) t a ha none
      have ht (x : U) := ih _ _ _ (hc.bind x) t a ha (some true)
      have hf (x : U) := ih _ _ _ (hc.bind x) t a ha (some false)
      have htwo (x y : U) := ih _ _ _ (hc.bindTwo x y) t a ha none
      dsimp only [part, sourcePart] at hr ht hf htwo
      cases q with
      | all =>
        cases p with
        | none =>
          simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.raw,
            Clafer.Behavioral.Quantifier.eval, Clafer.Behavioral.Observation.sets, hr] using all_unary h1.raw hD
        | some b =>
          cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.denote,
            Clafer.Behavioral.Observation.sets, all_unary h1.positive hD, exists_unary h1.negative hD, ht, hf]
      | some =>
        cases p with
        | none =>
          simpa (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.raw,
            Clafer.Behavioral.Quantifier.eval, Clafer.Behavioral.Observation.sets, hr] using exists_unary h1.raw hD
        | some b =>
          cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.denote,
            Clafer.Behavioral.Observation.sets, exists_unary h1.positive hD, all_unary h1.negative hD, ht, hf]
      | no =>
        cases p with
        | none =>
          simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.raw,
            Clafer.Behavioral.Quantifier.eval, Clafer.Behavioral.Observation.sets,
            all_unary (.unary .neg h1.raw) hD, hr]
        | some b =>
          cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, SemanticsBridge.Behavioral.formula,
            SemanticsBridge.Behavioral.quantifier, Clafer.Behavioral.Formula.denote,
            Clafer.Behavioral.Observation.sets, exists_unary h1.positive hD, all_unary h1.negative hD, ht, hf]
      | one =>
        have hm := one_meaning hp.injective hdt hD h1.raw h2.raw _ hr htwo
        cases p with
        | none => exact hm
        | some b =>
          cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.atomic,
            SemanticsBridge.Behavioral.formula, SemanticsBridge.Behavioral.quantifier,
            Clafer.Behavioral.Formula.denote, Clafer.Behavioral.polarity,
            Clafer.Behavioral.Observation.sets, hm]
      | lone =>
        have hm := lone_meaning hp.injective hdt hD h1.raw h2.raw _ hr htwo
        cases p with
        | none => exact hm
        | some b =>
          cases b <;> simp (maxDischargeDepth := 100) [formulaAt_succ, formulaStep, part, sourcePart, Translation.atomic,
            SemanticsBridge.Behavioral.formula, SemanticsBridge.Behavioral.quantifier,
            Clafer.Behavioral.Formula.denote, Clafer.Behavioral.polarity,
            Clafer.Behavioral.Observation.sets, hm]

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Backend.Alloy.Temporal.Lasso}

-- [proof->req~compiler-behavioral-correctness~1]
/-- Concrete preservation: the only trace premise is the shared identity and
relation representation. No arbitrary observation-adapter agreement is assumed. -/
theorem TraceRep.formula_raw (rep : TraceRep v source target) (w : Nat)
    (c : Context n) (ρ : Clafer.Behavioral.Environment (Fin o) n) (e : Environment)
    (hc : ContextRep v w target.unfold rep.label c ρ e) (t fuel : Nat)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).raw.Holds (schema v) w target.unfold e t ↔
      (SemanticsBridge.Behavioral.formula a).raw (SemanticsBridge.Behavioral.trace source)
        (.sets (SemanticsBridge.Structural.interpret v.core) (SemanticsBridge.Behavioral.trace source)) ρ t :=
  formulaAt_meaning v w _ _ _ (rep.primitiveAgreement w) fuel c ρ e hc t a h none

theorem TraceRep.formula_positive (rep : TraceRep v source target) (w : Nat)
    (c : Context n) (ρ : Clafer.Behavioral.Environment (Fin o) n) (e : Environment)
    (hc : ContextRep v w target.unfold rep.label c ρ e) (t fuel : Nat)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).positive.Holds (schema v) w target.unfold e t ↔
      (SemanticsBridge.Behavioral.formula a).denote (SemanticsBridge.Behavioral.trace source)
        (.sets (SemanticsBridge.Structural.interpret v.core) (SemanticsBridge.Behavioral.trace source)) true ρ t :=
  formulaAt_meaning v w _ _ _ (rep.primitiveAgreement w) fuel c ρ e hc t a h (some true)

theorem TraceRep.formula_negative (rep : TraceRep v source target) (w : Nat)
    (c : Context n) (ρ : Clafer.Behavioral.Environment (Fin o) n) (e : Environment)
    (hc : ContextRep v w target.unfold rep.label c ρ e) (t fuel : Nat)
    (a : IR.Behavioral.Formula k n) (h : sizeOf a < fuel) :
    (formulaAt v fuel c a h).negative.Holds (schema v) w target.unfold e t ↔
      (SemanticsBridge.Behavioral.formula a).denote (SemanticsBridge.Behavioral.trace source)
        (.sets (SemanticsBridge.Structural.interpret v.core) (SemanticsBridge.Behavioral.trace source)) false ρ t :=
  formulaAt_meaning v w _ _ _ (rep.primitiveAgreement w) fuel c ρ e hc t a h (some false)

end ClaferCompiler.Correctness.Behavioral
