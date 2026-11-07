module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersCoercion
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersExtraction
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaValues

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral

variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat} {next : Pass k} {fuel : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem integerStep_of_fold (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next)
    (hc : LexicalRows b s τ labels c ρ e)
    (fold : ∀ op ds a range result,
      Expression.Ranges.IntegerBound b c.estimates (.fold op ds a) range →
      (lowerStep v b fuel next).integer c (.fold op ds a) = .ok result →
      IntegerObservation s b.width τ e t
        (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers (.fold op ds a) ρ t) result)
    (bound : Expression.Ranges.IntegerBound b c.estimates a range)
    (success : (lowerStep v b fuel next).integer c a = .ok result) :
    IntegerObservation s b.width τ e t
      (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t) result := by
  cases a with
  | literal z =>
    cases bound with
    | literal fits =>
      cases success
      exact IntegerObservation.literal (interval_fits_value _ fits ⟨le_refl _, le_refl _⟩)
  | coerce a =>
    cases bound with
    | coerce body sumFits =>
      cases hr : collectionEstimate b fuel c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr] at success
      | ok estimate =>
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] at success
        | ok value =>
          have eq : value.bind (IntegerObservation.coercionBody c.lexical.aliases estimate) = result := by
            unfold IntegerObservation.coercionBody IntegerObservation.coercionGuard IntegerObservation.coercionTerms
            simp only [List.map_map, Function.comp_def]
            simpa [lowerStep, IntegerObservation.coercionBody, IntegerObservation.coercionGuard,
              IntegerObservation.coercionTerms, List.map_map,
              bind, Except.bind, pure, Except.pure, hr, ha] using success
          subst result
          have checked := collectionEstimate_certificate hr
          have same := Expression.Ranges.collection_unique body checked
          have sumFits : (IR.BehavioralArithmetic.setSumRange estimate.budget estimate.values).fits b.width = true := same ▸ sumFits
          apply IntegerObservation.coerce labels (ih.collection hc t a value _ checked ha)
            c.lexical.aliases estimate hm.positive hm.small
            (fun entry he => (hc.aliases entry he).term) ?_ ?_ ?_ ?_ sumFits
          · intro S hs x hx
            obtain ⟨entry, he, rows⟩ := hc.cover x (collection_inside hm hc checked hs hx)
            exact ⟨entry, he, rows t⟩
          · intro S hs; exact (Ranges.collection_bound hm.ranges hc.ranges checked hs).card
          · intro S hs z hz; exact (Ranges.collection_bound hm.ranges hc.ranges checked hs).values _ hz ⟨z, rfl⟩
          · intro S hs z hz; exact collection_inside hm hc checked hs hz
  | extract a =>
    cases bound with
    | extract body _ =>
      cases hr : collectionEstimate b fuel c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr] at success
      | ok estimate =>
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] at success
        | ok value =>
          have eq : integerExtract estimate.values value = result := by
            simpa [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] using success
          subst result
          have checked := collectionEstimate_certificate hr
          apply IntegerObservation.extract labels (ih.collection hc t a value _ body ha)
            estimate.values hm.positive hm.small
          intro S hs z hz
          have zbound := (Ranges.collection_bound hm.ranges hc.ranges checked hs).extract hz
          exact ⟨zbound, interval_fits_value _ (Expression.Ranges.collection_fits checked) zbound⟩
  | cardinality a =>
    cases bound with
    | cardinality body fits =>
      cases hr : collectionEstimate b fuel c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr] at success
      | ok estimate =>
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] at success
        | ok value =>
          have eq : integerCardinality c.lexical.aliases estimate.budget value = result := by
            simpa [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] using success
          subst result
          have checked := collectionEstimate_certificate hr
          have same := Expression.Ranges.collection_unique body checked
          have fits : (IR.BehavioralArithmetic.countRange estimate.budget).fits b.width = true := same ▸ fits
          apply IntegerObservation.cardinality (ih.collection hc t a value _ checked ha)
            (completionAtom labels).injective c.lexical.aliases estimate.budget
            (fun entry he => (hc.aliases entry he).term) ?_ ?_ ?_
          · intro S hs x hx
            obtain ⟨entry, he, rows⟩ := hc.cover x (collection_inside hm hc checked hs hx)
            exact ⟨entry, he, rows t⟩
          · intro S hs; exact (Ranges.collection_bound hm.ranges hc.ranges checked hs).card
          · intro S hs
            exact interval_fits_value _ fits (SemanticsBridge.BehavioralArithmetic.count_range
              (Ranges.collection_bound hm.ranges hc.ranges checked hs).card)
  | binary op a d =>
    cases bound with
    | binary left right checked =>
      cases ha : next.integer c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok av =>
        cases hd : next.integer c d with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] at success
        | ok dv =>
          have eq : integerBinary op av dv = result := by
            simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] using success
          subst result
          exact IntegerObservation.binary (ih.integer hc t a av _ left ha)
            (ih.integer hc t d dv _ right hd) op _ _ checked
            (fun _ hz => Ranges.integer_bound hm.ranges hc.ranges left hz)
            (fun _ hz => Ranges.integer_bound hm.ranges hc.ranges right hz)
  | negate a =>
    cases bound with
    | negate body fits =>
      cases ha : next.integer c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok value =>
        have eq : integerNegate value = result := by
          simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha] using success
        subst result
        apply IntegerObservation.negate (ih.integer hc t a value _ body ha)
        · have pow : 0 < 2 ^ (b.width - 1) := Nat.pow_pos (by decide)
          simp only [Backend.Alloy.fitsInt, Bool.and_eq_true, decide_eq_true_eq,
            Backend.Alloy.minInt, Backend.Alloy.maxInt]
          refine ⟨⟨⟨hm.positive, hm.small⟩, ?_⟩, ?_⟩
          · exact decide_eq_true (neg_nonpos.mpr (Int.natCast_nonneg _))
          · exact decide_eq_true (sub_nonneg.mpr (Int.ofNat_le.mpr pow))
        · intro z hz
          exact interval_fits_value _ fits (SemanticsBridge.BehavioralArithmetic.negate_range
            (Ranges.integer_bound hm.ranges hc.ranges body hz))
  | fold op ds a => exact fold op ds a range result bound success
  | ite cond a d =>
    cases bound with
    | ite condBound left right _ =>
      cases hcond : next.formula c cond with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcond] at success
      | ok cv =>
        cases ha : next.integer c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcond, ha] at success
        | ok av =>
          cases hd : next.integer c d with
          | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcond, ha, hd] at success
          | ok dv =>
            have eq : Value.conditional cv av dv = result := by
              simpa [lowerStep, bind, Except.bind, pure, Except.pure, hcond, ha, hd] using success
            subst result
            exact IntegerObservation.conditional (ih.formula hc t cond cv condBound hcond)
              (ih.integer hc t a av _ left ha) (ih.integer hc t d dv _ right hd)

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
