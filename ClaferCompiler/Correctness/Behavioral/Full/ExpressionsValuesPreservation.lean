module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsExtreme
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersFoldValues

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

namespace CollectionsObservation

theorem nil : CollectionsObservation s b.width τ e t (completionAtom labels) (some []) (.pure []) := by
  refine ⟨Full.Value.pure_built _, ?_, ?_⟩
  · intro rs hr
    have eq := (Full.Value.pure_meaning _ _).mp hr
    subst rs
    exact ⟨[], rfl, .nil⟩
  · intro _ _
    exact ⟨[], (Full.Value.pure_meaning _ _).mpr rfl⟩

theorem cons {sourceHead : Option (Set (Completion o))} {sourceTail : Option (List (Set (Completion o)))}
    {head : Value Rel} {tail : Value (List Rel)}
    (ha : CollectionObservation s b.width τ e t (completionAtom labels) sourceHead head)
    (hb : CollectionsObservation s b.width τ e t (completionAtom labels) sourceTail tail) :
    CollectionsObservation s b.width τ e t (completionAtom labels)
      (Clafer.Constraints.lift₂ List.cons sourceHead sourceTail)
      ((head.pair tail).map fun (a, ds) => a :: ds) := by
  refine ⟨Full.Value.map_built _ _ (Full.Value.pair_built _ _ ha.built hb.built), ?_, ?_⟩
  · intro rs hr
    obtain ⟨⟨r, ds⟩, pair, rfl⟩ := (Full.Value.map_meaning _ _).mp hr
    obtain ⟨hr, hds⟩ := (Full.Value.pair_meaning _ _ ha.built hb.built).mp pair
    obtain ⟨S, hs, ht, rows⟩ := ha.sound r hr
    obtain ⟨sets, hsets, reps⟩ := hb.sound ds hds
    exact ⟨S :: sets, by simp [Clafer.Constraints.lift₂, hs, hsets], .cons ⟨ht, rows⟩ reps⟩
  · intro sets result
    cases hs : sourceHead with
    | none => simp [Clafer.Constraints.lift₂, hs] at result
    | some S =>
      cases hsets : sourceTail with
      | none => simp [Clafer.Constraints.lift₂, hsets] at result
      | some tailSets =>
        obtain ⟨r, hr⟩ := ha.complete S hs
        obtain ⟨rs, hrs⟩ := hb.complete tailSets hsets
        exact ⟨r :: rs, (Full.Value.map_meaning _ _).mpr
          ⟨(r, rs), (Full.Value.pair_meaning _ _ ha.built hb.built).mpr ⟨hr, hrs⟩, rfl⟩⟩
end CollectionsObservation

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem lowerStep_collections (ih : PassObservation v b s τ σ labels next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.CollectionsBound b c.estimates a estimates)
    (success : (lowerStep v b fuel next).collections c a = .ok result) :
    CollectionsObservation s b.width τ e t (completionAtom labels)
      (SemanticsBridge.Behavioral.Expression.collections (Sets.model v) σ completeIntegers a ρ t) result := by
  cases bound with
  | nil => cases success; exact CollectionsObservation.nil
  | @cons _ _ a r ds rs head tail =>
    cases ha : next.collection c a with
    | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
    | ok av =>
      cases hds : next.collections c ds with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha, hds] at success
      | ok dsv =>
        have eq : ((av.pair dsv).map fun (x, xs) => x :: xs) = result := by
          simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha, hds] using success
        subst result
        exact CollectionsObservation.cons (ih.collection hc t a av r head ha)
          (ih.collections hc t ds dsv rs tail hds)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem lowerStep_collection (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.CollectionBound b c.estimates a estimate)
    (success : (lowerStep v b fuel next).collection c a = .ok result) :
    CollectionObservation s b.width τ e t (completionAtom labels)
      (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t) result := by
  cases a with
  | set a =>
    cases ha : next.set c a with
    | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
    | ok value =>
      have eq : Value.pure value = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha] using success
      subst result
      obtain ⟨term, rows⟩ := ih.set hc t a value ha
      exact CollectionObservation.pure term rows
  | literal i =>
    cases bound with
    | literal fits =>
      cases success
      exact CollectionObservation.literal labels i (interval_fits_value _ fits ⟨le_refl _, le_refl _⟩)
  | integer a =>
    cases bound with
    | integer body =>
      cases hr : integerEstimate b fuel c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr] at success
      | ok range =>
        cases ha : next.integer c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] at success
        | ok value =>
          have eq : integerCollection range value = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] using success
          subst result
          have checked := integerEstimate_certificate hr
          apply CollectionObservation.integer labels (ih.integer hc t a value _ body ha) range
          intro z hz
          have valueBound := Ranges.integer_bound hm.ranges hc.ranges checked hz
          exact ⟨valueBound, interval_fits_value _ (Expression.Ranges.integer_fits checked) valueBound⟩
  | extreme op a =>
    cases bound with
    | extreme body =>
      cases hr : collectionEstimate b fuel c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr] at success
      | ok range =>
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] at success
        | ok value =>
          have eq : collectionExtreme op range.values value = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, hr, ha] using success
          subst result
          have checked := collectionEstimate_certificate hr
          apply CollectionObservation.extreme labels op (ih.collection hc t a value _ body ha)
            range.values (Expression.Ranges.collection_fits checked)
          intro S hs z hz
          exact (Ranges.collection_bound hm.ranges hc.ranges checked hs).values _ hz ⟨z, rfl⟩
  | union a d =>
    cases bound with
    | union left right =>
      cases ha : next.collection c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok av =>
        cases hd : next.collection c d with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] at success
        | ok dv =>
          have eq : collectionUnion av dv = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] using success
          subst result
          exact CollectionObservation.union (ih.collection hc t a av _ left ha) (ih.collection hc t d dv _ right hd)
  | inter a d =>
    cases bound with
    | inter left right =>
      cases ha : next.collection c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok av =>
        cases hd : next.collection c d with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] at success
        | ok dv =>
          have eq : collectionInter av dv = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] using success
          subst result
          exact CollectionObservation.inter (completionAtom labels).injective
            (ih.collection hc t a av _ left ha) (ih.collection hc t d dv _ right hd)
  | diff a d =>
    cases bound with
    | diff left right =>
      cases ha : next.collection c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok av =>
        cases hd : next.collection c d with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] at success
        | ok dv =>
          have eq : collectionDiff av dv = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha, hd] using success
          subst result
          exact CollectionObservation.diff (completionAtom labels).injective
            (ih.collection hc t a av _ left ha) (ih.collection hc t d dv _ right hd)
  | step st a =>
    cases bound with
    | step body _ _ =>
      cases hst : finiteStep v st with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hst] at success
      | ok relation =>
        obtain ⟨rfl, finite⟩ := Sets.finiteStep_success v st hst
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hst, ha] at success
        | ok value =>
          have eq : value.map (fun x => .join x (Backend.Alloy.Behavioral.Full.step v st)) = result := by
            simpa [lowerStep, bind, Except.bind, pure, Except.pure, hst, ha] using success
          subst result
          apply CollectionObservation.map (ih.collection hc t a value _ body ha) _ _
            (fun _ ht => .join ht (hm.primitive.step_term st))
          intro S r hs ht rows
          exact Sets.image_rows hm.primitive st finite ht rows (collection_inside hm hc body hs)
  | ofType d a =>
    cases bound with
    | ofType body =>
      cases ha : next.collection c a with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, ha] at success
      | ok value =>
        have eq : value.map (fun x => .inter x (pool v d)) = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, ha] using success
        subst result
        apply CollectionObservation.map (ih.collection hc t a value _ body ha) _ _
          (fun _ ht => .inter ht (pool_term v d))
        intro S r hs ht rows
        have inter := Mixed.unary_inter (completionAtom labels).injective ht (pool_term v d) rows (hm.primitive.pool d e t)
        convert inter using 1
        ext x
        have inside := collection_inside hm hc body hs
        exact ⟨fun hx => ⟨hx.1, hx.2, inside hx.1⟩, fun hx => ⟨hx.1, hx.2.1⟩⟩
  | ite cond a d =>
    cases bound with
    | ite condBound left right =>
      cases hcnd : next.formula c cond with
      | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcnd] at success
      | ok cv =>
        cases ha : next.collection c a with
        | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcnd, ha] at success
        | ok av =>
          cases hd : next.collection c d with
          | error err => simp [lowerStep, bind, Except.bind, pure, Except.pure, hcnd, ha, hd] at success
          | ok dv =>
            have eq : Value.conditional cv av dv = result := by simpa [lowerStep, bind, Except.bind, pure, Except.pure, hcnd, ha, hd] using success
            subst result
            exact CollectionObservation.conditional (ih.formula hc t cond cv condBound hcnd)
              (ih.collection hc t a av _ left ha) (ih.collection hc t d dv _ right hd)

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
