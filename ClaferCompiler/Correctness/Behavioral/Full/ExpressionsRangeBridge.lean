module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPreservation
public import ClaferCompiler.Correctness.Behavioral.Full.RangesProperties

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral
variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat} {fuel : Nat}

theorem collectionEstimate_certificate (success : collectionEstimate b fuel c a = .ok estimate) :
    Expression.Ranges.CollectionBound b c.estimates a estimate := by
  unfold collectionEstimate at success
  cases run : (Expression.Ranges.analyzeAt b fuel).collection a c.estimates with
  | error err => simp [run] at success
  | ok value =>
    have equal : value.val = estimate := by simpa [run] using success
    exact equal ▸ value.property

theorem integerEstimate_certificate (success : integerEstimate b fuel c a = .ok range) :
    Expression.Ranges.IntegerBound b c.estimates a range := by
  unfold integerEstimate at success
  cases run : (Expression.Ranges.analyzeAt b fuel).integer a c.estimates with
  | error err => simp [run] at success
  | ok value =>
    have equal : value.val = range := by simpa [run] using success
    exact equal ▸ value.property

theorem collection_inside (hm : ModelRows v b s τ σ labels) (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.CollectionBound b c.estimates a estimate)
    (value : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t = some S) :
    S ⊆ observedDomain b.width := by
  have semantic := Ranges.collection_bound hm.ranges hc.ranges bound value
  intro x hx
  cases x with
  | inl x => trivial
  | inr z =>
    apply interval_fits_value _ (Expression.Ranges.collection_fits bound)
    exact semantic.values _ hx ⟨z, rfl⟩

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
