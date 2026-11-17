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

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Filtering integer literals by the domain's established interval preserves
its alias cover, without imposing liveness or integer typing on ordinary heads. -/
theorem captureAliases_cover (hc : LexicalRows b s τ labels c ρ e)
    (inside : S ⊆ observedDomain b.width)
    (bound : Ranges.CollectionBound completeIntegers estimate S) (x : Completion o) (hx : x ∈ S) :
    ∃ entry ∈ c.captureAliases estimate.values,
      ∀ t, Mixed.Unary (completionAtom labels) {x} (entry.eval s b.width τ e t) := by
  obtain ⟨entry, he, rows⟩ := hc.cover x (inside hx)
  refine ⟨entry, List.mem_filter.mpr ⟨he, ?_⟩, rows⟩
  change (match entry.code with
    | [.integer i] => estimate.values.lower ≤ i && i ≤ estimate.values.upper
    | _ => true) = true
  split
  · rename_i i code
    have eq : entry = Rel.integer i := by cases entry; simpa [Rel.integer] using code
    subst entry
    have member := (rows 0 [completionAtom labels x]).mpr ⟨x, by simp, rfl⟩
    by_cases fits : Backend.Alloy.fitsInt b.width i = true
    · have same : completionAtom labels x = Atom.integer i := by
        simpa [Rel.eval, Rel.integer, Rel.fold, RelAlgebra.step, relationAlgebra, fits] using member
      have same : x = Sum.inr i := (completionAtom labels).injective same
      subst x
      simpa [completeIntegers, IR.Expr.Interval.Contains] using
        bound.values (Sum.inr i) hx ⟨i, rfl⟩
    · simp [Rel.eval, Rel.integer, Rel.fold, RelAlgebra.step, relationAlgebra, fits] at member
  · rfl

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
