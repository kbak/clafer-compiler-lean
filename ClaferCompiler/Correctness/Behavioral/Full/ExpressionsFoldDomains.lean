module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFoldSelections
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open IR.Behavioral
namespace FoldSelections

theorem estimates_fit {b : Expression.Ranges.Inputs k} {Γ : Expression.Ranges.Context n}
    {ds : Expression.Collections k n} {estimates : List Expression.Ranges.CollectionEstimate}
    (bound : Expression.Ranges.CollectionsBound b Γ ds estimates) :
    ∀ estimate ∈ estimates, estimate.values.fits b.width = true := by
  induction estimates generalizing ds with
  | nil => simp
  | cons estimate estimates ih =>
    cases bound with
    | cons head tail =>
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Expression.Ranges.collection_fits head
      · exact ih tail value hv

variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
  {ρ : Clafer.Behavioral.Environment (Completion o) n} {e : Environment} {t : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem domains (hm : ModelRows v b s τ σ labels)
    (hc : LexicalRows b s τ labels c ρ e)
    (cert : Expression.Ranges.CollectionsBound b c.estimates ds estimates)
    (value : SemanticsBridge.Behavioral.Expression.collections (Sets.model v) σ completeIntegers ds ρ t = some sets)
    (represented : List.Forall₂ (fun (r : Rel) S => r.Term ∧
      Mixed.Unary (completionAtom labels) S (r.eval s b.width τ e t)) relations sets) :
    List.Forall₂ (DomainRows labels s b.width τ e t) (relations.zip estimates) sets := by
  have semantic := Ranges.collections_bound hm.ranges hc.ranges cert value
  have fits := estimates_fit cert
  clear cert value
  induction represented generalizing estimates with
  | nil => cases semantic; exact .nil
  | @cons r S rs sets head tail ih =>
    cases semantic with
    | cons hs rest =>
      refine .cons ⟨head.2, hs.card, ?_⟩ (ih rest (fun r hr => fits r (List.mem_cons_of_mem _ hr)))
      intro x hx
      cases x with
      | inl x => trivial
      | inr z =>
        exact interval_fits_value _ (fits _ List.mem_cons_self) (hs.values _ hx ⟨z, rfl⟩)

theorem domains_inside (represented : List.Forall₂ (DomainRows labels s w τ e t) pairs sets) :
    Ranges.unionSets sets ⊆ observedDomain w := by
  have allInside : ∀ S ∈ sets, S ⊆ observedDomain w := by
    induction represented with
    | nil => simp
    | cons h _ ih =>
      intro S hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact h.2.2
      · exact ih S hs
  intro x hx
  obtain ⟨S, hs, hx⟩ := hx
  exact allInside S hs hx

end FoldSelections
end ClaferCompiler.Correctness.Behavioral.Full.Expressions
