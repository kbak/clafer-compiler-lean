module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaQuantifiers
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open IR.Behavioral
open Backend.Alloy.Behavioral.Full.Expressions

namespace FormulaObservation

theorem letSet {A D : Nat → Type} {C U : Type}
    {σ : Clafer.Behavioral.Trace C U} {O : Clafer.Behavioral.PartialObservation A D U}
    {ρ : Clafer.Behavioral.Environment U n} {d : D n} {S : Set U}
    {a : Clafer.Behavioral.Formula A D (n + 1)}
    (source : O.domain d ρ t = some S)
    (body : FormulaObservation s w τ e t σ O (ρ.push S) a target) :
    FormulaObservation s w τ e t σ O ρ (.letSet d a) target := by
  have canon : O.canonical.domain d ρ t = S := by
    simp [Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete, source]
  have original : (Clafer.Behavioral.Formula.letSet d a).Defined σ O ρ t ↔ a.Defined σ O (ρ.push S) t := by
    simp [Clafer.Behavioral.Formula.Defined, source]
  refine ⟨body.built, body.defined.trans original.symm, ?_, ?_, ?_⟩
  · intro hd; simpa only [Clafer.Behavioral.Formula.raw, canon] using body.raw (original.mp hd)
  · intro hd; simpa only [Clafer.Behavioral.Formula.denote, canon] using body.positive (original.mp hd)
  · intro hd; simpa only [Clafer.Behavioral.Formula.denote, canon] using body.negative (original.mp hd)
end FormulaObservation

namespace Expressions
variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t fuel : Nat} {next : Pass k}

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

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem formula_quantStep (model : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (built : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (domainBound : Expression.Ranges.CollectionBound b c.estimates d estimate)
    (bodyBound : Expression.Ranges.FormulaBound b (Expression.Ranges.push c.estimates (Expression.Ranges.singleton estimate)) a)
    (success : (lowerStep v b fuel next).formula c (.quant q d a) = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers (.quant q d a)) result := by
  change (do
    let estimate ← collectionEstimate b fuel c d
    let domain ← next.collection c d
    partialMapM domain fun relation => do
      let one ← next.formula ((c.shift 1).push (.var 0) (Expression.Ranges.singleton estimate)) a
      let two ← next.formula ((c.shift 2).push (.var 0) (Expression.Ranges.singleton estimate)) a
      pure (Backend.Alloy.Behavioral.Partial.quantify q relation .truth one two)) = .ok result at success
  cases he : collectionEstimate b fuel c d with
  | error error => rw [he] at success; contradiction
  | ok r =>
    have same := Expression.Ranges.collection_unique (collectionEstimate_certificate he) domainBound
    subst r
    cases hd : next.collection c d with
    | error error => rw [he, hd] at success; contradiction
    | ok domain =>
      rw [he, hd] at success
      have observed := ih.collection hc t d domain estimate domainBound hd
      let compileBody := fun relation => do
        let one ← next.formula ((c.shift 1).push (.var 0) (Expression.Ranges.singleton estimate)) a
        let two ← next.formula ((c.shift 2).push (.var 0) (Expression.Ranges.singleton estimate)) a
        pure (Backend.Alloy.Behavioral.Partial.quantify q relation .truth one two)
      change partialMapM domain compileBody = .ok result at success
      refine partialMapM_observation domain compileBody result observed.built ?_ success ?_ ?_
      · intro _ relation body _ hb
        exact (SyntaxBuilt.bind (built.formula _ a) (fun one ho =>
          SyntaxBuilt.bind (built.formula _ a) (fun two ht =>
            SyntaxBuilt.pure (SyntaxBuilt.quantify q relation one two ho ht)))) body hb
      · intro defined
        obtain ⟨S, hs, _⟩ := defined
        exact observed.complete S hs
      · intro relation body hrel hbody
        obtain ⟨S, hS, term, rows⟩ := observed.sound relation hrel
        have semantic := Ranges.collection_bound model.ranges hc.ranges domainBound hS
        have inside := collection_inside model hc domainBound hS
        cases ho : next.formula ((c.shift 1).push (.var 0) (Expression.Ranges.singleton estimate)) a with
        | error error => unfold compileBody at hbody; rw [ho] at hbody; contradiction
        | ok one =>
          cases ht : next.formula ((c.shift 2).push (.var 0) (Expression.Ranges.singleton estimate)) a with
          | error error => unfold compileBody at hbody; rw [ho, ht] at hbody; contradiction
          | ok two =>
            unfold compileBody at hbody
            rw [ho, ht] at hbody
            have same := Except.ok.inj hbody
            subst body
            apply FormulaObservation.quantify q (completionAtom labels).injective term rows hS
              (built.formula _ a one ho) (built.formula _ a two ht)
            · intro x hx
              have context := (hc.shift [completionAtom labels x]).push (.var 0)
                (Expression.Ranges.singleton estimate) {x} (.var 0)
                (fun _ => Mixed.unary_singleton x) (Set.singleton_subset_iff.mpr (inside hx))
                (semantic.singleton_member hx)
              exact ih.formula context t a one bodyBound ho
            · intro x hx y hy
              have context := (hc.shift [completionAtom labels y, completionAtom labels x]).push (.var 0)
                (Expression.Ranges.singleton estimate) {y} (.var 0)
                (fun _ => Mixed.unary_singleton y) (Set.singleton_subset_iff.mpr (inside hy))
                (semantic.singleton_member hy)
              exact ih.formula context t a two bodyBound ht

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem formula_letStep (model : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (built : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (domainBound : Expression.Ranges.CollectionBound b c.estimates d estimate)
    (bodyBound : Expression.Ranges.FormulaBound b (Expression.Ranges.push c.estimates estimate) a)
    (success : (lowerStep v b fuel next).formula c (.letSet d a) = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers (.letSet d a)) result := by
  change (do
    let estimate ← collectionEstimate b fuel c d
    let domain ← next.collection c d
    partialMapM domain fun relation =>
      partialMapM (Backend.Alloy.Behavioral.Full.Value.capture (c.captureAliases estimate.values) relation estimate.budget)
        fun frozen => next.formula (c.push frozen estimate) a) = .ok result at success
  cases he : collectionEstimate b fuel c d with
  | error error => rw [he] at success; contradiction
  | ok r =>
    have same := Expression.Ranges.collection_unique (collectionEstimate_certificate he) domainBound
    subst r
    cases hd : next.collection c d with
    | error error => rw [he, hd] at success; contradiction
    | ok domain =>
      rw [he, hd] at success
      have observed := ih.collection hc t d domain estimate domainBound hd
      let compileBody := fun relation =>
        partialMapM (Backend.Alloy.Behavioral.Full.Value.capture (c.captureAliases estimate.values) relation estimate.budget)
          fun frozen => next.formula (c.push frozen estimate) a
      change partialMapM domain compileBody = .ok result at success
      refine partialMapM_observation domain compileBody result observed.built ?_ success ?_ ?_
      · intro _ relation body _ hb
        exact SyntaxBuilt.partialMapM _ _ (Value.capture_built _ _ _)
          (fun frozen => built.formula (c.push frozen estimate) a) body hb
      · intro defined
        obtain ⟨S, hs, _⟩ := defined
        exact observed.complete S hs
      · intro relation body hrel hbody
        obtain ⟨S, hS, _, rows⟩ := observed.sound relation hrel
        have semantic := Ranges.collection_bound model.ranges hc.ranges domainBound hS
        have inside := collection_inside model hc domainBound hS
        have aliases : ∀ entry ∈ c.captureAliases estimate.values, Stable s b.width τ e entry :=
          fun entry he => hc.aliases entry (List.mem_filter.mp he).1
        refine partialMapM_observation _ _ body (Value.capture_built _ _ _)
          (fun _ frozen result _ hr => built.formula (c.push frozen estimate) a result hr) hbody ?_ ?_
        · intro _
          obtain ⟨frozen, hcap, _⟩ := source_capture_complete (completionAtom labels).injective rows
            (fun entry he => (aliases entry he).term)
            (fun x hx => by
              obtain ⟨entry, he, hrows⟩ := captureAliases_cover hc inside semantic x hx
              exact ⟨entry, he, hrows t⟩) semantic.card
          exact ⟨frozen, hcap⟩
        · intro frozen result hcap hr
          have stable := capture_stable aliases hcap
          have frozenRows := source_capture_frozen rows aliases hcap
          have context := hc.push frozen estimate S stable.term frozenRows inside semantic
          exact FormulaObservation.letSet hS (ih.formula context t a result bodyBound hr)

end Expressions
end ClaferCompiler.Correctness.Behavioral.Full
