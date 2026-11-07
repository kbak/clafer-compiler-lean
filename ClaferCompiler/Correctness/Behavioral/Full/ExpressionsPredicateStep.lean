module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPreservation
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPredicates
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPresence

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open IR.Behavioral
open Backend.Alloy.Behavioral.Full.Expressions

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem predicateStep (_model : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.PredicateBound b c.estimates a)
    (success : (lowerStep v b fuel next).predicate c a = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (.atom (SemanticsBridge.Behavioral.Expression.predicate (Sets.model v) σ completeIntegers a)) result := by
  cases a with
  | inhabited a =>
    cases bound with
    | inhabited bound =>
      change (do let value ← next.collection c a; pure (value.predicate (.mult .some))) = .ok result at success
      cases hs : next.collection c a with
      | error error => rw [hs] at success; contradiction
      | ok value =>
        rw [hs] at success
        have same := Except.ok.inj success
        subst result
        have ha := ih.collection hc t a value _ bound hs
        apply FormulaObservation.predicate _ value (.mult .some) ha.built (fun _ => .mult _ _)
        · intro r hr
          obtain ⟨S, hS, _, rows⟩ := ha.sound r hr
          refine ⟨S.Nonempty, ?_, Mixed.unary_some rows⟩
          change (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t).map Set.Nonempty = some S.Nonempty
          rw [hS]; rfl
        · intro P hP
          change (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t).map Set.Nonempty = some P at hP
          obtain ⟨S, hS, _⟩ := Option.map_eq_some_iff.mp hP
          exact ha.complete S hS
  | equal a d =>
    cases bound with
    | equal left right =>
      change (do let x ← next.collection c a; let y ← next.collection c d; pure ((x.pair y).predicate fun pair => .equal pair.1 pair.2)) = .ok result at success
      cases hx : next.collection c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.collection c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          have ha := ih.collection hc t a x _ left hx
          have hd := ih.collection hc t d y _ right hy
          apply FormulaObservation.predicate _ (x.pair y) (fun pair => .equal pair.1 pair.2)
            (Value.pair_built x y ha.built hd.built) (fun _ => .equal _ _)
          · rintro ⟨r, u⟩ pair
            obtain ⟨hr, hu⟩ := (Value.pair_meaning x y ha.built hd.built).mp pair
            obtain ⟨S, hS, _, rS⟩ := ha.sound r hr
            obtain ⟨T, hT, _, uT⟩ := hd.sound u hu
            refine ⟨S = T, ?_, ?_⟩
            · change Clafer.Constraints.lift₂ (· = ·)
                (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t)
                (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t) = some _
              simp [Clafer.Constraints.lift₂, hS, hT]
            · exact Mixed.unary_equal (completionAtom labels).injective rS uT
          · intro P hP
            change Clafer.Constraints.lift₂ (· = ·)
              (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t)
              (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t) = some P at hP
            cases hS : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t with
            | none => simp [hS, Clafer.Constraints.lift₂] at hP
            | some S =>
              cases hT : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t with
              | none => simp [hT, Clafer.Constraints.lift₂] at hP
              | some T =>
                obtain ⟨r, hr⟩ := ha.complete S hS
                obtain ⟨u, hu⟩ := hd.complete T hT
                exact ⟨(r, u), (Value.pair_meaning x y ha.built hd.built).mpr ⟨hr, hu⟩⟩
  | subset a d =>
    cases bound with
    | subset left right =>
      change (do let x ← next.collection c a; let y ← next.collection c d; pure ((x.pair y).predicate fun pair => .subset pair.1 pair.2)) = .ok result at success
      cases hx : next.collection c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.collection c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          have ha := ih.collection hc t a x _ left hx
          have hd := ih.collection hc t d y _ right hy
          apply FormulaObservation.predicate _ (x.pair y) (fun pair => .subset pair.1 pair.2)
            (Value.pair_built x y ha.built hd.built) (fun _ => .subset _ _)
          · rintro ⟨r, u⟩ pair
            obtain ⟨hr, hu⟩ := (Value.pair_meaning x y ha.built hd.built).mp pair
            obtain ⟨S, hS, _, rS⟩ := ha.sound r hr
            obtain ⟨T, hT, _, uT⟩ := hd.sound u hu
            refine ⟨S ⊆ T, ?_, ?_⟩
            · change Clafer.Constraints.lift₂ (· ⊆ ·)
                (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t)
                (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t) = some _
              simp [Clafer.Constraints.lift₂, hS, hT]
            · exact Mixed.unary_subset (completionAtom labels).injective rS uT
          · intro P hP
            change Clafer.Constraints.lift₂ (· ⊆ ·)
              (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t)
              (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t) = some P at hP
            cases hS : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t with
            | none => simp [hS, Clafer.Constraints.lift₂] at hP
            | some S =>
              cases hT : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t with
              | none => simp [hT, Clafer.Constraints.lift₂] at hP
              | some T =>
                obtain ⟨r, hr⟩ := ha.complete S hS
                obtain ⟨u, hu⟩ := hd.complete T hT
                exact ⟨(r, u), (Value.pair_meaning x y ha.built hd.built).mpr ⟨hr, hu⟩⟩
  | integerEqual a d =>
    cases bound with
    | integerEqual left right =>
      change (do let x ← next.integer c a; let y ← next.integer c d; pure ((x.pair y).predicate fun pair => .compare .eq pair.1 pair.2)) = .ok result at success
      cases hx : next.integer c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.integer c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          have ha := ih.integer hc t a x _ left hx
          have hd := ih.integer hc t d y _ right hy
          apply FormulaObservation.predicate _ (x.pair y) (fun pair => .compare .eq pair.1 pair.2)
            (Value.pair_built x y ha.built hd.built) (fun _ => .compare .eq _ _)
          · rintro ⟨r, u⟩ pair
            obtain ⟨hr, hu⟩ := (Value.pair_meaning x y ha.built hd.built).mp pair
            obtain ⟨S, hS, _, rS⟩ := ha.sound r hr
            obtain ⟨T, hT, _, uT⟩ := hd.sound u hu
            refine ⟨S = T, ?_, ?_⟩
            · change Clafer.Constraints.lift₂ (· = ·)
                (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t)
                (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t) = some _
              simp [Clafer.Constraints.lift₂, hS, hT]
            · change (∃ i j, r.eval s b.width τ e t = some i ∧ u.eval s b.width τ e t = some j ∧
                (Backend.Alloy.Comparison.eq).holds i j = true) ↔ _
              simp [rS, uT, Backend.Alloy.Comparison.holds]
          · intro P hP
            change Clafer.Constraints.lift₂ (· = ·)
              (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t)
              (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t) = some P at hP
            cases hS : SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t with
            | none => simp [hS, Clafer.Constraints.lift₂] at hP
            | some S =>
              cases hT : SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t with
              | none => simp [hT, Clafer.Constraints.lift₂] at hP
              | some T =>
                obtain ⟨r, hr⟩ := ha.complete S hS
                obtain ⟨u, hu⟩ := hd.complete T hT
                exact ⟨(r, u), (Value.pair_meaning x y ha.built hd.built).mpr ⟨hr, hu⟩⟩
  | less a d =>
    cases bound with
    | less left right =>
      change (do let x ← next.integer c a; let y ← next.integer c d; pure ((x.pair y).predicate fun pair => .compare .lt pair.1 pair.2)) = .ok result at success
      cases hx : next.integer c a with
      | error error => rw [hx] at success; contradiction
      | ok x =>
        cases hy : next.integer c d with
        | error error => rw [hx, hy] at success; contradiction
        | ok y =>
          rw [hx, hy] at success
          have same := Except.ok.inj success
          subst result
          have ha := ih.integer hc t a x _ left hx
          have hd := ih.integer hc t d y _ right hy
          apply FormulaObservation.predicate _ (x.pair y) (fun pair => .compare .lt pair.1 pair.2)
            (Value.pair_built x y ha.built hd.built) (fun _ => .compare .lt _ _)
          · rintro ⟨r, u⟩ pair
            obtain ⟨hr, hu⟩ := (Value.pair_meaning x y ha.built hd.built).mp pair
            obtain ⟨S, hS, _, rS⟩ := ha.sound r hr
            obtain ⟨T, hT, _, uT⟩ := hd.sound u hu
            refine ⟨S < T, ?_, ?_⟩
            · change Clafer.Constraints.lift₂ (· < ·)
                (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t)
                (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t) = some _
              simp [Clafer.Constraints.lift₂, hS, hT]
            · change (∃ i j, r.eval s b.width τ e t = some i ∧ u.eval s b.width τ e t = some j ∧
                (Backend.Alloy.Comparison.lt).holds i j = true) ↔ _
              simp [rS, uT, Backend.Alloy.Comparison.holds]
          · intro P hP
            change Clafer.Constraints.lift₂ (· < ·)
              (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t)
              (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t) = some P at hP
            cases hS : SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t with
            | none => simp [hS, Clafer.Constraints.lift₂] at hP
            | some S =>
              cases hT : SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers d ρ t with
              | none => simp [hT, Clafer.Constraints.lift₂] at hP
              | some T =>
                obtain ⟨r, hr⟩ := ha.complete S hS
                obtain ⟨u, hu⟩ := hd.complete T hT
                exact ⟨(r, u), (Value.pair_meaning x y ha.built hd.built).mpr ⟨hr, hu⟩⟩

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
