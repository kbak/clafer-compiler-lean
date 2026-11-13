module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPredicates
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaQuantifiers

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions IR.Behavioral

variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem LexicalRows.close (hc : LexicalRows b s τ labels c ρ e) :
    LexicalRows b s τ labels c.close (.closed ρ.this) e :=
  ⟨⟨hc.context.this_term, hc.context.this, hc.context.this_inside,
    (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩, ⟨hc.ranges.this, fun i => Fin.elim0 i⟩, hc.aliases, hc.cover⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem equalClosedStep (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels (lowerAt v b fuel depth))
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.AtomBound b c.estimates (.equalClosed a d))
    (success : (lowerStep v b fuel (lowerAt v b fuel depth)).atom c (.equalClosed a d) = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (.atom (SemanticsBridge.Behavioral.Expression.atom (Sets.model v) σ completeIntegers
        (.equalClosed a d))) result := by
  cases bound with
  | equalClosed left right =>
    cases hx : (lowerAt v b fuel depth).set c a with
    | error err => simp [lowerStep, hx, bind, Except.bind] at success
    | ok x =>
      cases hy : (lowerAt v b fuel depth).collection c.close d with
      | error err => simp [lowerStep, hx, hy, bind, Except.bind] at success
      | ok y =>
        have eq : result = y.predicate (fun r => .equal x r) := by
          simpa [lowerStep, hx, hy, bind, Except.bind, pure, Except.pure] using success.symm
        subst result
        obtain ⟨_, rows, _⟩ := Sets.lowerAt_set hm.primitive hc.context b fuel depth a hx
        have hd := ih.collection hc.close t d y _ right hy
        apply FormulaObservation.predicate _ y (fun r => .equal x r) hd.built (fun _ => .equal _ _)
        · intro r hr
          obtain ⟨S, hS, _, rS⟩ := hd.sound r hr
          refine ⟨(SemanticsBridge.Behavioral.setExpr a).eval (Sets.model v) σ ρ t = S, ?_,
            Mixed.unary_equal (completionAtom labels).injective rows rS⟩
          change (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d
            (.closed ρ.this) t).map _ = _
          rw [hS]; rfl
        · intro P hP
          change (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d
            (.closed ρ.this) t).map _ = some P at hP
          obtain ⟨S, hS, _⟩ := Option.map_eq_some_iff.mp hP
          exact hd.complete S hS

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem LexicalRows.inContext (hc : LexicalRows b s τ labels c ρ e)
    (x : Completion o) (inside : x ∈ observedDomain b.width)
    (bound : Ranges.CollectionBound completeIntegers b.context {x}) :
    LexicalRows b s τ labels
      { c.shift 1 with lexical := { (c.shift 1).lexical with this := .var 0 } }
      {ρ with this := x} (completionAtom labels x :: e) := by
  have shifted := hc.shift [completionAtom labels x]
  exact ⟨⟨.var 0, fun _ => Mixed.unary_singleton x, inside,
    shifted.context.lookup_term, shifted.context.lookup, shifted.context.lookup_inside⟩,
    ⟨bound, hc.ranges.lookup⟩, shifted.aliases, shifted.cover⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The generated context binder preserves the entire partial body, including
its temporal cancellation context. Source captures are only shifted in target
syntax and retain their original values. -/
theorem inContextStep (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels (lowerAt v b fuel depth))
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.AtomBound b c.estimates (.inContext d a))
    (success : (lowerStep v b fuel (lowerAt v b fuel depth)).atom c (.inContext d a) = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (.atom (SemanticsBridge.Behavioral.Expression.atom (Sets.model v) σ completeIntegers
        (.inContext d a))) result := by
  classical
  cases bound with
  | inContext domainBound capacity lower upper bodyBound =>
    cases hd : (lowerAt v b fuel depth).set c d with
    | error err => simp [lowerStep, hd, bind, Except.bind] at success
    | ok domain =>
      let nextContext : Context n :=
        { c.shift 1 with lexical := { (c.shift 1).lexical with this := .var 0 } }
      cases ha : (lowerAt v b fuel depth).formula nextContext a with
      | error err =>
        simp [nextContext] at ha
        simp [lowerStep, hd, ha, bind, Except.bind, pure, Except.pure] at success
      | ok body =>
        have eq : result = Backend.Alloy.Behavioral.Partial.atom
            (.all domain body.defined) (.all domain body.truth.raw) := by
          simp [nextContext] at ha
          simpa [lowerStep, hd, ha, bind, Except.bind, pure, Except.pure] using success.symm
        subst result
        obtain ⟨_, rows, inside⟩ := Sets.lowerAt_set hm.primitive hc.context b fuel depth d hd
        let S := (SemanticsBridge.Behavioral.setExpr d).eval (Sets.model v) σ ρ t
        have observed (x : Completion o) (hx : x ∈ S) :=
          ih.formula (hc.inContext x (inside hx) (by
            refine ⟨Set.finite_singleton _, by simpa using capacity, ?_⟩
            intro y hy typed
            have same : y = x := Set.mem_singleton_iff.mp hy
            subst y
            have values := (Ranges.set_bound hm.ranges hc.ranges domainBound t).values x hx typed
            exact ⟨lower.trans values.1, values.2.trans upper⟩))
            t a body bodyBound ha
        have built := (SyntaxBuilt.lowerAt v b fuel depth).formula nextContext a body ha
        apply FormulaObservation.atom (.all domain built.defined) (.all domain built.truth.raw)
        · rw [Mixed.all_unary built.defined rows]
          change (∀ x ∈ S, body.defined.Holds _ _ _ _ _) ↔
            (SemanticsBridge.Behavioral.Expression.contextObservation (Sets.model v) σ d
              (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) ρ t).isSome = true
          unfold SemanticsBridge.Behavioral.Expression.contextObservation
          dsimp only
          split
          · rename_i defined
            simp only [Option.isSome_some, iff_true]
            exact fun x hx => (observed x hx).defined.mpr (defined x hx)
          · rename_i undefined
            simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
            exact fun h => undefined (fun x hx => (observed x hx).defined.mp (h x hx))
        · intro P hP
          change SemanticsBridge.Behavioral.Expression.contextObservation (Sets.model v) σ d
            (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) ρ t = some P at hP
          unfold SemanticsBridge.Behavioral.Expression.contextObservation at hP
          dsimp only at hP
          split at hP
          · rename_i defined
            cases Option.some.inj hP
            rw [Mixed.all_unary built.truth.raw rows]
            exact forall_congr' fun x => imp_congr_right fun hx => (observed x hx).raw (defined x hx)
          · contradiction

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
