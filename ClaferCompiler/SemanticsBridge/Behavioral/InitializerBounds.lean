module

public import ClaferCompiler.Frontend.Behavioral.InitializerBounds
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression
public import ClaferCompiler.SemanticsBridge.BehavioralStructural
public import Clafer.Behavioral.InitializerBounds

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Initializers
open IR.Behavioral
open Frontend.Behavioral.Initializers
open Clafer.Behavioral (Trace Environment)

private theorem bound_scalar (r : IR.Structural.Bounds) (S : Set U)
    (small : singleBound r = true)
    (bound : DPGraph.Predicates.InRange (Structural.bounds r) {x // x ∈ S}) :
    S.Subsingleton := by
  rcases r with ⟨lo, hi⟩
  cases hi with
  | unbounded => simp [singleBound] at small
  | finite hi =>
    have small : hi ≤ 1 := of_decide_eq_true small
    obtain ⟨f⟩ := bound.2
    intro x hx y hy
    have eq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := Fin.ext (by
      have h₁ := (f ⟨x, hx⟩).isLt
      have h₂ := (f ⟨y, hy⟩).isLt
      omega)
    exact congrArg Subtype.val (f.injective eq)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Functional parent/reference navigation and actual declaration fiber bounds
supply scalar leaves. Neither initializer truth nor target scopes are premises. -/
theorem scalarStep_sound (c : IR.BehavioralStructural.Core k) (τ : Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret c) τ)
    (t : Nat) (s : Step k) (small : scalarStep c.structural s = true)
    (S : Set U) (one : S.Subsingleton) :
    ((step s).image (BehavioralStructural.interpret c).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (BehavioralStructural.interpret c) τ) t S).Subsingleton := by
  apply Clafer.Behavioral.Initializers.Bounds.reference_image_scalar one
  intro x _ y z hy hz
  cases s with
  | parent => exact Option.some.inj (hy.1.symm.trans hz.1)
  | deref d => exact valid.refined_reference_agrees hy.2.2 hz.2.2
  | child d =>
    obtain ⟨_, p, parent, live⟩ := (valid.states t).typed.1 d x y hy
    exact bound_scalar (c.structural.get d).localBounds _ small
      ((valid.states t).multiplicities d p parent x live) hy hz

theorem scalarSet_sound (c : IR.BehavioralStructural.Core k) (τ : Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret c) τ)
    (ρ : Environment U n) (t : Nat) (fuel : Nat) (a : SetExpr k n)
    (small : scalarSet c.structural fuel a = true) :
    (Clafer.Behavioral.Structural.eval (BehavioralStructural.interpret c) τ (setExpr a) ρ t).Subsingleton := by
  induction fuel generalizing a with
  | zero => simp [scalarSet] at small
  | succ fuel ih =>
    cases a with
    | empty => exact Set.subsingleton_empty
    | this => exact fun _ hx _ hy => hx.1.trans hy.1.symm
    | root => exact Set.subsingleton_singleton
    | var v => simp [scalarSet] at small
    | union a b => simp [scalarSet] at small
    | inter a b =>
      rcases (by simpa only [scalarSet, Bool.or_eq_true] using small :
        scalarSet c.structural fuel a = true ∨ scalarSet c.structural fuel b = true) with h | h
      · exact fun _ hx _ hy => ih _ h hx.1 hy.1
      · exact fun _ hx _ hy => ih _ h hx.2 hy.2
    | diff a b => exact fun _ hx _ hy => ih _ small hx.1 hy.1
    | step s a =>
      obtain ⟨ha, hs⟩ : scalarSet c.structural fuel a = true ∧ scalarStep c.structural s = true := by
        simpa only [scalarSet, Bool.and_eq_true] using small
      exact scalarStep_sound c τ valid t s hs _ (ih _ ha)
    | thisStep s => exact scalarStep_sound c τ valid t s small _ Set.subsingleton_singleton
    | extent d =>
      rcases (by simpa only [scalarSet, Bool.or_eq_true] using small :
        (d == c.structural.root) = true ∨
          (((c.structural.get d).parent == some c.structural.root) && singleBound (c.structural.get d).localBounds) = true) with root | top
      · have root : d = c.structural.root := eq_of_beq root
        subst d
        exact fun _ hx _ hy => ((valid.states t).root_head _).mp hx |>.trans
          (((valid.states t).root_head _).mp hy).symm
      · obtain ⟨parent, small⟩ : ((c.structural.get d).parent == some c.structural.root) = true ∧
            singleBound (c.structural.get d).localBounds = true := by
          simpa only [Bool.and_eq_true] using top
        have parent : (c.structural.get d).parent = some c.structural.root := eq_of_beq parent
        have subset : (τ.raw (BehavioralStructural.interpret c).toEffectiveCore t).head d ⊆
            {x | (τ.raw (BehavioralStructural.interpret c).toEffectiveCore t).contains d τ.identities.root x} := by
          intro x hx
          obtain ⟨p, hp, _⟩ := (valid.states t).parents d _ parent x hx
          obtain ⟨_, q, hq, pq⟩ := (valid.states t).typed.1 d p x hp
          have eq : q = c.structural.root := Option.some.inj (hq.symm.trans parent)
          subst q
          have eq := ((valid.states t).root_head p).mp pq
          exact eq ▸ hp
        have one := (bound_scalar (c.structural.get d).localBounds _ small
          ((valid.states t).multiplicities d _ parent τ.identities.root
            (((valid.states t).root_head _).mpr rfl)))
        exact fun _ hx _ hy => one (subset hx) (subset hy)

private theorem literal_value (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (ρ : Environment U n) (t : Nat)
    (a : Expression.Collection k n) (h : integerLiteral a = some i) :
    Expression.collection m τ R a ρ t = some {R.encode i} := by
  cases a <;> simp only [integerLiteral] at h
  all_goals try contradiction
  · cases Option.some.inj h; rfl
  · rename_i a
    cases a <;> try contradiction
    cases Option.some.inj h; rfl

private theorem extreme_scalar (op : Clafer.Behavioral.Aggregate.Extreme)
    (R : Clafer.Constraints.IntegerRealization U) (A T : Set U)
    (value : op.select R A = some T) : T.Subsingleton := by
  obtain ⟨finite, typed⟩ := (Clafer.Behavioral.Aggregate.select_defined_iff op R A).mp ⟨T, value⟩
  rcases A.eq_empty_or_nonempty with empty | present
  · subst A
    have eq := Option.some.inj ((Clafer.Behavioral.Aggregate.select_empty op R).symm.trans value)
    exact eq ▸ Set.subsingleton_empty
  · obtain ⟨x, _, hx⟩ := Clafer.Behavioral.Aggregate.select_singleton op R finite typed present
    exact Option.some.inj (hx.symm.trans value) ▸ Set.subsingleton_singleton

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Every admitted RHS has at most one distinct target when defined. Strict
conditionals retain both branches' definedness; bags and arbitrary constraints
cannot furnish scalar evidence. The observation is the compiler's actual
resolved collection evaluator over the valid inherited-reference adapter. -/
theorem scalarAt_sound (c : IR.BehavioralStructural.Core k) (τ : Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret c) τ)
    (R : Clafer.Constraints.IntegerRealization U) (ρ : Environment U n) (t : Nat)
    (fuel : Nat) (a : Expression.Collection k n) (small : scalarAt c.structural fuel a = true)
    {T : Set U} (value : Expression.collection (BehavioralStructural.interpret c).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (BehavioralStructural.interpret c) τ) R a ρ t = some T) :
    T.Subsingleton := by
  let m := (BehavioralStructural.interpret c).toEffectiveCore
  let obs := Clafer.Behavioral.Structural.observed (BehavioralStructural.interpret c) τ
  change Expression.collection m obs R a ρ t = some T at value
  induction fuel generalizing a T with
  | zero => simp [scalarAt] at small
  | succ fuel ih =>
    cases a with
    | set a => exact Option.some.inj value ▸ scalarSet_sound c τ valid ρ t (fuel + 1) a small
    | literal i => exact Option.some.inj value ▸ Set.subsingleton_singleton
    | integer a =>
      change (Expression.integer m obs R a ρ t).map _ = some T at value
      obtain ⟨i, _, eq⟩ := Option.map_eq_some_iff.mp value
      exact eq ▸ Set.subsingleton_singleton
    | extreme op a =>
      change (Expression.collection m obs R a ρ t).bind _ = some T at value
      obtain ⟨A, _, hv⟩ := Option.bind_eq_some_iff.mp value
      exact extreme_scalar (Primitive.extreme op) R A T hv
    | union a b =>
      simp only [scalarAt] at small
      cases ha : integerLiteral a with
      | none => simp [ha] at small
      | some i =>
        cases hb : integerLiteral b with
        | none => simp [ha, hb] at small
        | some j =>
          have eq : i = j := by simpa [ha, hb] using small
          subst j
          change Clafer.Constraints.lift₂ (· ∪ ·)
            (Expression.collection m obs R a ρ t) (Expression.collection m obs R b ρ t) = some T at value
          rw [literal_value m obs R ρ t a ha, literal_value m obs R ρ t b hb] at value
          have eq : ({R.encode i} : Set U) = T := by simpa [Clafer.Constraints.lift₂] using value
          exact eq ▸ Set.subsingleton_singleton
    | inter a b =>
      change Clafer.Constraints.lift₂ (· ∩ ·)
        (Expression.collection m obs R a ρ t) (Expression.collection m obs R b ρ t) = some T at value
      cases ha : Expression.collection m obs R a ρ t <;> cases hb : Expression.collection m obs R b ρ t <;>
        simp only [Clafer.Constraints.lift₂, ha, hb, Option.bind_none, Option.bind_some, Option.map_none,
          Option.map_some, Option.some.injEq, reduceCtorEq] at value
      rename_i A B
      subst T
      rcases (by simpa only [scalarAt, Bool.or_eq_true] using small :
        scalarAt c.structural fuel a = true ∨ scalarAt c.structural fuel b = true) with h | h
      · exact fun _ hx _ hy => ih a h ha hx.1 hy.1
      · exact fun _ hx _ hy => ih b h hb hx.2 hy.2
    | diff a b =>
      change Clafer.Constraints.lift₂ (· \ ·)
        (Expression.collection m obs R a ρ t) (Expression.collection m obs R b ρ t) = some T at value
      cases ha : Expression.collection m obs R a ρ t <;> cases hb : Expression.collection m obs R b ρ t <;>
        simp only [Clafer.Constraints.lift₂, ha, hb, Option.bind_none, Option.bind_some, Option.map_none,
          Option.map_some, Option.some.injEq, reduceCtorEq] at value
      subst T
      exact fun _ hx _ hy => ih a small ha hx.1 hy.1
    | ofType d a =>
      change (Expression.collection m obs R a ρ t).map _ = some T at value
      obtain ⟨A, ha, eq⟩ := Option.map_eq_some_iff.mp value
      subst T
      exact fun _ hx _ hy => ih a small ha hx.1 hy.1
    | step s a =>
      obtain ⟨ha, hs⟩ : scalarAt c.structural fuel a = true ∧ scalarStep c.structural s = true := by
        simpa only [scalarAt, Bool.and_eq_true] using small
      change (Expression.collection m obs R a ρ t).map _ = some T at value
      obtain ⟨A, hv, eq⟩ := Option.map_eq_some_iff.mp value
      exact eq ▸ scalarStep_sound c τ valid t s hs A (ih a ha hv)
    | ite condition a b =>
      obtain ⟨ha, hb⟩ : scalarAt c.structural fuel a = true ∧ scalarAt c.structural fuel b = true := by
        simpa only [scalarAt, Bool.and_eq_true] using small
      change IR.BehavioralArithmetic.conditional
        (Expression.condition obs (Expression.formula m obs R condition) ρ t)
        (Expression.collection m obs R a ρ t) (Expression.collection m obs R b ρ t) = some T at value
      cases hc : Expression.condition obs (Expression.formula m obs R condition) ρ t <;>
        cases va : Expression.collection m obs R a ρ t <;> cases vb : Expression.collection m obs R b ρ t <;>
        simp only [IR.BehavioralArithmetic.conditional, hc, va, vb, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq] at value
      rename_i flag A B
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at value
      · exact value ▸ ih b hb vb
      · exact value ▸ ih a ha va

end ClaferCompiler.SemanticsBridge.Behavioral.Initializers
