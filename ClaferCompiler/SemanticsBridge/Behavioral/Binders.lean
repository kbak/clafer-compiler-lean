module

public import ClaferCompiler.IR.Behavioral.Binders
public import ClaferCompiler.SemanticsBridge.Behavioral.Grouped

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Binders
open IR.Behavioral
open Clafer.Behavioral (Environment Trace)

theorem diffFold_mem {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (ρ : Environment U (n + 1 + bound)) (t : Nat) (x : U) (indices : List (Fin bound))
    (domain : SetExpr k (n + 1 + bound)) :
    x ∈ (setExpr (indices.foldl (fun d i => .diff d (.var ⟨i.val, by omega⟩)) domain)).eval m τ ρ t ↔
      x ∈ (setExpr domain).eval m τ ρ t ∧
        ∀ i ∈ indices, x ∉ ρ.lookup ⟨i.val, by omega⟩ := by
  induction indices generalizing domain with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons, ih, setExpr, Clafer.Behavioral.SetExpr.eval,
      Set.mem_sdiff, List.mem_cons, forall_eq_or_imp]
    tauto

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The next domain excludes exactly previously chosen identities. In
particular strict definedness is not demanded on inadmissible repetitions. -/
theorem choices_mem {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (ρ : Environment U (n + 1 + bound)) (t : Nat) (x : U) (disjoint : Bool) :
    x ∈ (setExpr (IR.Behavioral.Binders.choices k n bound disjoint)).eval m τ ρ t ↔
      x ∈ ρ.lookup ⟨bound, by omega⟩ ∧
        (disjoint = true → ∀ i : Fin bound, x ∉ ρ.lookup ⟨i.val, by omega⟩) := by
  cases disjoint
  · simp [IR.Behavioral.Binders.choices, setExpr, Clafer.Behavioral.SetExpr.eval]
  · simp only [IR.Behavioral.Binders.choices, ↓reduceIte, diffFold_mem,
      setExpr, Clafer.Behavioral.SetExpr.eval, List.mem_finRange, forall_true_left]

theorem captured_domain {U : Type} (ρ : Environment U n) (S : Set U)
    (assignment : Fin arity → U) :
    (Grouped.extend (ρ.push S) arity assignment).lookup ⟨arity, by omega⟩ = S := by
  simpa using Grouped.extend_outer (ρ.push S) assignment (0 : Fin (n + 1))

theorem captured_outer {U : Type} (ρ : Environment U n) (S : Set U)
    (assignment : Fin arity → U) (i : Fin n) :
    (Grouped.extend (ρ.push S) arity assignment).lookup ⟨i.val + 1 + arity, by omega⟩ =
      ρ.lookup i := by
  simpa using Grouped.extend_outer (ρ.push S) assignment i.succ

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Generated captures and authored binders preserve the original attachment,
and hence the parent lifetime used by all signed temporal operators. -/
theorem attachment_preserved {U : Type} (ρ : Environment U n) (S : Set U)
    (assignment : Fin arity → U) :
    (Grouped.extend (ρ.push S) arity assignment).this = ρ.this := rfl

theorem one_interpret {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (arity : Nat) (disjoint : Bool)
    (domain : Primitive.Collection k n) (body : IR.Behavioral.Grouped.Formula k (n + 1 + arity)) :
    Grouped.formula m τ R (IR.Behavioral.Binders.elaborate .one arity disjoint domain body) =
      Clafer.Behavioral.Formula.letSet (Primitive.collection domain)
        (.atom (Grouped.countObservation m τ R .one arity disjoint (.set (.var 0))
          (Grouped.formula m τ R body))) := rfl

theorem lone_interpret {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (arity : Nat) (disjoint : Bool)
    (domain : Primitive.Collection k n) (body : IR.Behavioral.Grouped.Formula k (n + 1 + arity)) :
    Grouped.formula m τ R (IR.Behavioral.Binders.elaborate .lone arity disjoint domain body) =
      Clafer.Behavioral.Formula.letSet (Primitive.collection domain)
        (.atom (Grouped.countObservation m τ R .lone arity disjoint (.set (.var 0))
          (Grouped.formula m τ R body))) := rfl

end ClaferCompiler.SemanticsBridge.Behavioral.Binders
