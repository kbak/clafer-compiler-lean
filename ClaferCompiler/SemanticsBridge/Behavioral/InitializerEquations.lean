module

public import ClaferCompiler.SemanticsBridge.Behavioral.InitializerTransport

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Initializers
open IR.Behavioral
open Clafer.Behavioral (Trace Environment Formula)

variable (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
  (R : Clafer.Constraints.IntegerRealization U)

/-- Generated equations use positive raw truth. Authored conditions stay inside
closed RHS observations and retain their independent strict temporal domain. -/
def Holds (a : Expression.Meaning U n) (ρ : Environment U n) (t : Nat) : Prop :=
  a.Defined τ Expression.observation ρ t ∧ a.raw τ Expression.observation.canonical ρ t

-- [proof->req~compiler-behavioral-elaboration~1]
theorem equal_closed (left : SetExpr k n) (right : Expression.Collection k 0)
    (ρ : Environment U n) (t : Nat) :
    Holds τ (Expression.formula m τ R (.atom (.equalClosed left right))) ρ t ↔
      Expression.collection m τ R right (.closed ρ.this) t =
        some ((setExpr left).eval m τ ρ t) := by
  change (Formula.atom (Expression.atom m τ R (.equalClosed left right))).Satisfies
    τ Expression.observation true ρ t ↔ _
  rw [Clafer.Behavioral.Initializers.atom_satisfies]
  change (∃ p, (Expression.collection m τ R right (.closed ρ.this) t).map _ = some p ∧ p) ↔ _
  cases h : Expression.collection m τ R right (.closed ρ.this) t with
  | none => simp
  | some S =>
    constructor
    · rintro ⟨p, eq, truth⟩
      have same := Option.some.inj eq
      subst p
      exact congrArg some truth.symm
    · intro eq
      exact ⟨_, rfl, (Option.some.inj eq).symm⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem all_holds (domain : SetExpr k n) (body : Expression.Formula k (n + 1))
    (ρ : Environment U n) (t : Nat) :
    Holds τ (Expression.formula m τ R (.quant .all (.set domain) body)) ρ t ↔
      ∀ x ∈ (setExpr domain).eval m τ ρ t,
        Holds τ (Expression.formula m τ R body) (ρ.push {x}) t := by
  change ((∃ S, some ((setExpr domain).eval m τ ρ t) = some S ∧
    ∀ x ∈ S, _) ∧ ∀ x ∈ (setExpr domain).eval m τ ρ t, _) ↔ _
  constructor
  · rintro ⟨⟨S, eq, defined⟩, truth⟩
    cases Option.some.inj eq
    exact fun x hx => ⟨defined x hx, truth x hx⟩
  · intro h
    exact ⟨⟨_, rfl, fun x hx => (h x hx).1⟩, fun x hx => (h x hx).2⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem context_holds (domain : SetExpr k n) (body : Expression.Formula k n)
    (ρ : Environment U n) (t : Nat) :
    Holds τ (Expression.formula m τ R (.atom (.inContext domain body))) ρ t ↔
      ∀ x ∈ (setExpr domain).eval m τ ρ t,
        Holds τ (Expression.formula m τ R body) {ρ with this := x} t :=
  context_observation m τ domain (Expression.formula m τ R body) ρ t

-- [proof->req~compiler-behavioral-elaboration~1]
theorem initially_holds (body : Expression.Formula k n) (ρ : Environment U n) (t : Nat) :
    Holds τ (Expression.formula m τ R (.initially body)) ρ t ↔
      τ.Starts t ρ.this → Holds τ (Expression.formula m τ R body) ρ t := by
  change ((_ → _) ∧ (_ → _)) ↔ _
  exact (imp_and).symm

-- [proof->req~compiler-behavioral-elaboration~1]
/-- An empty declaration head is a vacuous guard; it never asks for a value
from the complete original RHS. Equality otherwise compares the full target set. -/
theorem aggregate_equation (heads : SetExpr k 0) (targets : SetExpr k 1)
    (right : Expression.Collection k 0) (ρ : Environment U 0) (t : Nat) (S : Set U)
    (target : ∀ x ∈ (setExpr heads).eval m τ ρ t,
      (setExpr targets).eval m τ (ρ.push {x}) t = S) :
    Holds τ (Expression.formula m τ R (.quant .all (.set heads)
      (.atom (.equalClosed targets right)))) ρ t ↔
      Clafer.Behavioral.Initializers.Candidate.Guarded ((setExpr heads).eval m τ ρ t) S
        (Expression.collection m τ R right (.closed ρ.this) t) := by
  rw [all_holds]
  simp only [equal_closed]
  change (∀ x ∈ (setExpr heads).eval m τ ρ t,
    Expression.collection m τ R right (.closed ρ.this) t =
      some ((setExpr targets).eval m τ (ρ.push {x}) t)) ↔ _
  constructor
  · intro h nonempty
    obtain ⟨x, hx⟩ := nonempty
    simpa only [target x hx] using h x hx
  · intro h x hx
    rw [target x hx]
    exact h ⟨x, hx⟩

end ClaferCompiler.SemanticsBridge.Behavioral.Initializers
