module

public import ClaferCompiler.Frontend.Behavioral.Expressions
public import ClaferCompiler.SemanticsBridge.Behavioral.ExpressionBinders
public import ClaferCompiler.SemanticsBridge.Behavioral.GenericSurface

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Source
open IR.Behavioral
open Clafer.Behavioral (Environment Trace)

/-- A source derivation supplies an upstream formula. The relation depends on
independent name, coercion, operation and binding rules, not the compiler result.
`Expression` supplies partial value observations using upstream primitives. -/
inductive Interprets (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (e : Frontend.Behavioral.Expr) : Expression.Meaning U 0 → Prop where
  | expression {formula : Expression.Formula k 0} (source : Frontend.Behavioral.Expressions.FormulaElaborates v owner e formula) :
      Interprets v owner m τ R e (Expression.formula m τ R formula)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem elaborate_agrees (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) {formula : Expression.Formula k 0}
    (h : Frontend.Behavioral.Expressions.elaborate doc v owner budget e = .ok formula) :
    Interprets v owner m τ R e (Expression.formula m τ R formula) :=
  .expression (Frontend.Behavioral.Expressions.elaborate_sound h)

/-- Composition through executable source elaboration and signed normalization.
The original strict domain is retained; no premise assumes that the constraint
holds. The source relation retains spans, attachment and lexical context. -/
-- [proof->req~compiler-behavioral-elaboration~1]
theorem normalized_agrees (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) {formula : Expression.Formula k 0}
    (h : Frontend.Behavioral.Expressions.elaborate doc v owner budget e = .ok formula)
    (positive : Bool) (fuel : Nat) (enough : sizeOf formula < fuel) (ρ : Environment U 0) (t : Nat) :
    Interprets v owner m τ R e (Expression.formula m τ R formula) ∧
      ((Expression.formula m τ R formula).Satisfies τ Expression.observation positive ρ t ↔
        (Expression.formula m τ R formula).Defined τ Expression.observation ρ t ∧
        (Expression.formula m τ R (FormulaF.normalize formula positive fuel enough)).raw
          τ Expression.observation.canonical ρ t) :=
  ⟨elaborate_agrees m τ R h, Expression.normalized_satisfaction m τ R formula positive fuel enough ρ t⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem patterns_agree (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U)
    (pattern : Surface.Patterns.Pattern (Expression.Formula k n))
    (scope : Surface.Patterns.Scope (Expression.Formula k n)) (ρ : Environment U n) (sign : Bool) (t : Nat) :
    (Expression.formula m τ R (Surface.Patterns.expand pattern scope)).denote
        τ Expression.observation.canonical sign ρ t ↔
      Clafer.Behavioral.Patterns.meaning (τ.ParentPresent ρ.this)
        ((GenericSurface.Patterns.pattern (fun {_} => Expression.atom m τ R)
          (fun {_} => Expression.collection m τ R) pattern).map
          (fun a sign => a.denote τ Expression.observation.canonical sign ρ))
        ((GenericSurface.Patterns.scope (fun {_} => Expression.atom m τ R)
          (fun {_} => Expression.collection m τ R) scope).map
          (fun a sign => a.denote τ Expression.observation.canonical sign ρ)) sign t := by
  rw [Expression.formula_eq_generic]
  exact GenericSurface.Patterns.expand_agrees _ _ _ _ _ _ _ _ _

theorem transitions_agree (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (context : Expression.Formula k n)
    (chain : Surface.Transitions.ChainF (Expression.Atom k) (Expression.Collection k) n)
    (ρ : Environment U n) (sign : Bool) (t : Nat) :
    (Expression.formula m τ R (Surface.Transitions.expand context chain)).denote
        τ Expression.observation.canonical sign ρ t ↔
      (GenericSurface.Transitions.chain (fun {_} => Expression.atom m τ R)
        (fun {_} => Expression.collection m τ R) chain).meaning τ Expression.observation.canonical
        (Expression.formula m τ R context) ρ sign t := by
  simp only [Expression.formula_eq_generic]
  exact GenericSurface.Transitions.expand_agrees _ _ _ _ _ _ _ _ _

end ClaferCompiler.SemanticsBridge.Behavioral.Source
