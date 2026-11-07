module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaValues
public import ClaferCompiler.Correctness.Behavioral.Full.RangesExpressions
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSteps
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersCoercion
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsIntegers

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
namespace Expressions
open IR.Behavioral

/-- Collection families preserve order and repeated domain occurrences. -/
structure CollectionsObservation (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (t : Nat) (f : U → Atom) (source : Option (List (Set U))) (target : Value (List Rel)) : Prop where
  built : Full.Value.Built target
  sound : ∀ rs, Full.Value.Meaning s w τ e t target rs →
    ∃ sets, source = some sets ∧ List.Forall₂
      (fun r S => r.Term ∧ Mixed.Unary f S (r.eval s w τ e t)) rs sets
  complete : ∀ sets, source = some sets → ∃ rs, Full.Value.Meaning s w τ e t target rs

/-- Uniform source/target primitive observations and scope-derived semantic
ranges. These fields contain no expression or property truth agreement. -/
structure ModelRows (v : IR.BehavioralStructural.Validated k)
    (b : Expression.Ranges.Inputs k) (s : Schema) (τ : Trace)
    (σ : Clafer.Behavioral.Trace (Fin k) (Completion o)) (labels : Fin o ↪ Nat) : Prop where
  primitive : Sets.PrimitiveRows v s b.width σ τ (completionAtom labels) (observedDomain b.width)
  ranges : Ranges.InputsBound v b σ completeIntegers
  positive : 0 < b.width
  small : b.width ≤ 16

/-- Frozen source environments and the one fixed finite alias cover, including
all bounded integers. Captures and quantifier shifts preserve these data. -/
structure LexicalRows (b : Expression.Ranges.Inputs k) (s : Schema) (τ : Trace)
    (labels : Fin o ↪ Nat) (c : Backend.Alloy.Behavioral.Full.Expressions.Context n)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) (e : Environment) : Prop where
  context : Sets.ContextRows s b.width τ (completionAtom labels) (observedDomain b.width) c ρ e
  ranges : Ranges.EnvironmentBound b c.estimates completeIntegers ρ
  aliases : ∀ entry ∈ c.lexical.aliases, Stable s b.width τ e entry
  cover : ∀ x ∈ observedDomain b.width, ∃ entry ∈ c.lexical.aliases,
    ∀ t, Mixed.Unary (completionAtom labels) {x} (entry.eval s b.width τ e t)

/-- Constructor induction statement for an executable lowering pass. Every
conclusion uses its actual successful result and original source meaning. -/
structure PassObservation (v : IR.BehavioralStructural.Validated k)
    (b : Expression.Ranges.Inputs k) (s : Schema) (τ : Trace)
    (σ : Clafer.Behavioral.Trace (Fin k) (Completion o)) (labels : Fin o ↪ Nat)
    (pass : Backend.Alloy.Behavioral.Full.Expressions.Pass k) : Prop where
  set : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result, pass.set c a = .ok result →
      result.Term ∧ Mixed.Unary (completionAtom labels)
        ((SemanticsBridge.Behavioral.setExpr a).eval (Sets.model v) σ ρ t)
        (result.eval s b.width τ e t)
  collection : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result estimate,
      Expression.Ranges.CollectionBound b c.estimates a estimate → pass.collection c a = .ok result →
      CollectionObservation s b.width τ e t (completionAtom labels)
        (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers a ρ t) result
  integer : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result range,
      Expression.Ranges.IntegerBound b c.estimates a range → pass.integer c a = .ok result →
      IntegerObservation s b.width τ e t (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers a ρ t) result
  collections : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result estimates,
      Expression.Ranges.CollectionsBound b c.estimates a estimates → pass.collections c a = .ok result →
      CollectionsObservation s b.width τ e t (completionAtom labels)
        (SemanticsBridge.Behavioral.Expression.collections (Sets.model v) σ completeIntegers a ρ t) result
  predicate : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result,
      Expression.Ranges.PredicateBound b c.estimates a → pass.predicate c a = .ok result →
      FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
        (.atom (SemanticsBridge.Behavioral.Expression.predicate (Sets.model v) σ completeIntegers a)) result
  atom : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result,
      Expression.Ranges.AtomBound b c.estimates a → pass.atom c a = .ok result →
      FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
        (.atom (SemanticsBridge.Behavioral.Expression.atom (Sets.model v) σ completeIntegers a)) result
  formula : ∀ {n} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n} {ρ e},
    LexicalRows b s τ labels c ρ e → ∀ t a result,
      Expression.Ranges.FormulaBound b c.estimates a → pass.formula c a = .ok result →
      FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) result

end Expressions
end ClaferCompiler.Correctness.Behavioral.Full
