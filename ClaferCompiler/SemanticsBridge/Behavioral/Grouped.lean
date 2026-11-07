module

public import ClaferCompiler.IR.Behavioral.Grouped
public import ClaferCompiler.SemanticsBridge.Behavioral.Primitive

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Grouped
open IR.Behavioral
open Clafer.Behavioral (Environment Trace PartialObservation)

/-- Source order is left-to-right; lexical index zero is the last binder.
The original attachment identity is unchanged. -/
def extend {U : Type} (ρ : Environment U n) (arity : Nat) (assignment : Fin arity → U) :
    Environment U (n + arity) :=
  ⟨ρ.this, fun i => if h : i.val < arity then
    {assignment ⟨arity - (i.val + 1), by omega⟩}
    else ρ.lookup ⟨i.val - arity, by omega⟩⟩

def assignments {U : Type} (arity : Nat) (disjoint : Bool) (domain : Set U) : Set (Fin arity → U) :=
  {a | (∀ i, a i ∈ domain) ∧ (disjoint = true → Function.Injective a)}

def count : Grouped.Count → Clafer.Behavioral.Quantifier
  | .one => .one
  | .lone => .lone

/-- Function atoms are confined to the proof interpretation. They reuse the
upstream formula and partial-observation machinery at every recursive level. -/
abbrev ObservedAtom (U : Type) (n : Nat) := Environment U n → Nat → Option Prop

def observation {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) :
    PartialObservation (ObservedAtom U) (Clafer.Behavioral.CollectionExpr (Fin k)) U where
  atom a ρ t := a ρ t
  domain a ρ t := Clafer.Behavioral.PrimitiveExpression.collection m τ R ρ t a

-- [impl->req~compiler-behavioral-elaboration~1]
def countObservation {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (q : Grouped.Count) (arity : Nat)
    (disjoint : Bool) (domain : Clafer.Behavioral.CollectionExpr (Fin k) n)
    (body : Clafer.Behavioral.Formula (ObservedAtom U)
      (Clafer.Behavioral.CollectionExpr (Fin k)) (n + arity)) : ObservedAtom U n := by
  classical
  exact fun ρ t => (Clafer.Behavioral.PrimitiveExpression.collection m τ R ρ t domain).bind fun S =>
    if ∀ a ∈ assignments arity disjoint S, body.Defined τ (observation m τ R) (extend ρ arity a) t then
      some ((count q).eval (assignments arity disjoint S)
        (fun a => body.raw τ (observation m τ R).canonical (extend ρ arity a) t))
    else none

/-- Use the checked nested datatype recursor directly. Recursive equation
compilation for this nested type would generate a helper rejected by the audit. -/
def atom {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Grouped.Atom k n → ObservedAtom U n :=
  Grouped.Atom.rec
    (motive_1 := fun n _ => ObservedAtom U n)
    (motive_2 := fun n _ => Clafer.Behavioral.Formula (ObservedAtom U)
      (Clafer.Behavioral.CollectionExpr (Fin k)) n)
    (fun {_} a ρ t => (Primitive.atom a).eval m τ R ρ t)
    (fun {_} q arity disjoint domain _ body => countObservation m τ R q arity disjoint
      (Primitive.collection domain) body)
    (fun {_} => .truth)
    (fun {_} _ a => .atom a)
    (fun {_} _ a => .not a)
    (fun {_} _ _ a b => .and a b)
    (fun {_} _ _ a b => .or a b)
    (fun {_} _ _ a b => .implies a b)
    (fun {_} _ _ a b => .iff a b)
    (fun {_} _ _ a b => .xor a b)
    (fun {_} _ _ _ c a b => .ite c a b)
    (fun {_} _ a => .next a)
    (fun {_} _ a => .eventually a)
    (fun {_} _ a => .always a)
    (fun {_} _ _ a b => .strongUntil a b)
    (fun {_} _ _ a b => .weakUntil a b)
    (fun {_} _ a => .initially a)
    (fun {_} _ a => .finally a)
    (fun {_} q d _ a => .quant (quantifier q) (Primitive.collection d) a)
    (fun {_} d _ a => .letSet (Primitive.collection d) a)

def formula {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Grouped.Formula k n →
    Clafer.Behavioral.Formula (ObservedAtom U) (Clafer.Behavioral.CollectionExpr (Fin k)) n :=
  Grouped.Atom.rec_1
    (motive_1 := fun n _ => ObservedAtom U n)
    (motive_2 := fun n _ => Clafer.Behavioral.Formula (ObservedAtom U)
      (Clafer.Behavioral.CollectionExpr (Fin k)) n)
    (fun {_} a ρ t => (Primitive.atom a).eval m τ R ρ t)
    (fun {_} q arity disjoint domain _ body => countObservation m τ R q arity disjoint
      (Primitive.collection domain) body)
    (fun {_} => .truth)
    (fun {_} _ a => .atom a)
    (fun {_} _ a => .not a)
    (fun {_} _ _ a b => .and a b)
    (fun {_} _ _ a b => .or a b)
    (fun {_} _ _ a b => .implies a b)
    (fun {_} _ _ a b => .iff a b)
    (fun {_} _ _ a b => .xor a b)
    (fun {_} _ _ _ c a b => .ite c a b)
    (fun {_} _ a => .next a)
    (fun {_} _ a => .eventually a)
    (fun {_} _ a => .always a)
    (fun {_} _ _ a b => .strongUntil a b)
    (fun {_} _ _ a b => .weakUntil a b)
    (fun {_} _ a => .initially a)
    (fun {_} _ a => .finally a)
    (fun {_} q d _ a => .quant (quantifier q) (Primitive.collection d) a)
    (fun {_} d _ a => .letSet (Primitive.collection d) a)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem atom_count {U : Type} (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (q : Grouped.Count) (arity : Nat)
    (disjoint : Bool) (domain : IR.Behavioral.Primitive.Collection k n)
    (body : Grouped.Formula k (n + arity)) :
    atom m τ R (.count q arity disjoint domain body) =
      countObservation m τ R q arity disjoint (Primitive.collection domain) (formula m τ R body) := rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem extend_this {U : Type} (ρ : Environment U n) (a : Fin arity → U) :
    (extend ρ arity a).this = ρ.this := rfl

theorem extend_local {U : Type} (ρ : Environment U n) (a : Fin arity → U) (i : Fin arity) :
    (extend ρ arity a).lookup ⟨i.val, by omega⟩ =
      {a ⟨arity - (i.val + 1), by omega⟩} := by simp [extend, i.isLt]

theorem extend_outer {U : Type} (ρ : Environment U n) (a : Fin arity → U) (i : Fin n) :
    (extend ρ arity a).lookup ⟨i.val + arity, by omega⟩ = ρ.lookup i := by
  simp [extend]

/-- The shared domain must be defined, and every admissible complete assignment
must have a defined body, regardless of whether that body is true. -/
theorem count_defined_iff {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (q : Grouped.Count) (arity : Nat) (disjoint : Bool) (domain) (body)
    (ρ : Environment U n) (t : Nat) :
    (∃ p, countObservation m τ R q arity disjoint domain body ρ t = some p) ↔
      ∃ S, Clafer.Behavioral.PrimitiveExpression.collection m τ R ρ t domain = some S ∧
        ∀ a ∈ assignments arity disjoint S, body.Defined τ (observation m τ R) (extend ρ arity a) t := by
  classical
  unfold countObservation
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨p, S, hs, hp⟩
    split at hp
    · exact ⟨S, hs, ‹∀ a ∈ assignments arity disjoint S, _›⟩
    · cases hp
  · rintro ⟨S, hs, defined⟩
    refine ⟨(count q).eval (assignments arity disjoint S)
      (fun a => body.raw τ (observation m τ R).canonical (extend ρ arity a) t), S, hs, ?_⟩
    split
    · rfl
    · contradiction

/-- Independent upstream Quantifier.eval counts whole assignments, preserving
classical raw-body truth for both counting forms. -/
theorem count_value {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (q : Grouped.Count) (arity : Nat) (disjoint : Bool) (domain) (body)
    (ρ : Environment U n) (t : Nat) (S : Set U)
    (domainDefined : Clafer.Behavioral.PrimitiveExpression.collection m τ R ρ t domain = some S)
    (defined : ∀ a ∈ assignments arity disjoint S,
      body.Defined τ (observation m τ R) (extend ρ arity a) t) :
    countObservation m τ R q arity disjoint domain body ρ t =
      some ((count q).eval (assignments arity disjoint S)
        (fun a => body.raw τ (observation m τ R).canonical (extend ρ arity a) t)) := by
  simp only [countObservation, domainDefined, Option.bind_some]
  split
  · rfl
  · contradiction

-- [proof->req~compiler-behavioral-elaboration~1]
theorem formula_eq_generic {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U) (a : Grouped.Formula k n) :
    formula m τ R a = Generic.interpret (fun {_} => atom m τ R) (fun {_} => Primitive.collection) a := by
  induction a <;> simp_all [formula, atom, Generic.interpret]

theorem normalized_satisfaction {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (a : Grouped.Formula k n) (positive : Bool) (fuel : Nat) (enough : sizeOf a < fuel)
    (ρ : Environment U n) (t : Nat) :
    (formula m τ R a).Satisfies τ (observation m τ R) positive ρ t ↔
      (formula m τ R a).Defined τ (observation m τ R) ρ t ∧
      (formula m τ R (FormulaF.normalize a positive fuel enough)).raw τ
        (observation m τ R).canonical ρ t := by
  simp only [formula_eq_generic]
  exact Generic.satisfies_iff_normalized _ _ _ _ _ _ _ _ _ _

/-- Model properties keep syntax fixed across traces; only this observation
changes. Use the inherited-reference observed trace for a behavioral model. -/
def syntaxObservation {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U) :
    PartialObservation (IR.Behavioral.Grouped.Atom k) (IR.Behavioral.Primitive.Collection k) U :=
  Generic.pullback (fun {_} => atom m τ R) (fun {_} => Primitive.collection) (observation m τ R)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem syntax_satisfaction {U : Type} (m : Clafer.Semantics.EffectiveCore k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (a : IR.Behavioral.Grouped.Formula k n) (s : Bool) (ρ : Environment U n) (t : Nat) :
    (Generic.interpret (fun x => x) (fun x => x) a).Satisfies τ (syntaxObservation m τ R) s ρ t ↔
      (formula m τ R a).Satisfies τ (observation m τ R) s ρ t := by
  rw [formula_eq_generic]
  exact Generic.satisfies_pullback _ _ _ _ _ _ _ _

end ClaferCompiler.SemanticsBridge.Behavioral.Grouped
