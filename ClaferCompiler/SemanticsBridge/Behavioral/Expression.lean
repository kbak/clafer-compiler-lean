module

public import ClaferCompiler.IR.Behavioral.Expression
public import ClaferCompiler.SemanticsBridge.Behavioral.Grouped

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Expression
open IR.Behavioral
open Clafer.Behavioral (Environment Trace PartialObservation)

abbrev Observed (U α : Type) (n : Nat) := Environment U n → Nat → Option α
abbrev Meaning (U : Type) := Clafer.Behavioral.Formula (Observed U Prop) (Observed U (Set U))

def observation : PartialObservation (Observed U Prop) (Observed U (Set U)) U where
  atom a ρ t := a ρ t
  domain a ρ t := a ρ t

/-- A value condition observes its complete original formula. Negation of an
outside formula never rewrites the raw condition or removes its strict domain. -/
def condition (τ : Trace (Fin k) U) (c : Meaning U n) (ρ : Environment U n) (t : Nat) : Option Bool := by
  classical
  exact if c.Defined τ observation ρ t then some (decide (c.raw τ observation.canonical ρ t)) else none

def choose (τ : Trace (Fin k) U) (c : Meaning U n) (yes no : Observed U α n) : Observed U α n :=
  fun ρ t => IR.BehavioralArithmetic.conditional (condition τ c ρ t) (yes ρ t) (no ρ t)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem condition_truth (τ : Trace (Fin k) U) (ρ : Environment U n) (t : Nat) :
    condition τ .truth ρ t = some true := by
  classical
  unfold condition
  split
  · apply congrArg some
    exact @decide_eq_true
      (Clafer.Behavioral.Formula.raw τ observation.canonical .truth ρ t)
      (Classical.propDecidable _) True.intro
  · next h => exact False.elim (h True.intro)

def countObservation (τ : Trace (Fin k) U) (q : Grouped.Count) (arity : Nat)
    (disjoint : Bool) (domain : Observed U (Set U) n) (body : Meaning U (n + arity)) :
    Observed U Prop n := by
  classical
  exact fun ρ t => (domain ρ t).bind fun S =>
    if ∀ a ∈ Grouped.assignments arity disjoint S,
        body.Defined τ observation (Grouped.extend ρ arity a) t then
      some ((Grouped.count q).eval (Grouped.assignments arity disjoint S)
        (fun a => body.raw τ observation.canonical (Grouped.extend ρ arity a) t))
    else none

/-- Context transport changes only `this`; captured values and evaluation time
remain unchanged. The body retains its full strict domain and raw truth. -/
def contextObservation (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (domain : SetExpr k n) (body : Meaning U n) : Observed U Prop n := by
  classical
  exact fun ρ t =>
    let S := (setExpr domain).eval m τ ρ t
    if ∀ x ∈ S, body.Defined τ observation {ρ with this := x} t then
      some (∀ x ∈ S, body.raw τ observation.canonical {ρ with this := x} t)
    else none

-- [impl->req~compiler-behavioral-elaboration~1]
def collection (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Collection k n → Observed U (Set U) n :=
  Expression.Collection.rec
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [impl->req~compiler-behavioral-elaboration~1]
def integer (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Integer k n → Observed U Int n :=
  Expression.Integer.rec
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [impl->req~compiler-behavioral-elaboration~1]
def collections (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Collections k n → Observed U (List (Set U)) n :=
  Expression.Collections.rec
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [impl->req~compiler-behavioral-elaboration~1]
def predicate (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Predicate k n → Observed U Prop n :=
  Expression.Predicate.rec
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [impl->req~compiler-behavioral-elaboration~1]
def atom (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Atom k n → Observed U Prop n :=
  Expression.Atom.rec
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [impl->req~compiler-behavioral-elaboration~1]
def formula (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Expression.Formula k n → Meaning U n :=
  Expression.Collection.rec_1
    (motive_1 := fun n _ => Observed U (Set U) n)
    (motive_2 := fun n _ => Observed U Int n)
    (motive_3 := fun n _ => Observed U (List (Set U)) n)
    (motive_4 := fun n _ => Observed U Prop n)
    (motive_5 := fun n _ => Observed U Prop n)
    (motive_6 := fun n _ => Meaning U n)
    (fun {_} a ρ t => some ((setExpr a).eval m τ ρ t))
    (fun {_} i _ _ => some {R.encode i})
    (fun {_} _ a ρ t => (a ρ t).map (fun i => {R.encode i}))
    (fun {_} op _ a ρ t => (a ρ t).bind ((Primitive.extreme op).select R))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∪ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ∩ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· \ ·) (a ρ t) (b ρ t))
    (fun {_} s _ a ρ t => (a ρ t).map ((step s).image m τ t))
    (fun {_} d _ a ρ t => (a ρ t).map (fun S => {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d}))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} i _ _ => some i)
    (fun {_} _ a ρ t => (a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce R))
    (fun {_} _ a ρ t => (a ρ t).bind R.extract)
    (fun {_} _ a ρ t => ((a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down)
    (fun {_} op _ _ a b ρ t => (BehavioralArithmetic.binary op).eval (a ρ t) (b ρ t))
    (fun {_} _ a ρ t => (a ρ t).map (- ·))
    (fun {_} op _ _ ds body ρ t => (ds ρ t).bind (fun sets =>
      (BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => body (ρ.push {ix.2}) t)))
    (fun {_} _ _ _ c a b => choose τ c a b)
    (fun {_} _ _ => some [])
    (fun {_} _ _ a rest ρ t => Clafer.Constraints.lift₂ List.cons (a ρ t) (rest ρ t))
    (fun {_} _ a ρ t => (a ρ t).map Set.Nonempty)
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· ⊆ ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· = ·) (a ρ t) (b ρ t))
    (fun {_} _ _ a b ρ t => Clafer.Constraints.lift₂ (· < ·) (a ρ t) (b ρ t))
    (fun {_} _ a => a)
    (fun {_} domain _ body => contextObservation m τ domain body)
    (fun {_} left _ right ρ t => (right (.closed ρ.this) t).map
      (fun S => (setExpr left).eval m τ ρ t = S))
    (fun {_} q arity disjoint _ _ domain body => countObservation τ q arity disjoint domain body)
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
    (fun {_} q _ _ d a => .quant (quantifier q) d a)
    (fun {_} _ _ d a => .letSet d a)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem collection_set (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : SetExpr k n) (ρ : Environment U n) (t : Nat) :
    collection m τ R (.set a) ρ t = some ((setExpr a).eval m τ ρ t) := rfl

theorem collection_step (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (s : Step k) (a : Expression.Collection k n)
    (ρ : Environment U n) (t : Nat) :
    collection m τ R (.step s a) ρ t = (collection m τ R a ρ t).map ((step s).image m τ t) := rfl

theorem collection_ite (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (c : Expression.Formula k n)
    (a b : Expression.Collection k n) (ρ : Environment U n) (t : Nat) :
    collection m τ R (.ite c a b) ρ t = IR.BehavioralArithmetic.conditional
      (condition τ (formula m τ R c) ρ t) (collection m τ R a ρ t) (collection m τ R b ρ t) := rfl

theorem integer_ite (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (c : Expression.Formula k n)
    (a b : Expression.Integer k n) (ρ : Environment U n) (t : Nat) :
    integer m τ R (.ite c a b) ρ t = IR.BehavioralArithmetic.conditional
      (condition τ (formula m τ R c) ρ t) (integer m τ R a ρ t) (integer m τ R b ρ t) := rfl

/-- Both branches must have values; subsequent operations see only the selected
value. This is a definedness guarantee, independent of constraint truth. -/
theorem conditional_defined (c : Option Bool) (a b : Option α) :
    (∃ x, IR.BehavioralArithmetic.conditional c a b = some x) ↔
      (∃ p, c = some p) ∧ (∃ x, a = some x) ∧ (∃ y, b = some y) := by
  cases c <;> cases a <;> cases b <;> simp [IR.BehavioralArithmetic.conditional]

/-- Fixed type filtering must not use the current live extent: captured
identities keep their type while absent. -/
theorem ofType_member (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (d : Fin k) (a : Expression.Collection k n)
    (ρ : Environment U n) (t : Nat) (S : Set U) (h : collection m τ R a ρ t = some S) :
    collection m τ R (.ofType d a) ρ t = some {x | x ∈ S ∧ m.Ancestor (τ.identities.directType x) d} := by
  change (collection m τ R a ρ t).map _ = _
  rw [h]; rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem formula_eq_generic (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : Expression.Formula k n) :
    formula m τ R a = Generic.interpret (fun {_} => atom m τ R) (fun {_} => collection m τ R) a := by
  induction a <;> simp_all [formula, atom, collection, Generic.interpret]

def syntaxObservation (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) :
    PartialObservation (Expression.Atom k) (Expression.Collection k) U :=
  Generic.pullback (fun {_} => atom m τ R) (fun {_} => collection m τ R) observation

-- [proof->req~compiler-behavioral-elaboration~1]
theorem normalized_satisfaction (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : Expression.Formula k n)
    (positive : Bool) (fuel : Nat) (enough : sizeOf a < fuel) (ρ : Environment U n) (t : Nat) :
    (formula m τ R a).Satisfies τ observation positive ρ t ↔
      (formula m τ R a).Defined τ observation ρ t ∧
      (formula m τ R (FormulaF.normalize a positive fuel enough)).raw τ observation.canonical ρ t := by
  simp only [formula_eq_generic]
  exact Generic.satisfies_iff_normalized _ _ _ _ _ _ _ _ _ _

end ClaferCompiler.SemanticsBridge.Behavioral.Expression
