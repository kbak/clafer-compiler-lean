module

public import ClaferCompiler.IR.Behavioral.RangeRules

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Expression.Ranges
open Expr BehavioralArithmetic

abbrev Result {α : Type} (P : α → Prop) := Except Structural.Diagnostic {a // P a}
structure Evidence (P : Prop) : Type where
  property : P

abbrev Verified (P : Prop) := Except Structural.Diagnostic (Evidence P)

def rangeError : Structural.Diagnostic :=
  { category := .unsupported, code := "behavioral.integer-range" }

def checkRange (b : Inputs k) (r : Interval) : Verified (r.fits b.width = true) :=
  if h : r.fits b.width = true then .ok ⟨h⟩ else .error rangeError

/-- Observation admission is checked before recursive expansion, including in
vacuous bodies. Whole primitive extents have no finite budget. -/
def checkObservation (allowed : Bool) : Verified (allowed = true) :=
  if h : allowed = true then .ok ⟨h⟩ else
    .error { category := .unsupported, code := "behavioral.infinite-observation" }

structure Pass (b : Inputs k) where
  set : {n : Nat} → (a : SetExpr k n) → (Γ : Context n) → Result (SetBound b Γ a)
  collection : {n : Nat} → (a : Collection k n) → (Γ : Context n) → Result (CollectionBound b Γ a)
  integer : {n : Nat} → (a : Integer k n) → (Γ : Context n) → Result (IntegerBound b Γ a)
  collections : {n : Nat} → (a : Collections k n) → (Γ : Context n) → Result (CollectionsBound b Γ a)
  predicate : {n : Nat} → (a : Predicate k n) → (Γ : Context n) → Verified (PredicateBound b Γ a)
  atom : {n : Nat} → (a : Atom k n) → (Γ : Context n) → Verified (AtomBound b Γ a)
  formula : {n : Nat} → (a : Formula k n) → (Γ : Context n) → Verified (FormulaBound b Γ a)

/-- Each recursive call consumes traversal storage. Exhaustion is an explicit
error and cannot certify an unvisited operand or a vacuous binder body. -/
-- [impl->req~compiler-behavioral-elaboration~1]
-- [proof->req~compiler-behavioral-elaboration~1]
def analyzeStep (b : Inputs k) (next : Pass b) : Pass b where
  set := fun a Γ => by
    cases a with
    | empty => exact .ok ⟨⟨0, ⟨0, 0⟩⟩, .empty⟩
    | this => exact do
      let fits ← checkRange b (b.context).values
      return ⟨b.context, .this fits.property⟩
    | root => exact do
      let fits ← checkRange b (b.root).values
      return ⟨b.root, .root fits.property⟩
    | var i => exact do
      let fits ← checkRange b (Γ[i]).values
      return ⟨Γ[i], .var fits.property⟩
    | extent d => exact do
      let allowed ← checkObservation b.extentAllowed[d]
      let fits ← checkRange b (b.extents[d]).values
      return ⟨b.extents[d], .extent allowed.property fits.property⟩
    | union a c => exact do
      let a ← next.set a Γ
      let c ← next.set c Γ
      return ⟨union a.val c.val, .union a.property c.property⟩
    | inter a c => exact do
      let a ← next.set a Γ
      let c ← next.set c Γ
      return ⟨intersection a.val c.val, .inter a.property c.property⟩
    | diff a c => exact do
      let a ← next.set a Γ
      let c ← next.set c Γ
      return ⟨a.val, .diff a.property c.property⟩
    | step s a => exact do
      let a ← next.set a Γ
      let allowed ← checkObservation (b.stepAllowed s)
      let fits ← checkRange b (b.steps s).values
      return ⟨b.steps s, .step a.property allowed.property fits.property⟩
    | thisStep s => exact do
      let allowed ← checkObservation (b.stepAllowed s)
      let fits ← checkRange b (b.steps s).values
      return ⟨b.steps s, .thisStep allowed.property fits.property⟩
  collection := fun a Γ => by
    cases a with
    | set a => exact do
        let a ← next.set a Γ
        let fits ← checkRange b a.val.values
        return ⟨a.val, .set a.property fits.property⟩
    | literal i => exact do
        let fits ← checkRange b ⟨i, i⟩
        return ⟨⟨1, ⟨i, i⟩⟩, .literal fits.property⟩
    | integer a => exact do
        let a ← next.integer a Γ
        return ⟨⟨1, a.val⟩, .integer a.property⟩
    | extreme op a => exact do
        let a ← next.collection a Γ
        return ⟨⟨min 1 a.val.budget, a.val.values⟩, .extreme a.property⟩
    | union a c => exact do
        let a ← next.collection a Γ
        let c ← next.collection c Γ
        return ⟨union a.val c.val, .union a.property c.property⟩
    | inter a c => exact do
        let a ← next.collection a Γ
        let c ← next.collection c Γ
        return ⟨intersection a.val c.val, .inter a.property c.property⟩
    | diff a c => exact do
        let a ← next.collection a Γ
        let c ← next.collection c Γ
        return ⟨a.val, .diff a.property c.property⟩
    | step s a => exact do
        let a ← next.collection a Γ
        let allowed ← checkObservation (b.stepAllowed s)
        let fits ← checkRange b (b.steps s).values
        return ⟨b.steps s, .step a.property allowed.property fits.property⟩
    | ofType d a => exact do
        let a ← next.collection a Γ
        return ⟨a.val, .ofType a.property⟩
    | ite c a d => exact do
        let c ← next.formula c Γ
        let a ← next.collection a Γ
        let d ← next.collection d Γ
        return ⟨selected a.val d.val, .ite c.property a.property d.property⟩
  integer := fun a Γ => by
    cases a with
    | literal i => exact do
        let fits ← checkRange b ⟨i, i⟩
        return ⟨⟨i, i⟩, .literal fits.property⟩
    | coerce a => exact do
        let a ← next.collection a Γ
        let fits ← checkRange b (setSumRange a.val.budget a.val.values)
        return ⟨setSumRange a.val.budget a.val.values, .coerce a.property fits.property⟩
    | extract a => exact do
        let a ← next.collection a Γ
        let fits ← checkRange b (a.val.values)
        return ⟨a.val.values, .extract a.property fits.property⟩
    | cardinality a => exact do
        let a ← next.collection a Γ
        let fits ← checkRange b (countRange a.val.budget)
        return ⟨countRange a.val.budget, .cardinality a.property fits.property⟩
    | binary op a c => exact do
        let a ← next.integer a Γ
        let c ← next.integer c Γ
        let checked ← validateOperation op b.width a.val c.val
        return ⟨op.range a.val c.val, .binary a.property c.property checked⟩
    | negate a => exact do
        let a ← next.integer a Γ
        let fits ← checkRange b (negateRange a.val)
        return ⟨negateRange a.val, .negate a.property fits.property⟩
    | fold op ds a => exact do
        let ds ← next.collections ds Γ
        let a ← next.integer a (push Γ (singleton (family ds.val)))
        let fits ← checkRange b (foldRange op (family ds.val).budget a.val)
        return ⟨foldRange op (family ds.val).budget a.val, .fold ds.property a.property fits.property⟩
    | ite c a d => exact do
        let c ← next.formula c Γ
        let a ← next.integer a Γ
        let d ← next.integer d Γ
        let fits ← checkRange b (hull a.val d.val)
        return ⟨hull a.val d.val, .ite c.property a.property d.property fits.property⟩
  collections := fun a Γ => by
    cases a with
    | nil => exact do
        return ⟨[], .nil⟩
    | cons a ds => exact do
        let a ← next.collection a Γ
        let ds ← next.collections ds Γ
        return ⟨a.val :: ds.val, .cons a.property ds.property⟩
  predicate := fun a Γ => by
    change Except Structural.Diagnostic (Evidence (PredicateBound b Γ a))
    cases a with
    | inhabited a => exact do
        let a ← next.collection a Γ
        return ⟨.inhabited a.property⟩
    | equal a c => exact do
        let a ← next.collection a Γ
        let c ← next.collection c Γ
        return ⟨.equal a.property c.property⟩
    | subset a c => exact do
        let a ← next.collection a Γ
        let c ← next.collection c Γ
        return ⟨.subset a.property c.property⟩
    | integerEqual a c => exact do
        let a ← next.integer a Γ
        let c ← next.integer c Γ
        return ⟨.integerEqual a.property c.property⟩
    | less a c => exact do
        let a ← next.integer a Γ
        let c ← next.integer c Γ
        return ⟨.less a.property c.property⟩
  atom := fun a Γ => by
    change Except Structural.Diagnostic (Evidence (AtomBound b Γ a))
    cases a with
    | primitive a => exact do
        let a ← next.predicate a Γ
        return ⟨.primitive a.property⟩
    | count q arity disjoint d a => exact do
        let d ← next.collection d Γ
        let a ← next.formula a (extend Γ arity d.val)
        return ⟨.count d.property a.property⟩
  formula := fun a Γ => by
    change Except Structural.Diagnostic (Evidence (FormulaBound b Γ a))
    cases a with
    | truth => exact do
        return ⟨.truth⟩
    | atom a => exact do
        let a ← next.atom a Γ
        return ⟨.atom a.property⟩
    | not a => exact do
        let a ← next.formula a Γ
        return ⟨.not a.property⟩
    | next a => exact do
        let a ← next.formula a Γ
        return ⟨.next a.property⟩
    | eventually a => exact do
        let a ← next.formula a Γ
        return ⟨.eventually a.property⟩
    | always a => exact do
        let a ← next.formula a Γ
        return ⟨.always a.property⟩
    | initially a => exact do
        let a ← next.formula a Γ
        return ⟨.initially a.property⟩
    | «finally» a => exact do
        let a ← next.formula a Γ
        return ⟨.finally a.property⟩
    | and a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.and a.property c.property⟩
    | or a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.or a.property c.property⟩
    | implies a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.implies a.property c.property⟩
    | iff a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.iff a.property c.property⟩
    | xor a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.xor a.property c.property⟩
    | strongUntil a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.strongUntil a.property c.property⟩
    | weakUntil a c => exact do
        let a ← next.formula a Γ
        let c ← next.formula c Γ
        return ⟨.weakUntil a.property c.property⟩
    | ite c a d => exact do
        let c ← next.formula c Γ
        let a ← next.formula a Γ
        let d ← next.formula d Γ
        return ⟨.ite c.property a.property d.property⟩
    | quant q d a => exact do
        let d ← next.collection d Γ
        let a ← next.formula a (push Γ (singleton d.val))
        return ⟨.quant d.property a.property⟩
    | letSet d a => exact do
        let d ← next.collection d Γ
        let a ← next.formula a (push Γ (d.val))
        return ⟨.letSet d.property a.property⟩

def budgetError : Structural.Diagnostic :=
  { category := .unsupported, code := "behavioral.range-budget" }

def analyzeAt (b : Inputs k) : Nat → Pass b :=
  Nat.rec ⟨fun _ _ => .error budgetError, fun _ _ => .error budgetError, fun _ _ => .error budgetError,
    fun _ _ => .error budgetError, fun _ _ => .error budgetError,
    fun _ _ => .error budgetError, fun _ _ => .error budgetError⟩ (fun _ next => analyzeStep b next)

-- [impl->req~compiler-behavioral-elaboration~1]
def analyze (b : Inputs k) (fuel : Nat) (a : Formula k n) (Γ : Context n) : Verified (FormulaBound b Γ a) :=
  if 1 ≤ b.width ∧ b.width ≤ 16 then (analyzeAt b fuel).formula a Γ
  else .error rangeError

end ClaferCompiler.IR.Behavioral.Expression.Ranges
