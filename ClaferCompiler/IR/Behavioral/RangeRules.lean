module

public import ClaferCompiler.IR.Behavioral.Expression

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Expression.Ranges
open Expr BehavioralArithmetic

structure CollectionEstimate where
  budget : Nat
  values : Interval
  deriving DecidableEq, Repr

def hull (a b : Interval) : Interval := ⟨min a.lower b.lower, max a.upper b.upper⟩
def union (a b : CollectionEstimate) : CollectionEstimate := ⟨a.budget + b.budget, hull a.values b.values⟩
def intersection (a b : CollectionEstimate) : CollectionEstimate := ⟨min a.budget b.budget, a.values⟩
def selected (a b : CollectionEstimate) : CollectionEstimate := ⟨max a.budget b.budget, hull a.values b.values⟩
def singleton (a : CollectionEstimate) : CollectionEstimate := ⟨1, a.values⟩

/-- Uniform observation bounds supplied by structural scope admission. Step
budgets bound the entire image at any time; integer intervals bound the integer
members only. They do not assert that observations are integer-typed or defined. -/
structure Inputs (k : Nat) where
  width : Nat
  context : CollectionEstimate
  root : CollectionEstimate
  extents : Vector CollectionEstimate k
  steps : Step k → CollectionEstimate

abbrev Context (n : Nat) := Vector CollectionEstimate n

def push (Γ : Context n) (a : CollectionEstimate) : Context (n + 1) :=
  Vector.ofFn fun i => if h : i.val = 0 then a else Γ[(⟨i.val - 1, by omega⟩ : Fin n)]

def extend (Γ : Context n) (arity : Nat) (a : CollectionEstimate) : Context (n + arity) :=
  Vector.ofFn fun i => if h : i.val < arity then singleton a else Γ[(⟨i.val - arity, by omega⟩ : Fin n)]

/-- Independent set-path estimates retain capture bounds and current image
budgets. Both operands are represented even when one determines the estimate. -/
inductive SetBound (b : Inputs k) (Γ : Context n) : SetExpr k n → CollectionEstimate → Prop where
  | empty : SetBound b Γ .empty ⟨0, ⟨0, 0⟩⟩
  | this (fits : b.context.values.fits b.width = true) : SetBound b Γ .this b.context
  | root (fits : b.root.values.fits b.width = true) : SetBound b Γ .root b.root
  | var (fits : Γ[i].values.fits b.width = true) : SetBound b Γ (.var i) Γ[i]
  | extent (fits : b.extents[d].values.fits b.width = true) : SetBound b Γ (.extent d) b.extents[d]
  | union (left : SetBound b Γ a x) (right : SetBound b Γ c y) : SetBound b Γ (.union a c) (union x y)
  | inter (left : SetBound b Γ a x) (right : SetBound b Γ c y) : SetBound b Γ (.inter a c) (intersection x y)
  | diff (left : SetBound b Γ a x) (right : SetBound b Γ c y) : SetBound b Γ (.diff a c) x
  | step (body : SetBound b Γ a x) (fits : (b.steps s).values.fits b.width = true) : SetBound b Γ (.step s a) (b.steps s)
  | thisStep (fits : (b.steps s).values.fits b.width = true) : SetBound b Γ (.thisStep s) (b.steps s)

def family (ds : List CollectionEstimate) : CollectionEstimate :=
  match ds with
  | [] => ⟨0, ⟨0, 0⟩⟩
  | d :: ds => ds.foldl union d

def foldRange (op : Fold) (budget : Nat) (values : Interval) : Interval :=
  match op with | .sum => setSumRange budget values | .product => productRange budget values

mutual
  /-- Constructor rules retain every intermediate obligation, including both
  conditional branches, every Boolean operand and bodies of vacuous binders. -/
  -- [impl->req~compiler-behavioral-elaboration~1]
  inductive CollectionBound (b : Inputs k) : {n : Nat} → Context n → Collection k n → CollectionEstimate → Prop where
    | set (path : SetBound b Γ a r) (fits : r.values.fits b.width = true) : CollectionBound b Γ (.set a) r
    | literal (fits : (⟨i, i⟩ : Interval).fits b.width = true) : CollectionBound b Γ (.literal i) ⟨1, ⟨i, i⟩⟩
    | integer (body : IntegerBound b Γ a r) : CollectionBound b Γ (.integer a) ⟨1, r⟩
    | extreme (body : CollectionBound b Γ a r) : CollectionBound b Γ (.extreme op a) ⟨min 1 r.budget, r.values⟩
    | union (left : CollectionBound b Γ a x) (right : CollectionBound b Γ c y) : CollectionBound b Γ (.union a c) (union x y)
    | inter (left : CollectionBound b Γ a x) (right : CollectionBound b Γ c y) : CollectionBound b Γ (.inter a c) (intersection x y)
    | diff (left : CollectionBound b Γ a x) (right : CollectionBound b Γ c y) : CollectionBound b Γ (.diff a c) x
    | step (body : CollectionBound b Γ a r) (fits : (b.steps s).values.fits b.width = true) : CollectionBound b Γ (.step s a) (b.steps s)
    | ofType (body : CollectionBound b Γ a r) : CollectionBound b Γ (.ofType d a) r
    | ite (condition : FormulaBound b Γ c) (yes : CollectionBound b Γ a x) (no : CollectionBound b Γ d y) :
        CollectionBound b Γ (.ite c a d) (selected x y)
  inductive IntegerBound (b : Inputs k) : {n : Nat} → Context n → Integer k n → Interval → Prop where
    | literal (fits : (⟨i, i⟩ : Interval).fits b.width = true) : IntegerBound b Γ (.literal i) ⟨i, i⟩
    | coerce (body : CollectionBound b Γ a r) (fits : (setSumRange r.budget r.values).fits b.width = true) :
        IntegerBound b Γ (.coerce a) (setSumRange r.budget r.values)
    | extract (body : CollectionBound b Γ a r) (fits : r.values.fits b.width = true) : IntegerBound b Γ (.extract a) r.values
    | cardinality (body : CollectionBound b Γ a r) (fits : (countRange r.budget).fits b.width = true) :
        IntegerBound b Γ (.cardinality a) (countRange r.budget)
    | binary (left : IntegerBound b Γ a x) (right : IntegerBound b Γ c y) (checked : Checked op b.width x y) :
        IntegerBound b Γ (.binary op a c) (op.range x y)
    | negate (body : IntegerBound b Γ a r) (fits : (negateRange r).fits b.width = true) : IntegerBound b Γ (.negate a) (negateRange r)
    | fold (domains : CollectionsBound b Γ ds bounds)
        (body : IntegerBound b (push Γ (singleton (family bounds))) a r)
        (fits : (foldRange op (family bounds).budget r).fits b.width = true) :
        IntegerBound b Γ (.fold op ds a) (foldRange op (family bounds).budget r)
    | ite (condition : FormulaBound b Γ c) (yes : IntegerBound b Γ a x) (no : IntegerBound b Γ d y)
        (fits : (hull x y).fits b.width = true) : IntegerBound b Γ (.ite c a d) (hull x y)
  inductive CollectionsBound (b : Inputs k) : {n : Nat} → Context n → Collections k n → List CollectionEstimate → Prop where
    | nil : CollectionsBound b Γ .nil []
    | cons (head : CollectionBound b Γ a r) (tail : CollectionsBound b Γ ds rs) : CollectionsBound b Γ (.cons a ds) (r :: rs)
  inductive PredicateBound (b : Inputs k) : {n : Nat} → Context n → Predicate k n → Prop where
    | inhabited (body : CollectionBound b Γ a r) : PredicateBound b Γ (.inhabited a)
    | equal (left : CollectionBound b Γ a x) (right : CollectionBound b Γ c y) : PredicateBound b Γ (.equal a c)
    | subset (left : CollectionBound b Γ a x) (right : CollectionBound b Γ c y) : PredicateBound b Γ (.subset a c)
    | integerEqual (left : IntegerBound b Γ a x) (right : IntegerBound b Γ c y) : PredicateBound b Γ (.integerEqual a c)
    | less (left : IntegerBound b Γ a x) (right : IntegerBound b Γ c y) : PredicateBound b Γ (.less a c)
  inductive AtomBound (b : Inputs k) : {n : Nat} → Context n → Atom k n → Prop where
    | primitive (body : PredicateBound b Γ a) : AtomBound b Γ (.primitive a)
    | count (domain : CollectionBound b Γ d r) (body : FormulaBound b (extend Γ arity r) a) :
        AtomBound b Γ (.count q arity disjoint d a)
  inductive FormulaBound (b : Inputs k) : {n : Nat} → Context n → Formula k n → Prop where
    | truth : FormulaBound b Γ .truth
    | atom (body : AtomBound b Γ a) : FormulaBound b Γ (.atom a)
    | not (body : FormulaBound b Γ a) : FormulaBound b Γ (.not a)
    | and (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.and a c)
    | or (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.or a c)
    | implies (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.implies a c)
    | iff (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.iff a c)
    | xor (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.xor a c)
    | ite (condition : FormulaBound b Γ c) (yes : FormulaBound b Γ a) (no : FormulaBound b Γ d) : FormulaBound b Γ (.ite c a d)
    | next (body : FormulaBound b Γ a) : FormulaBound b Γ (.next a)
    | eventually (body : FormulaBound b Γ a) : FormulaBound b Γ (.eventually a)
    | always (body : FormulaBound b Γ a) : FormulaBound b Γ (.always a)
    | strongUntil (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.strongUntil a c)
    | weakUntil (left : FormulaBound b Γ a) (right : FormulaBound b Γ c) : FormulaBound b Γ (.weakUntil a c)
    | initially (body : FormulaBound b Γ a) : FormulaBound b Γ (.initially a)
    | finally (body : FormulaBound b Γ a) : FormulaBound b Γ (.finally a)
    | quant (domain : CollectionBound b Γ d r) (body : FormulaBound b (push Γ (singleton r)) a) : FormulaBound b Γ (.quant q d a)
    | letSet (domain : CollectionBound b Γ d r) (body : FormulaBound b (push Γ r) a) : FormulaBound b Γ (.letSet d a)
end

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Every scalar result in a derivation has passed the width check. Child
premises retain the same guarantee for all intermediates. -/
theorem integer_fits (h : IntegerBound b Γ a r) : r.fits b.width = true := by
  cases h with
  | literal fits => exact fits
  | coerce _ fits => exact fits
  | extract _ fits => exact fits
  | cardinality _ fits => exact fits
  | binary _ _ checked => exact checked.result
  | negate _ fits => exact fits
  | fold _ _ fits => exact fits
  | ite _ _ _ fits => exact fits

end ClaferCompiler.IR.Behavioral.Expression.Ranges
