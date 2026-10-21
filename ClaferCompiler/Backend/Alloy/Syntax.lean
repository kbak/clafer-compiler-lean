module

public import Std

@[expose] public section

namespace ClaferCompiler.Backend.Alloy

/-! Resolved, static M1 target syntax. IDs are list positions, never display names.
The checked API uses extrinsic arity/scope typing; raw terms are untrusted.
No source-language definition or encoder is imported here.
[impl->req~compiler-alloy-core~1] -/

inductive Arity where
  | unary | binary
  deriving DecidableEq, BEq

inductive Multiplicity where
  | set | lone | one | some
  deriving DecidableEq, BEq

structure Signature where
  parent : Option Nat := none
  isAbstract : Bool := false
  multiplicity : Multiplicity := .set
  scalar : Bool := false
  deriving DecidableEq, BEq

structure Field where
  owner : Nat
  target : Nat
  multiplicity : Multiplicity := .set
  deriving DecidableEq, BEq

structure Schema where
  signatures : List Signature
  fields : List Field := []
  deriving DecidableEq, BEq

inductive RelOp where
  | empty (arity : Arity)
  | sig (id : Nat)
  | field (id : Nat)
  | var (index : Nat)
  | union | inter | diff | product | join | transpose | diagonal
  deriving DecidableEq, BEq

/-- Postfix syntax; public builders preserve operand order. Raw code is checked. -/
structure Rel where
  code : List RelOp
  deriving DecidableEq, BEq

def Rel.empty (a : Arity) : Rel := ⟨[.empty a]⟩
def Rel.sig (i : Nat) : Rel := ⟨[.sig i]⟩
def Rel.field (i : Nat) : Rel := ⟨[.field i]⟩
def Rel.var (i : Nat) : Rel := ⟨[.var i]⟩
def Rel.union (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.union]⟩
def Rel.inter (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.inter]⟩
def Rel.diff (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.diff]⟩
def Rel.product (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.product]⟩
def Rel.join (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.join]⟩
def Rel.diagonal (a : Rel) : Rel := ⟨a.code ++ [.diagonal]⟩
def Rel.transpose (a : Rel) : Rel := ⟨a.code ++ [.transpose]⟩

inductive IntegerOp where
  | literal (value : Int)
  | count (rel : Rel)
  | scalar (owner : Nat) (lower upper : Int) (rel : Rel)
  | add | subtract
  deriving DecidableEq, BEq

/-! [impl->req~compiler-target-arithmetic~1] -/

/-- Integer programs share the target's standard-library stack-fold machinery.
Each arithmetic instruction observes its own bounded intermediate value. -/
structure Integer where
  code : List IntegerOp
  deriving DecidableEq, BEq

def Integer.literal (value : Int) : Integer := ⟨[.literal value]⟩
def Integer.count (rel : Rel) : Integer := ⟨[.count rel]⟩
def Integer.scalar (owner : Nat) (lower upper : Int) (rel : Rel) : Integer :=
  ⟨[.scalar owner lower upper rel]⟩
def Integer.add (left right : Integer) : Integer := ⟨left.code ++ right.code ++ [.add]⟩
def Integer.subtract (left right : Integer) : Integer := ⟨left.code ++ right.code ++ [.subtract]⟩

structure IntegerAlgebra (α : Type) where
  literal : Int → α
  count : Rel → α
  scalar : Nat → Int → Int → Rel → α
  add : α → α → α
  subtract : α → α → α

def IntegerAlgebra.step (a : IntegerAlgebra α) (stack : Option (List α))
    (op : IntegerOp) : Option (List α) :=
  match op, stack with
  | .literal n, some xs => some (a.literal n :: xs)
  | .count r, some xs => some (a.count r :: xs)
  | .scalar o lo hi r, some xs => some (a.scalar o lo hi r :: xs)
  | .add, some (y :: x :: xs) => some (a.add x y :: xs)
  | .subtract, some (y :: x :: xs) => some (a.subtract x y :: xs)
  | _, _ => none

def Integer.fold (a : IntegerAlgebra α) (fallback : α) (n : Integer) : α :=
  match n.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

inductive Comparison where
  | eq | lt | le
  deriving DecidableEq, BEq

inductive FormulaOp where
  | truth | falsity
  | equal (left right : Rel)
  | subset (left right : Rel)
  | mult (multiplicity : Multiplicity) (rel : Rel)
  | compare (op : Comparison) (left right : Integer)
  | neg | conj | disj | implies
  | all (domain : Rel)
  | exists_ (domain : Rel)
  deriving DecidableEq, BEq

structure Formula where
  code : List FormulaOp
  deriving DecidableEq, BEq

def Formula.truth : Formula := ⟨[.truth]⟩
def Formula.falsity : Formula := ⟨[.falsity]⟩
def Formula.equal (a b : Rel) : Formula := ⟨[.equal a b]⟩
def Formula.subset (a b : Rel) : Formula := ⟨[.subset a b]⟩
def Formula.mult (m : Multiplicity) (r : Rel) : Formula := ⟨[.mult m r]⟩
def Formula.compare (op : Comparison) (a b : Integer) : Formula := ⟨[.compare op a b]⟩
def Formula.neg (a : Formula) : Formula := ⟨a.code ++ [.neg]⟩
def Formula.conj (a b : Formula) : Formula := ⟨a.code ++ b.code ++ [.conj]⟩
def Formula.disj (a b : Formula) : Formula := ⟨a.code ++ b.code ++ [.disj]⟩
def Formula.implies (a b : Formula) : Formula := ⟨a.code ++ b.code ++ [.implies]⟩
def Formula.all (domain : Rel) (body : Formula) : Formula := ⟨body.code ++ [.all domain]⟩
def Formula.exists_ (domain : Rel) (body : Formula) : Formula := ⟨body.code ++ [.exists_ domain]⟩

/-- Compositional stack algebras use standard-library folds, preserving the
repository's prohibition on generated partial recursive project declarations. -/
structure RelAlgebra (α : Type) where
  empty : Arity → α
  sig : Nat → α
  field : Nat → α
  var : Nat → α
  union : α → α → α
  inter : α → α → α
  diff : α → α → α
  product : α → α → α
  join : α → α → α
  transpose : α → α
  diagonal : α → α

def RelAlgebra.step (a : RelAlgebra α) (stack : Option (List α)) (op : RelOp) : Option (List α) :=
  match op, stack with
  | .empty x, some xs => some (a.empty x :: xs)
  | .sig x, some xs => some (a.sig x :: xs)
  | .field x, some xs => some (a.field x :: xs)
  | .var x, some xs => some (a.var x :: xs)
  | .union, some (y :: x :: xs) => some (a.union x y :: xs)
  | .inter, some (y :: x :: xs) => some (a.inter x y :: xs)
  | .diff, some (y :: x :: xs) => some (a.diff x y :: xs)
  | .product, some (y :: x :: xs) => some (a.product x y :: xs)
  | .join, some (y :: x :: xs) => some (a.join x y :: xs)
  | .transpose, some (x :: xs) => some (a.transpose x :: xs)
  | .diagonal, some (x :: xs) => some (a.diagonal x :: xs)
  | _, _ => none

def Rel.fold (a : RelAlgebra α) (fallback : α) (r : Rel) : α :=
  match r.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

theorem Rel.fold_join (a : RelAlgebra α) (left right : Rel) (x y fallback : α)
    (hl : left.code.foldl a.step (some []) = some [x])
    (hr : right.code.foldl a.step (some [x]) = some [y, x]) :
    (Rel.join left right).fold a fallback = a.join x y := by
  simp [Rel.join, Rel.fold, List.foldl_append, hl, hr, RelAlgebra.step]

structure FormulaAlgebra (α : Type) where
  truth : α
  falsity : α
  equal : Rel → Rel → α
  subset : Rel → Rel → α
  mult : Multiplicity → Rel → α
  compare : Comparison → Integer → Integer → α
  neg : α → α
  conj : α → α → α
  disj : α → α → α
  implies : α → α → α
  all : Rel → α → α
  exists_ : Rel → α → α

def FormulaAlgebra.step (a : FormulaAlgebra α) (stack : Option (List α)) (op : FormulaOp) : Option (List α) :=
  match op, stack with
  | .truth, some xs => some (a.truth :: xs)
  | .falsity, some xs => some (a.falsity :: xs)
  | .equal x y, some xs => some (a.equal x y :: xs)
  | .subset x y, some xs => some (a.subset x y :: xs)
  | .mult m r, some xs => some (a.mult m r :: xs)
  | .compare op x y, some xs => some (a.compare op x y :: xs)
  | .neg, some (x :: xs) => some (a.neg x :: xs)
  | .conj, some (y :: x :: xs) => some (a.conj x y :: xs)
  | .disj, some (y :: x :: xs) => some (a.disj x y :: xs)
  | .implies, some (y :: x :: xs) => some (a.implies x y :: xs)
  | .all r, some (p :: xs) => some (a.all r p :: xs)
  | .exists_ r, some (p :: xs) => some (a.exists_ r p :: xs)
  | _, _ => none

def Formula.fold (a : FormulaAlgebra α) (fallback : α) (p : Formula) : α :=
  match p.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

/-- A checked operand is composed with negation without changing stack shape. -/
theorem Formula.fold_neg (a : FormulaAlgebra α) (p : Formula) (value : α)
    (h : p.code.foldl a.step (some []) = some [value]) (fallback : α) :
    (Formula.neg p).fold a fallback = a.neg value := by
  simp [Formula.neg, Formula.fold, List.foldl_append, h, FormulaAlgebra.step]

/-- The body is closed over an environment; quantification applies that closure. -/
theorem Formula.fold_all (a : FormulaAlgebra α) (p : Formula) (value : α)
    (h : p.code.foldl a.step (some []) = some [value]) (fallback : α) (domain : Rel) :
    (Formula.all domain p).fold a fallback = a.all domain value := by
  simp [Formula.all, Formula.fold, List.foldl_append, h, FormulaAlgebra.step]

structure Scope where
  size : Nat
  exact : Bool := false
  deriving DecidableEq, BEq

inductive CommandKind where
  | run | check
  deriving DecidableEq, BEq

structure Command where
  kind : CommandKind := .run
  body : Formula := .truth
  scopes : List Scope
  bitwidth : Nat
  deriving DecidableEq, BEq

structure Module where
  schema : Schema
  facts : List Formula := []
  command : Command
  deriving DecidableEq, BEq

def Schema.wellFormed (s : Schema) : Bool :=
  (s.signatures.zipIdx.all fun (decl, i) =>
    decl.parent.all fun parent => parent < i) &&
  (s.fields.all fun f => f.owner < s.signatures.length && f.target < s.signatures.length)

def sameArity (left right : Option Arity) : Option Arity := do
  let a ← left
  let b ← right
  if a == b then some a else none

/-- Variables use de Bruijn indices; each quantifier adds a unary singleton. -/
def Rel.typeOf (s : Schema) (depth : Nat) (rel : Rel) : Option Arity :=
  rel.fold {
    empty := some
    sig := fun i => if i < s.signatures.length then some .unary else none
    field := fun i => if i < s.fields.length then some .binary else none
    var := fun i => if i < depth then some .unary else none
    union := sameArity, inter := sameArity, diff := sameArity
    product := fun a b => if a == some .unary && b == some .unary then some .binary else none
    join := fun a b => match a, b with
      | some .unary, some .binary | some .binary, some .unary => some .unary
      | some .binary, some .binary => some .binary
      | _, _ => none
    transpose := fun a => if a == some .binary then some .binary else none
    diagonal := fun a => if a == some .unary then some .binary else none
  } none

def Integer.wellTyped (s : Schema) (depth : Nat) (n : Integer) : Bool :=
  n.fold {
    literal := fun _ => true
    count := fun r => (r.typeOf s depth).isSome
    scalar := fun owner lo hi r =>
      (s.signatures[owner]?).any Signature.scalar && lo ≤ hi &&
        r.typeOf s depth == some .unary
    add := (· && ·), subtract := (· && ·)
  } false

def Formula.wellTyped (s : Schema) (depth : Nat) (formula : Formula) : Bool :=
  formula.fold {
    truth := fun _ => true, falsity := fun _ => true
    equal := fun a b d => (sameArity (a.typeOf s d) (b.typeOf s d)).isSome
    subset := fun a b d => (sameArity (a.typeOf s d) (b.typeOf s d)).isSome
    mult := fun _ r d => (r.typeOf s d).isSome
    compare := fun _ a b d => a.wellTyped s d && b.wellTyped s d
    neg := fun p d => p d
    conj := fun p q d => p d && q d
    disj := fun p q d => p d && q d
    implies := fun p q d => p d && q d
    all := fun domain p d => domain.typeOf s d == some .unary && p (d + 1)
    exists_ := fun domain p d => domain.typeOf s d == some .unary && p (d + 1)
  } (fun _ => false) depth

def Module.wellTyped (m : Module) : Bool :=
  m.schema.wellFormed && m.facts.all (Formula.wellTyped m.schema 0) &&
  m.command.body.wellTyped m.schema 0

end ClaferCompiler.Backend.Alloy
