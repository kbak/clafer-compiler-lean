module

public import ClaferCompiler.Backend.Alloy.Bounds

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Temporal

-- [impl->req~compiler-alloy-temporal-target~1]
/-- Temporal declarations have separate admission; the static schema is unchanged.
Only top-level mutable type signatures can receive explicit Alloy identity scopes. -/
structure Schema where
  declarations : Alloy.Schema
  mutableSignatures : List Bool
  mutableFields : List Bool
  deriving DecidableEq, BEq

/-- Temporal terms reuse the static target's finite postfix representation.
Standard List folds avoid generated partial recursive project helpers. -/
inductive RelOp where
  | empty (arity : Arity) | sig (id : Nat) | field (id : Nat) | var (index : Nat)
  | integer (value : Int) | values (owner : Nat)
  | univ | iden | ints | union | inter | diff | product | join | transpose | prime
  deriving DecidableEq, BEq

structure Rel where
  code : List RelOp
  deriving DecidableEq, BEq

def Rel.empty (x : Arity) : Rel := ⟨[.empty x]⟩
def Rel.sig (x : Nat) : Rel := ⟨[.sig x]⟩
def Rel.field (x : Nat) : Rel := ⟨[.field x]⟩
def Rel.var (x : Nat) : Rel := ⟨[.var x]⟩
def Rel.univ : Rel := ⟨[.univ]⟩
def Rel.iden : Rel := ⟨[.iden]⟩
def Rel.ints : Rel := ⟨[.ints]⟩
def Rel.integer (n : Int) : Rel := ⟨[.integer n]⟩
def Rel.values (owner : Nat) : Rel := ⟨[.values owner]⟩
def Rel.union (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.union]⟩
def Rel.inter (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.inter]⟩
def Rel.diff (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.diff]⟩
def Rel.product (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.product]⟩
def Rel.join (a b : Rel) : Rel := ⟨a.code ++ b.code ++ [.join]⟩
def Rel.transpose (a : Rel) : Rel := ⟨a.code ++ [.transpose]⟩
def Rel.prime (a : Rel) : Rel := ⟨a.code ++ [.prime]⟩

structure RelAlgebra (α : Type) where
  empty : Arity → α
  sig : Nat → α
  field : Nat → α
  var : Nat → α
  univ : α
  iden : α
  ints : α
  integer : Int → α
  values : Nat → α
  union : α → α → α
  inter : α → α → α
  diff : α → α → α
  product : α → α → α
  join : α → α → α
  transpose : α → α
  prime : α → α

def RelAlgebra.step (a : RelAlgebra α) (stack : Option (List α)) (op : RelOp) : Option (List α) :=
  match op, stack with
  | .empty x, some xs => some (a.empty x :: xs)
  | .sig x, some xs => some (a.sig x :: xs)
  | .field x, some xs => some (a.field x :: xs)
  | .var x, some xs => some (a.var x :: xs)
  | .univ, some xs => some (a.univ :: xs)
  | .iden, some xs => some (a.iden :: xs)
  | .ints, some xs => some (a.ints :: xs)
  | .integer n, some xs => some (a.integer n :: xs)
  | .values n, some xs => some (a.values n :: xs)
  | .union, some (y :: x :: xs) => some (a.union x y :: xs)
  | .inter, some (y :: x :: xs) => some (a.inter x y :: xs)
  | .diff, some (y :: x :: xs) => some (a.diff x y :: xs)
  | .product, some (y :: x :: xs) => some (a.product x y :: xs)
  | .join, some (y :: x :: xs) => some (a.join x y :: xs)
  | .transpose, some (x :: xs) => some (a.transpose x :: xs)
  | .prime, some (x :: xs) => some (a.prime x :: xs)
  | _, _ => none

def Rel.fold (a : RelAlgebra α) (fallback : α) (r : Rel) : α :=
  match r.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

inductive IntegerOp where
  | literal (value : Int) | count (rel : Rel)
  | scalar (lower upper : Int) (rel : Rel) | add | subtract
  | multiply | divide | remainder
  deriving DecidableEq, BEq

structure Integer where
  code : List IntegerOp
  deriving DecidableEq, BEq

def Integer.literal (n : Int) : Integer := ⟨[.literal n]⟩
def Integer.count (r : Rel) : Integer := ⟨[.count r]⟩
def Integer.scalar (lo hi : Int) (r : Rel) : Integer := ⟨[.scalar lo hi r]⟩
def Integer.add (a b : Integer) : Integer := ⟨a.code ++ b.code ++ [.add]⟩
def Integer.subtract (a b : Integer) : Integer := ⟨a.code ++ b.code ++ [.subtract]⟩
def Integer.multiply (a b : Integer) : Integer := ⟨a.code ++ b.code ++ [.multiply]⟩
def Integer.divide (a b : Integer) : Integer := ⟨a.code ++ b.code ++ [.divide]⟩
def Integer.remainder (a b : Integer) : Integer := ⟨a.code ++ b.code ++ [.remainder]⟩

structure IntegerAlgebra (α : Type) where
  literal : Int → α
  count : Rel → α
  scalar : Int → Int → Rel → α
  add : α → α → α
  subtract : α → α → α
  multiply : α → α → α
  divide : α → α → α
  remainder : α → α → α

def IntegerAlgebra.step (a : IntegerAlgebra α) (stack : Option (List α)) (op : IntegerOp) : Option (List α) :=
  match op, stack with
  | .literal n, some xs => some (a.literal n :: xs)
  | .count r, some xs => some (a.count r :: xs)
  | .scalar lo hi r, some xs => some (a.scalar lo hi r :: xs)
  | .add, some (y :: x :: xs) => some (a.add x y :: xs)
  | .subtract, some (y :: x :: xs) => some (a.subtract x y :: xs)
  | .multiply, some (y :: x :: xs) => some (a.multiply x y :: xs)
  | .divide, some (y :: x :: xs) => some (a.divide x y :: xs)
  | .remainder, some (y :: x :: xs) => some (a.remainder x y :: xs)
  | _, _ => none

def Integer.fold (a : IntegerAlgebra α) (fallback : α) (n : Integer) : α :=
  match n.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

inductive Unary where
  | neg | after | always | eventually | before | once | historically
  deriving DecidableEq, BEq

inductive Binary where
  | conj | disj | implies | until | releases | since | triggered
  deriving DecidableEq, BEq

inductive FormulaOp where
  | truth | falsity
  | equal (a b : Rel) | subset (a b : Rel) | mult (m : Multiplicity) (r : Rel)
  | compare (op : Comparison) (a b : Integer)
  | unary (op : Unary) | binary (op : Binary)
  | all (domain : Rel) | exists_ (domain : Rel)
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
def Formula.unary (op : Unary) (p : Formula) : Formula := ⟨p.code ++ [.unary op]⟩
def Formula.binary (op : Binary) (p q : Formula) : Formula := ⟨p.code ++ q.code ++ [.binary op]⟩
def Formula.all (r : Rel) (p : Formula) : Formula := ⟨p.code ++ [.all r]⟩
def Formula.exists_ (r : Rel) (p : Formula) : Formula := ⟨p.code ++ [.exists_ r]⟩

structure FormulaAlgebra (α : Type) where
  truth : α
  falsity : α
  equal : Rel → Rel → α
  subset : Rel → Rel → α
  mult : Multiplicity → Rel → α
  compare : Comparison → Integer → Integer → α
  unary : Unary → α → α
  binary : Binary → α → α → α
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
  | .unary op, some (p :: xs) => some (a.unary op p :: xs)
  | .binary op, some (q :: p :: xs) => some (a.binary op p q :: xs)
  | .all r, some (p :: xs) => some (a.all r p :: xs)
  | .exists_ r, some (p :: xs) => some (a.exists_ r p :: xs)
  | _, _ => none

def Formula.fold (a : FormulaAlgebra α) (fallback : α) (p : Formula) : α :=
  match p.code.foldl a.step (some []) with
  | some [value] => value
  | _ => fallback

/-- Public builders produce well-shaped programs; raw instruction lists may not.
This predicate is independent of truth, binding and arithmetic admission. -/
inductive Formula.Built : Formula → Prop where
  | truth : Built .truth
  | falsity : Built .falsity
  | equal (a b : Rel) : Built (.equal a b)
  | subset (a b : Rel) : Built (.subset a b)
  | mult (m : Multiplicity) (r : Rel) : Built (.mult m r)
  | compare (op : Comparison) (a b : Integer) : Built (.compare op a b)
  | unary (op : Unary) {p : Formula} : Built p → Built (.unary op p)
  | binary (op : Binary) {p q : Formula} : Built p → Built q → Built (.binary op p q)
  | all (r : Rel) {p : Formula} : Built p → Built (.all r p)
  | exists_ (r : Rel) {p : Formula} : Built p → Built (.exists_ r p)

-- [proof->req~compiler-alloy-temporal-target~1]
theorem Formula.Built.stack {p : Formula} (hp : p.Built) (a : FormulaAlgebra α) :
    ∃ value, ∀ stack, p.code.foldl a.step (some stack) = some (value :: stack) := by
  induction hp with
  | truth => exact ⟨a.truth, fun _ => rfl⟩
  | falsity => exact ⟨a.falsity, fun _ => rfl⟩
  | equal r s => exact ⟨a.equal r s, fun _ => rfl⟩
  | subset r s => exact ⟨a.subset r s, fun _ => rfl⟩
  | mult m r => exact ⟨a.mult m r, fun _ => rfl⟩
  | compare op r s => exact ⟨a.compare op r s, fun _ => rfl⟩
  | unary op _ ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨a.unary op v, fun _ => by simp [Formula.unary, List.foldl_append, hv, FormulaAlgebra.step]⟩
  | binary op _ _ ihp ihq =>
    obtain ⟨v, hv⟩ := ihp
    obtain ⟨w, hw⟩ := ihq
    exact ⟨a.binary op v w, fun _ => by simp [Formula.binary, List.foldl_append, hv, hw, FormulaAlgebra.step]⟩
  | all r _ ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨a.all r v, fun _ => by simp [Formula.all, List.foldl_append, hv, FormulaAlgebra.step]⟩
  | exists_ r _ ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨a.exists_ r v, fun _ => by simp [Formula.exists_, List.foldl_append, hv, FormulaAlgebra.step]⟩

theorem Formula.fold_unary (a : FormulaAlgebra α) (fallback : α) (op : Unary)
    (p : Formula) (hp : p.Built) :
    (Formula.unary op p).fold a fallback = a.unary op (p.fold a fallback) := by
  obtain ⟨v, hv⟩ := hp.stack a
  simp [Formula.fold, Formula.unary, List.foldl_append, hv, FormulaAlgebra.step]

theorem Formula.fold_binary (a : FormulaAlgebra α) (fallback : α) (op : Binary)
    (p q : Formula) (hp : p.Built) (hq : q.Built) :
    (Formula.binary op p q).fold a fallback = a.binary op (p.fold a fallback) (q.fold a fallback) := by
  obtain ⟨v, hv⟩ := hp.stack a
  obtain ⟨w, hw⟩ := hq.stack a
  simp [Formula.fold, Formula.binary, List.foldl_append, hv, hw, FormulaAlgebra.step]

/-- Alloy has no weak-until token. Keep its standard expansion in the AST. -/
def Formula.weakUntil (p q : Formula) : Formula :=
  .binary .disj (.binary .until p q) (.unary .always p)

/-- Presence now with no presence at the actual predecessor, including time zero. -/
def Formula.birth (presence : Formula) : Formula :=
  .binary .conj presence (.unary .neg (.unary .before presence))

structure Command where
  kind : CommandKind := .run
  body : Formula := .truth
  scopes : List Scope
  bitwidth : Nat
  minSteps : Nat
  maxSteps : Nat
  deriving DecidableEq, BEq

structure Module where
  schema : Schema
  /-- Facts are initial formulas. Recurrence requires an explicit `always`. -/
  facts : List Formula := []
  command : Command
  deriving DecidableEq, BEq

-- [impl->req~compiler-alloy-temporal-target~1]
def Rel.typeOf (s : Schema) (depth : Nat) (r : Rel) : Option Arity :=
  r.fold {
    empty := some
    sig := fun i => if i < s.declarations.signatures.length then some .unary else none
    field := fun i => if i < s.declarations.fields.length then some .binary else none
    var := fun i => if i < depth then some .unary else none
    univ := some .unary, iden := some .binary, ints := some .unary
    integer := fun _ => some .unary
    values := fun i => if (s.declarations.signatures[i]?).any Alloy.Signature.scalar then some .binary else none
    union := sameArity, inter := sameArity, diff := sameArity
    product := fun a b => if a == some .unary && b == some .unary then some .binary else none
    join := fun a b => match a, b with
      | some .unary, some .binary | some .binary, some .unary => some .unary
      | some .binary, some .binary => some .binary
      | _, _ => none
    transpose := fun a => if a == some .binary then some .binary else none
    prime := id } none

def Integer.wellTyped (s : Schema) (d : Nat) (n : Integer) : Bool :=
  n.fold {
    literal := fun _ => true, count := fun r => (r.typeOf s d).isSome
    scalar := fun lo hi r => lo ≤ hi && r.typeOf s d == some .unary
    add := (· && ·), subtract := (· && ·), multiply := (· && ·)
    divide := (· && ·), remainder := (· && ·) } false

def Formula.wellTyped (s : Schema) (d : Nat) (p : Formula) : Bool :=
  p.fold {
    truth := fun _ => true, falsity := fun _ => true
    equal := fun a b d => (sameArity (a.typeOf s d) (b.typeOf s d)).isSome
    subset := fun a b d => (sameArity (a.typeOf s d) (b.typeOf s d)).isSome
    mult := fun _ r d => (r.typeOf s d).isSome
    compare := fun _ a b d => a.wellTyped s d && b.wellTyped s d
    unary := fun _ p d => p d
    binary := fun _ p q d => p d && q d
    all := fun r p d => r.typeOf s d == some .unary && p (d + 1)
    exists_ := fun r p d => r.typeOf s d == some .unary && p (d + 1) } (fun _ => false) d

def Schema.wellFormed (s : Schema) : Bool :=
  s.declarations.wellFormed &&
  s.mutableSignatures.length == s.declarations.signatures.length &&
  s.mutableFields.length == s.declarations.fields.length &&
  s.declarations.signatures.zipIdx.all (fun (sig, i) =>
    (!(s.mutableSignatures[i]?.getD false) || sig.parent.isNone))

def Module.wellTyped (m : Module) : Bool :=
  m.schema.wellFormed && m.facts.all (Formula.wellTyped m.schema 0) &&
    m.command.body.wellTyped m.schema 0

/-- Finite column capacities use trace-wide identity budgets, including Int. -/
def Rel.columns (m : Module) (r : Rel) : List Nat :=
  let capacity := (m.command.scopes.map Scope.size).foldl (· + ·) 0 + 2 ^ m.command.bitwidth
  r.fold {
    empty := fun a => if a == .unary then [0] else [0, 0]
    sig := fun i => [(m.command.scopes[i]?.map Scope.size).getD 0]
    field := fun i => match m.schema.declarations.fields[i]? with
      | some f => [(m.command.scopes[f.owner]?.map Scope.size).getD 0,
                   (m.command.scopes[f.target]?.map Scope.size).getD 0]
      | none => [0, 0]
    var := fun _ => [1]
    integer := fun _ => [1]
    values := fun i => [(m.command.scopes[i]?.map Scope.size).getD 0, 2 ^ m.command.bitwidth]
    ints := [2 ^ m.command.bitwidth], univ := [capacity], iden := [capacity, capacity]
    union := List.zipWith (· + ·), inter := List.zipWith min, diff := fun a _ => a
    product := (· ++ ·), join := fun a b => a.dropLast ++ b.drop 1
    transpose := List.reverse, prime := id } []

/-- The same conservative magnitude bounds used by the frontend range pass,
over the target's independent interval representation. -/
def magnitude (r : IntRange) : Nat := max r.lower.natAbs r.upper.natAbs

def symmetric (bound : Nat) : IntRange := ⟨-(bound : Int), bound⟩

def nonzero (r : IntRange) : Bool := r.upper < 0 || 0 < r.lower

def quotientRange (width : Nat) (a b : Option IntRange) : Option IntRange := do
  let a ← a; let b ← b
  if nonzero b then IntRange.checked width (symmetric (magnitude a)) else none

def Rel.safe (m : Module) (r : Rel) : Bool := r.code.all fun op => match op with
  | .integer n => fitsInt m.command.bitwidth n
  | _ => true

-- [impl->req~compiler-alloy-temporal-target~1]
def Integer.range (m : Module) (n : Integer) : Option IntRange :=
  n.fold {
    literal := fun n => IntRange.checked m.command.bitwidth ⟨n, n⟩
    scalar := fun lo hi r => if r.safe m then IntRange.checked m.command.bitwidth ⟨lo, hi⟩ else none
    count := fun r => if r.safe m then IntRange.checked m.command.bitwidth
      ⟨0, Int.ofNat ((r.columns m).foldl (· * ·) 1)⟩ else none
    add := fun a b => do
      let a ← a; let b ← b
      IntRange.checked m.command.bitwidth ⟨a.lower + b.lower, a.upper + b.upper⟩
    subtract := fun a b => do
      let a ← a; let b ← b
      IntRange.checked m.command.bitwidth ⟨a.lower - b.upper, a.upper - b.lower⟩
    multiply := fun a b => do
      let a ← a; let b ← b
      IntRange.checked m.command.bitwidth (symmetric (magnitude a * magnitude b))
    divide := quotientRange m.command.bitwidth
    remainder := quotientRange m.command.bitwidth } none

def Formula.safe (m : Module) (p : Formula) : Bool :=
  p.fold {
    truth := true, falsity := true
    equal := fun a b => a.safe m && b.safe m
    subset := fun a b => a.safe m && b.safe m, mult := fun _ r => r.safe m
    compare := fun _ a b => (a.range m).isSome && (b.range m).isSome
    unary := fun _ p => p, binary := fun _ p q => p && q
    all := fun r p => r.safe m && p, exists_ := fun r p => r.safe m && p } false

def Rel.temporal (r : Rel) : Bool := r.code.contains .prime

def Integer.temporal (n : Integer) : Bool := n.code.any fun op => match op with
  | .count r | .scalar _ _ r => r.temporal
  | _ => false

def Formula.temporal (p : Formula) : Bool := p.code.any fun op => match op with
  | .truth | .falsity => false
  | .equal a b | .subset a b => a.temporal || b.temporal
  | .mult _ r | .all r | .exists_ r => r.temporal
  | .compare _ a b => a.temporal || b.temporal
  | .unary .neg => false
  | .unary _ => true
  | .binary .conj | .binary .disj | .binary .implies => false
  | .binary _ => true

/-- Alloy rejects an explicit `steps` scope on an entirely static module. -/
def Module.temporal (m : Module) : Bool :=
  m.schema.mutableSignatures.any id || m.schema.mutableFields.any id ||
  m.schema.declarations.signatures.any Alloy.Signature.scalar ||
  m.facts.any Formula.temporal || m.command.body.temporal

def Module.safeBounds (m : Module) : Bool :=
  m.temporal &&
  1 ≤ m.command.bitwidth && m.command.bitwidth ≤ 16 &&
  1 ≤ m.command.minSteps && m.command.minSteps ≤ m.command.maxSteps &&
  m.command.scopes.length == m.schema.declarations.signatures.length &&
  (m.schema.declarations.signatures.zipIdx.all fun (sig, i) =>
    let scope := m.command.scopes[i]?.getD ⟨0, false⟩
    (!(m.schema.mutableSignatures[i]?.getD false) || !scope.exact) &&
    match sig.multiplicity with
    | .set => true
    | .one => if m.schema.mutableSignatures[i]?.getD false then 1 ≤ scope.size else scope.size == 1
    | .lone => m.schema.mutableSignatures[i]?.getD false || scope.size ≤ 1
    | .some => 1 ≤ scope.size) &&
  m.facts.all (Formula.safe m) && m.command.body.safe m

structure CheckedModule where
  raw : Module
  typed : raw.wellTyped = true
  bounded : raw.safeBounds = true

def check (m : Module) : Except AdmissionError CheckedModule :=
  if ht : m.wellTyped = true then
    if hb : m.safeBounds = true then .ok ⟨m, ht, hb⟩ else .error .unsupportedBounds
  else .error .malformedSyntax

end ClaferCompiler.Backend.Alloy.Temporal
