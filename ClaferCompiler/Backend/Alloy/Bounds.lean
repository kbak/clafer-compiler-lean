module

public import ClaferCompiler.Backend.Alloy.Syntax

@[expose] public section

namespace ClaferCompiler.Backend.Alloy

/-! Explicit bounds, independent of facts and candidate satisfaction.
[impl->req~compiler-bounds~1] -/

def minInt (width : Nat) : Int := -(Int.ofNat (2 ^ (width - 1)))
def maxInt (width : Nat) : Int := Int.ofNat (2 ^ (width - 1)) - 1

def fitsInt (width : Nat) (value : Int) : Bool :=
  1 ≤ width && width ≤ 16 && minInt width ≤ value && value ≤ maxInt width

/-- A failed range check is undefined, never modular arithmetic or false. -/
def boundedInt (width : Nat) (value : Int) : Option Int :=
  if fitsInt width value then some value else none

theorem boundedInt_some_iff (width : Nat) (value : Int) :
    boundedInt width value = some value ↔ fitsInt width value = true := by
  simp [boundedInt]

/-- Column budgets bound the finite operand inventory, even for empty products.
Union sums are conservative; intersection/difference cannot increase columns. -/
def Rel.columns (scopes : List Scope) (schema : Schema) (env : List Nat) (rel : Rel) : List Nat :=
  rel.fold {
    empty := fun a => match a with | .unary => [0] | .binary => [0, 0]
    sig := fun i => [(scopes[i]?).map Scope.size |>.getD 0]
    field := fun i => match schema.fields[i]? with
      | none => [0, 0]
      | some f => [(scopes[f.owner]?).map Scope.size |>.getD 0,
                   (scopes[f.target]?).map Scope.size |>.getD 0]
    var := fun i => [env[i]?.getD 0]
    union := List.zipWith (· + ·)
    inter := List.zipWith min
    diff := fun a _ => a
    product := (· ++ ·)
    join := fun a b => a.dropLast ++ b.drop 1
    transpose := List.reverse
  } []

/-! [impl->req~compiler-target-arithmetic~1] -/

/-- A successful interval certifies every intermediate, not only the root.
Counts use independent finite column budgets, never assumed fact truth. -/
structure IntRange where
  lower : Int
  upper : Int
  deriving DecidableEq, BEq

def IntRange.checked (width : Nat) (r : IntRange) : Option IntRange :=
  if r.lower ≤ r.upper && fitsInt width r.lower && fitsInt width r.upper then some r else none

def Integer.range (m : Module) (depth : Nat) (n : Integer) : Option IntRange :=
  n.fold {
    literal := fun n => IntRange.checked m.command.bitwidth ⟨n, n⟩
    count := fun r => IntRange.checked m.command.bitwidth
      ⟨0, Int.ofNat ((r.columns m.command.scopes m.schema
        (List.replicate depth 1)).foldl (· * ·) 1)⟩
    add := fun a b => do
      let a ← a; let b ← b
      IntRange.checked m.command.bitwidth ⟨a.lower + b.lower, a.upper + b.upper⟩
    subtract := fun a b => do
      let a ← a; let b ← b
      IntRange.checked m.command.bitwidth ⟨a.lower - b.upper, a.upper - b.lower⟩
  } none

def Integer.safe (m : Module) (depth : Nat) (n : Integer) : Bool :=
  (n.range m depth).isSome

/-- Check all branches, including negation, vacuous implications and empty domains. -/
def Formula.safe (m : Module) (depth : Nat) (formula : Formula) : Bool :=
  formula.fold {
    truth := fun _ => true, falsity := fun _ => true
    equal := fun _ _ _ => true, subset := fun _ _ _ => true, mult := fun _ _ _ => true
    compare := fun _ a b d => a.safe m d && b.safe m d
    neg := fun p d => p d
    conj := fun p q d => p d && q d
    disj := fun p q d => p d && q d
    implies := fun p q d => p d && q d
    all := fun _ p d => p (d + 1)
    exists_ := fun _ p d => p (d + 1)
  } (fun _ => false) depth

def Module.safeBounds (m : Module) : Bool :=
  1 ≤ m.command.bitwidth && m.command.bitwidth ≤ 16 &&
  m.command.scopes.length == m.schema.signatures.length &&
  ((m.schema.signatures.zip m.command.scopes).all fun (sig, scope) =>
    match sig.multiplicity with
    | .set => true
    | .one => scope.size == 1
    | .lone => scope.size ≤ 1
    | .some => 1 ≤ scope.size) &&
  m.facts.all (Formula.safe m 0) && m.command.body.safe m 0

structure CheckedModule where
  raw : Module
  typed : raw.wellTyped = true
  bounded : raw.safeBounds = true

inductive AdmissionError where
  | malformedSyntax | unsupportedBounds
  deriving DecidableEq, BEq

def check (m : Module) : Except AdmissionError CheckedModule :=
  if ht : m.wellTyped = true then
    if hb : m.safeBounds = true then .ok ⟨m, ht, hb⟩ else .error .unsupportedBounds
  else .error .malformedSyntax

end ClaferCompiler.Backend.Alloy
