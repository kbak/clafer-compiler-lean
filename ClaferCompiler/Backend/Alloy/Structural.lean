module

public import ClaferCompiler.IR.Structural
public import ClaferCompiler.Backend.Alloy.Bounds

@[expose] public section

namespace ClaferCompiler.Backend.Alloy.Structural

/-! First structural backend: source heads are atoms, including reference heads.
All target meanings remain in the independent target modules.
[impl->req~compiler-structural-encoding~1] -/

/-- Manual bounds use input identities, not names or target positions. The object
budget counts the union of extents (including the root), not their sum. -/
structure Bounds where
  declarations : List (IR.Structural.DeclId × Scope)
  objects : Nat
  bitwidth : Nat

inductive Error where
  | source (diagnostic : IR.Structural.Diagnostic)
  | malformedBounds
  | unsupportedBounds
  | internalTarget

inductive FieldRole where
  | containment | dereference
  deriving DecidableEq

/-- The checked super rank orders parents before children; position breaks ties.
Every declaration occurs once, regardless of source names and input ordering. -/
def order (v : IR.Structural.Layout n) : List (Fin n) :=
  (List.finRange n).mergeSort fun a b =>
    v.certificate.superRank[a] < v.certificate.superRank[b] ||
      (v.certificate.superRank[a] == v.certificate.superRank[b] && a.val ≤ b.val)

/-- Zero is the object union signature; declarations occupy positions 1..n. -/
def signatureId (v : IR.Structural.Layout n) (d : Fin n) : Nat := 1 + (order v).idxOf d

def fieldKeys (m : IR.Structural.Core n) : List (Fin n × FieldRole) :=
  (List.finRange n).flatMap fun d =>
    ((m.get d).parent.toList.map fun _ => (d, .containment)) ++
    ((m.get d).reference.target.toList.map fun _ => (d, .dereference))

def fieldId (m : IR.Structural.Core n) (d : Fin n) (role : FieldRole) : Nat :=
  (fieldKeys m).idxOf (d, role)

def head (v : IR.Structural.Layout n) (d : Fin n) : Rel := .sig (signatureId v d)
def contains (m : IR.Structural.Core n) (d : Fin n) : Rel := .field (fieldId m d .containment)
def deref (m : IR.Structural.Core n) (d : Fin n) : Rel := .field (fieldId m d .dereference)

/-- Shared lookup functions; the reference allocation retains the original indices. -/
structure Allocation (n : Nat) where
  signatures : Fin n → Nat
  fields : Fin n → FieldRole → Nat

def allocation (v : IR.Structural.Layout n) : Allocation n :=
  ⟨signatureId v, fieldId v.core⟩

/-- Sort once and retain dense lookup tables for this compilation. Missing field
roles keep the original `idxOf` fallback, so even unused lookups are identical. -/
def cachedAllocation (v : IR.Structural.Layout n) : Allocation n :=
  let ordered := order v
  let keys := fieldKeys v.core
  let signatures := Vector.ofFn fun d : Fin n => 1 + ordered.idxOf d
  let fields := Vector.ofFn fun d : Fin n =>
    (keys.idxOf (d, FieldRole.containment), keys.idxOf (d, FieldRole.dereference))
  ⟨fun d => signatures[d], fun d role =>
    match role with | .containment => fields[d].1 | .dereference => fields[d].2⟩

@[simp] theorem cachedAllocation_eq (v : IR.Structural.Layout n) :
    cachedAllocation v = allocation v := by
  unfold cachedAllocation allocation
  dsimp only
  congr 1
  · funext d
    simp [signatureId]
  · funext d role
    cases role <;> simp [fieldId]

abbrev Allocation.head (a : Allocation n) (d : Fin n) : Rel := .sig (a.signatures d)
abbrev Allocation.contains (a : Allocation n) (d : Fin n) : Rel := .field (a.fields d .containment)
abbrev Allocation.deref (a : Allocation n) (d : Fin n) : Rel := .field (a.fields d .dereference)

@[simp] theorem allocation_signatures (v : IR.Structural.Layout n) :
    (allocation v).signatures = signatureId v := rfl
@[simp] theorem allocation_fields (v : IR.Structural.Layout n) :
    (allocation v).fields = fieldId v.core := rfl
@[simp] theorem allocation_head (v : IR.Structural.Layout n) :
    (allocation v).head = head v := rfl
@[simp] theorem allocation_contains (v : IR.Structural.Layout n) :
    (allocation v).contains = contains v.core := rfl
@[simp] theorem allocation_deref (v : IR.Structural.Layout n) :
    (allocation v).deref = deref v.core := rfl
@[simp] theorem allocation_head_apply (v : IR.Structural.Layout n) (d : Fin n) :
    (allocation v).head d = head v d := rfl
@[simp] theorem allocation_contains_apply (v : IR.Structural.Layout n) (d : Fin n) :
    (allocation v).contains d = contains v.core d := rfl
@[simp] theorem allocation_deref_apply (v : IR.Structural.Layout n) (d : Fin n) :
    (allocation v).deref d = deref v.core d := rfl

def union (rs : List Rel) : Rel := rs.foldl Rel.union (.empty .unary)

/-- Bounds apply to distinct heads. Unbounded is omission, never an Int value.
Unrestricted intervals introduce no integer observations. -/
def interval (b : IR.Structural.Bounds) (r : Rel) : Formula :=
  let lower := if b.lower == 0 then Formula.truth
    else .compare .le (.literal (Int.ofNat b.lower)) (.count r)
  let upper := match b.upper with
    | .unbounded => Formula.truth
    | .finite k => .compare .le (.count r) (.literal (Int.ofNat k))
  .conj lower upper

def children (m : IR.Structural.Core n) (d : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun c => (m.get c).parent == some d

def subtypes (m : IR.Structural.Core n) (d : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun c => (m.get c).super == some d

/-- A child union at one owner; reference heads are never dereferenced here. -/
def childHeads (m : IR.Structural.Core n) (d : Fin n)
    (fields : Fin n → FieldRole → Nat := fieldId m) : Rel :=
  union ((children m d).map fun c => .join (.var 0) (.field (fields c .containment)))

def ownership (v : IR.Structural.Layout n) (d : Fin n)
    (a : Allocation n := allocation v) : Formula :=
  .all (a.head d) (.mult .one (.join (.var 0) (.transpose (a.contains d))))

/-- For one owner, equal referents imply equal heads. Different owners may
reference the same target. The innermost binders are y=0, x=1, owner=2. -/
def setKey (v : IR.Structural.Layout n) (d p : Fin n)
    (a : Allocation n := allocation v) : Formula :=
  .all (a.head p)
    (.all (.join (.var 0) (a.contains d))
      (.all (.join (.var 1) (a.contains d))
        (.implies (.equal (.join (.var 1) (a.deref d))
                          (.join (.var 0) (a.deref d)))
                  (.equal (.var 1) (.var 0)))))

/-- Every emitted fact retains its obligation and input declaration identity. -/
inductive Obligation where
  | root | objectCover
  | abstractCover (declaration : IR.Structural.DeclId)
  | ownership (declaration : IR.Structural.DeclId)
  | localBounds (declaration : IR.Structural.DeclId)
  | groupBounds (declaration : IR.Structural.DeclId)
  | setKey (declaration : IR.Structural.DeclId)
  deriving DecidableEq

def declarationFacts (v : IR.Structural.Layout n) (d : Fin n)
    (a : Allocation n := allocation v) : List (Obligation × Formula) :=
  let row := v.core.get d
  let abstractFacts := if row.isAbstract then
    [(.abstractCover row.id, .equal (a.head d) (union ((subtypes v.core d).map (a.head))))]
    else [(.groupBounds row.id, .all (a.head d) (interval row.groupBounds (childHeads v.core d a.fields)))]
  let parentFacts := match row.parent with
    | none => []
    | some p =>
      [(.ownership row.id, ownership v d a),
       (.localBounds row.id, .all (a.head p)
         (interval row.localBounds (.join (.var 0) (a.contains d))))] ++
      match row.reference with
      | .set _ => [(.setKey row.id, setKey v d p a)]
      | _ => []
  abstractFacts ++ parentFacts

def facts (v : IR.Structural.Layout n)
    (a : Allocation n := allocation v) : List (Obligation × Formula) :=
  [(.root, .mult .one (a.head v.core.root)),
   (.objectCover, .equal (.sig 0) (union ((List.finRange n).map (a.head))))] ++
    (List.finRange n).flatMap (fun d => declarationFacts v d a)

def fieldDeclaration (v : IR.Structural.Layout n) (key : Fin n × FieldRole)
    (a : Allocation n := allocation v) : Field :=
  match key with
  | (d, role) => match role with
    | .containment =>
      { owner := (v.core.get d).parent.map (a.signatures) |>.getD 0
        target := a.signatures d }
    | .dereference =>
      { owner := a.signatures d
        target := (v.core.get d).reference.target.map (a.signatures) |>.getD 0
        multiplicity := .one }

/-- Extends implements shared inherited identity and incomparable disjointness.
All signature multiplicities are set: conflicting manual scopes are constraints,
not malformed syntax. Explicit abstract facts cover the Alloy leaf exception. -/
def schema (v : IR.Structural.Layout n)
    (a : Allocation n := allocation v) : Schema where
  signatures := { isAbstract := true } :: (order v).map fun d =>
    { parent := some ((v.core.get d).super.map (a.signatures) |>.getD 0)
      isAbstract := (v.core.get d).isAbstract }
  fields := (fieldKeys v.core).map (fun key => fieldDeclaration v key a)

structure DeclarationMap where
  id : IR.Structural.DeclId
  name : String
  source : Option IR.Structural.SourceSpan
  signature : Nat
  containment : Option Nat
  dereference : Option Nat

def declarationMap (v : IR.Structural.Layout n) (d : Fin n)
    (a : Allocation n := allocation v) : DeclarationMap where
  id := (v.core.get d).id
  name := (v.core.get d).name
  source := (v.core.get d).source
  signature := a.signatures d
  containment := (v.core.get d).parent.map fun _ => a.fields d .containment
  dereference := (v.core.get d).reference.target.map fun _ => a.fields d .dereference

def nameMap (v : IR.Structural.Layout n)
    (a : Allocation n := allocation v) : List DeclarationMap :=
  (List.finRange n).map (fun d => declarationMap v d a)

/-- Complete, unique ID scopes; preserve impossible but well-formed constraints. -/
def resolveScopes (v : IR.Structural.Layout n) (b : Bounds) : Except Error (List Scope) := do
  if b.declarations.length != n || !(b.declarations.map Prod.fst).Nodup then
    throw .malformedBounds
  let scopes ← (order v).mapM fun d =>
    match b.declarations.find? (fun entry => entry.1 == (v.core.get d).id) with
    | none => .error Error.malformedBounds
    | some entry => .ok entry.2
  return { size := b.objects } :: scopes

def target (v : IR.Structural.Layout n) (scopes : List Scope) (bitwidth : Nat)
    (a : Allocation n := allocation v) : Module where
  schema := schema v a
  facts := (facts v a).map Prod.snd
  command := { scopes, bitwidth }

structure Compiled where
  module : CheckedModule
  declarations : List DeclarationMap
  obligations : List Obligation

/-- Successful compilation carries checked target binding/arity and bounds.
No solver, parser, text serializer or semantic satisfaction test is invoked. -/
def compile (v : IR.Structural.Validated n) (b : Bounds) : Except Error Compiled := do
  let scopes ← resolveScopes v.toLayout b
  match check (target v.toLayout scopes b.bitwidth) with
  | .error .malformedSyntax => .error .internalTarget
  | .error .unsupportedBounds => .error .unsupportedBounds
  | .ok checked => .ok ⟨checked, nameMap v.toLayout, (facts v.toLayout).map Prod.fst⟩

/-- Native implementation shares allocation across target generation and metadata. -/
def compileCached (v : IR.Structural.Validated n) (b : Bounds) : Except Error Compiled := do
  let scopes ← resolveScopes v.toLayout b
  let a := cachedAllocation v.toLayout
  match check (target v.toLayout scopes b.bitwidth a) with
  | .error .malformedSyntax => .error .internalTarget
  | .error .unsupportedBounds => .error .unsupportedBounds
  | .ok checked => .ok ⟨checked, nameMap v.toLayout a, (facts v.toLayout a).map Prod.fst⟩

/-- The compiler replacement preserves the entire result, including errors. -/
@[csimp] theorem compile_eq_compileCached : @compile = @compileCached := by
  funext n v b
  simp only [compile, compileCached, cachedAllocation_eq]

/-- Raw effective IR retains the existing exact admission boundary. -/
def compileRaw (r : IR.Structural.Raw) (b : Bounds) : Except Error Compiled := do
  let v ← (IR.Structural.validateRaw r).mapError Error.source
  compile v b

end ClaferCompiler.Backend.Alloy.Structural
