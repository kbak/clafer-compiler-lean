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
def childHeads (m : IR.Structural.Core n) (d : Fin n) : Rel :=
  union ((children m d).map fun c => .join (.var 0) (contains m c))

def ownership (v : IR.Structural.Layout n) (d : Fin n) : Formula :=
  .all (head v d) (.mult .one (.join (.var 0) (.transpose (contains v.core d))))

/-- For one owner, equal referents imply equal heads. Different owners may
reference the same target. The innermost binders are y=0, x=1, owner=2. -/
def setKey (v : IR.Structural.Layout n) (d p : Fin n) : Formula :=
  .all (head v p)
    (.all (.join (.var 0) (contains v.core d))
      (.all (.join (.var 1) (contains v.core d))
        (.implies (.equal (.join (.var 1) (deref v.core d))
                          (.join (.var 0) (deref v.core d)))
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

def declarationFacts (v : IR.Structural.Layout n) (d : Fin n) : List (Obligation × Formula) :=
  let row := v.core.get d
  let abstractFacts := if row.isAbstract then
    [(.abstractCover row.id, .equal (head v d) (union ((subtypes v.core d).map (head v))))]
    else [(.groupBounds row.id, .all (head v d) (interval row.groupBounds (childHeads v.core d)))]
  let parentFacts := match row.parent with
    | none => []
    | some p =>
      [(.ownership row.id, ownership v d),
       (.localBounds row.id, .all (head v p)
         (interval row.localBounds (.join (.var 0) (contains v.core d))))] ++
      match row.reference with
      | .set _ => [(.setKey row.id, setKey v d p)]
      | _ => []
  abstractFacts ++ parentFacts

def facts (v : IR.Structural.Layout n) : List (Obligation × Formula) :=
  [(.root, .mult .one (head v v.core.root)),
   (.objectCover, .equal (.sig 0) (union ((List.finRange n).map (head v))))] ++
    (List.finRange n).flatMap (declarationFacts v)

def fieldDeclaration (v : IR.Structural.Layout n) (key : Fin n × FieldRole) : Field :=
  match key with
  | (d, role) => match role with
    | .containment =>
      { owner := (v.core.get d).parent.map (signatureId v) |>.getD 0
        target := signatureId v d }
    | .dereference =>
      { owner := signatureId v d
        target := (v.core.get d).reference.target.map (signatureId v) |>.getD 0
        multiplicity := .one }

/-- Extends implements shared inherited identity and incomparable disjointness.
All signature multiplicities are set: conflicting manual scopes are constraints,
not malformed syntax. Explicit abstract facts cover the Alloy leaf exception. -/
def schema (v : IR.Structural.Layout n) : Schema where
  signatures := { isAbstract := true } :: (order v).map fun d =>
    { parent := some ((v.core.get d).super.map (signatureId v) |>.getD 0)
      isAbstract := (v.core.get d).isAbstract }
  fields := (fieldKeys v.core).map (fieldDeclaration v)

structure DeclarationMap where
  id : IR.Structural.DeclId
  name : String
  source : Option IR.Structural.SourceSpan
  signature : Nat
  containment : Option Nat
  dereference : Option Nat

def declarationMap (v : IR.Structural.Layout n) (d : Fin n) : DeclarationMap where
  id := (v.core.get d).id
  name := (v.core.get d).name
  source := (v.core.get d).source
  signature := signatureId v d
  containment := (v.core.get d).parent.map fun _ => fieldId v.core d .containment
  dereference := (v.core.get d).reference.target.map fun _ => fieldId v.core d .dereference

def nameMap (v : IR.Structural.Layout n) : List DeclarationMap :=
  (List.finRange n).map (declarationMap v)

/-- Complete, unique ID scopes; preserve impossible but well-formed constraints. -/
def resolveScopes (v : IR.Structural.Layout n) (b : Bounds) : Except Error (List Scope) := do
  if b.declarations.length != n || !(b.declarations.map Prod.fst).Nodup then
    throw .malformedBounds
  let scopes ← (order v).mapM fun d =>
    match b.declarations.find? (fun entry => entry.1 == (v.core.get d).id) with
    | none => .error Error.malformedBounds
    | some entry => .ok entry.2
  return { size := b.objects } :: scopes

def target (v : IR.Structural.Layout n) (scopes : List Scope) (bitwidth : Nat) : Module where
  schema := schema v
  facts := (facts v).map Prod.snd
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

/-- Raw effective IR retains the existing exact admission boundary. -/
def compileRaw (r : IR.Structural.Raw) (b : Bounds) : Except Error Compiled := do
  let v ← (IR.Structural.validateRaw r).mapError Error.source
  compile v b

end ClaferCompiler.Backend.Alloy.Structural
