module

public import ClaferCompiler.Backend.Alloy.Expressions
public import ClaferCompiler.Backend.Alloy.Inherited

/-! [impl->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Expressions
open IR.Expr

/-- Every occurrence retains its owner, original identity and optional span.
Repeated bodies remain distinct list entries, including inherited owners. -/
structure Body (n : Nat) where
  id : Nat
  owner : Fin n
  source : Option IR.Structural.SourceSpan := none
  mapCount : Nat
  support : Support n mapCount
  term : Term n mapCount

def bindingError : Structural.Error := .source
  { category := .malformed, code := "expr.unresolved-support" }

/-- A resolved role has one concrete target relation; original IDs select the
owning declaration before endpoint validation. -/
def bindMap (v : IR.Inherited.Validated n) (e : MapRef n) : Except Structural.Error Rel := do
  let c := v.core.structural
  let some d := (List.finRange n).find? (fun d => (c.get d).id == e.owner)
    | throw bindingError
  let decl := c.get d
  match e.kind with
  | .head =>
    if decl.parent != some e.source || d != e.target then throw bindingError
    return Structural.contains v.layout.core d
  | .parent =>
    if d != e.source || decl.parent != some e.target then throw bindingError
    return .transpose (Structural.contains v.layout.core d)
  | .dereference =>
    if d != e.source || decl.reference.target != some e.target then throw bindingError
    return Structural.deref v.layout.core d
  | .target =>
    if decl.parent != some e.source || decl.reference.target != some e.target then throw bindingError
    return .join (Structural.contains v.layout.core d) (Structural.deref v.layout.core d)
  | .inclusion =>
    if d != e.source || decl.super != some e.target then throw bindingError
    return .diagonal (Structural.head v.layout d)

/-- Validate concrete declaration and role equations; names never select a map. -/
def bindSupport (v : IR.Inherited.Validated n) (s : Support n m) (owner : Fin n) :
    Except Structural.Error (Layout n m) := do
  let c := v.core.structural
  if s.context != owner || !(List.finRange n).all (fun x =>
      s.classes[x] == (c.get x).id && s.integer[x] == decide ((c.get x).origin = .integer)) then
    throw bindingError
  let maps ← (List.finRange m).mapM (fun edge => bindMap v (s.maps.get edge))
  if h : maps.length = m then
    return ⟨Vector.ofFn (Structural.head v.layout), ⟨maps.toArray, by simp [h]⟩,
      Vector.ofFn (Structural.signatureId v.layout)⟩
  else throw bindingError

def scalarIds (v : IR.Inherited.Validated n) : List Nat :=
  ((List.finRange n).filter fun d => (v.core.structural.get d).origin == .integer).map
    (Structural.signatureId v.layout)

def scalarSchema (v : IR.Inherited.Validated n) (s : Schema) : Schema :=
  { s with signatures := s.signatures.zipIdx.map fun (decl, i) =>
      { decl with scalar := (scalarIds v).contains i } }

/-- The full-width read is used only in domain/injectivity enforcement. Source
extractions use the narrower declared interval after these facts enforce it. -/
def scalarAt (owner width index : Nat) : Integer :=
  .scalar owner (minInt width) (maxInt width) (.var index)

def scalarFacts (owner width : Nat) (range : Interval) : List Formula := [
  .all (.sig owner) (.conj
    (.compare .le (.literal range.lower) (scalarAt owner width 0))
    (.compare .le (scalarAt owner width 0) (.literal range.upper))),
  .all (.sig owner) (.all (.sig owner) (.implies
    (.compare .eq (scalarAt owner width 1) (scalarAt owner width 0))
    (.equal (.var 1) (.var 0)))) ]

structure EncodedBody (n : Nat) where
  original : Body n
  formula : Formula
  defined : Formula
  truth : Formula

structure Compiled (n : Nat) where
  module : CheckedModule
  declarations : List Structural.DeclarationMap
  structural : List Inherited.Obligation
  bodies : List (EncodedBody n)
  numericFacts : List Formula

def encodeBody (v : IR.Inherited.Validated n) (b : IR.Expr.Bounds n) (body : Body n) :
    Except Structural.Error (EncodedBody n) := do
  let layout ← bindSupport v body.support body.owner
  let a ← (validateBounds body.support b [] .boolean body.term).mapError Structural.Error.source
  let code := encode layout a
  return ⟨body, attach (Structural.head v.layout body.owner) code, code.defined, code.value⟩

/-- Full source-body compilation composes the inherited structural facts, numeric
field/range/identity enforcement, and every attachment occurrence. -/
def sourceBounds (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) : IR.Expr.Bounds n := {
    width := bounds.bitwidth
    extents := Vector.ofFn fun x =>
      ((bounds.declarations.find? fun row => row.1 == (v.core.structural.get x).id).map
        (fun row => row.2.size)).getD 0
    integers := intervals }

def numericFacts (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) : Except Structural.Error (List Formula) :=
  (List.finRange n).flatMapM fun d => do
    if (v.core.structural.get d).origin != .integer then return []
    if !intervals[d].fits bounds.bitwidth then throw (.source boundsError)
    return scalarFacts (Structural.signatureId v.layout d) bounds.bitwidth intervals[d]

def compile (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) :
    Except Structural.Error (Compiled n) := do
  let base ← Inherited.compile v bounds
  let numeric ← numericFacts v bounds intervals
  let encoded ← bodies.mapM (encodeBody v (sourceBounds v bounds intervals))
  let raw : Module := { base.module.raw with
    schema := scalarSchema v base.module.raw.schema
    facts := base.module.raw.facts ++ numeric ++ encoded.map EncodedBody.formula }
  match check raw with
  | .error .malformedSyntax => throw .internalTarget
  | .error .unsupportedBounds => throw .unsupportedBounds
  | .ok checked => return ⟨checked, base.declarations, base.obligations, encoded, numeric⟩

end ClaferCompiler.Backend.Alloy.Expressions
