module

public import ClaferCompiler.Driver.Decode
public import ClaferCompiler.Frontend.Pipeline

@[expose] public section
/-! [impl->req~compiler-pipeline-correctness~1]
[impl->req~compiler-cli~1] -/
namespace ClaferCompiler.Driver.Source
open Backend.Alloy

structure Bounds where
  structural : Structural.Bounds
  integers : List (Nat × IR.Expr.Interval)

def integer (n : Decode.Node) : Except Diagnostic Int :=
  n.value.getInt?.mapError fun _ => Decode.bad n "expected integer-number token"

def integerScope (n : Decode.Node) : Except Diagnostic (Nat × IR.Expr.Interval) := do
  Decode.closed n ["id", "lower", "upper"]
  let id ← Decode.natural (← Decode.field n "id")
  let lo ← integer (← Decode.field n "lower")
  let hi ← integer (← Decode.field n "upper")
  if lo > hi then throw (Decode.bad n "integer interval is reversed")
  return (id, ⟨lo, hi⟩)

def bounds (file text : String) : Except Diagnostic Bounds := do
  let n ← Decode.parse file text true
  Decode.version n "version" "clafer-bounds/2" "bounds.version"
  Decode.closed n ["version", "objects", "bitwidth", "declarations", "integers"]
  return ⟨{
    objects := ← Decode.natural (← Decode.field n "objects")
    bitwidth := ← Decode.natural (← Decode.field n "bitwidth")
    declarations := (← Decode.array Decode.scope (← Decode.field n "declarations")).toList },
    (← Decode.array integerScope (← Decode.field n "integers")).toList⟩

def intervals (file : String) (v : IR.Inherited.Validated n) (b : Bounds) :
    Except Diagnostic (Vector IR.Expr.Interval n) := do
  let ids := ((List.finRange n).filter fun d =>
    (v.core.structural.get d).origin == .integer).map fun d => (v.core.structural.get d).id
  if !(b.integers.map Prod.fst).Nodup || b.integers.length != ids.length ||
      !b.integers.all (fun row => ids.contains row.1) then
    throw {
      code := "bounds.integers", phase := "bounds", file, pointer := "/integers"
      message := "each primitive declaration ID requires exactly one integer interval" }
  return Vector.ofFn fun d =>
    ((b.integers.find? fun row => row.1 == (v.core.structural.get d).id).map Prod.snd).getD ⟨0, 0⟩

/-- The public budget counts only nonprimitive objects. The target union also
contains finite scalar atoms, allocated using the explicit primitive scopes. -/
def targetBounds (v : IR.Inherited.Validated n) (b : Bounds) : Structural.Bounds :=
  let extra := ((List.finRange n).filter fun d =>
    (v.core.structural.get d).origin == .integer).foldl
      (fun total d => total + ((b.structural.declarations.find? fun row =>
        row.1 == (v.core.structural.get d).id).map (fun row => row.2.size)).getD 0) 0
  { b.structural with objects := b.structural.objects + extra }

def objectBudget (v : IR.Inherited.Validated n) (budget : Nat) : Formula :=
  .compare .le (.count (.diff (.sig 0)
    (Structural.union ((Expressions.scalarIds v).map Rel.sig)))) (.literal budget)

def backendDiagnostic (file : String) : Structural.Error → Diagnostic :=
  Driver.backendDiagnostic file fun d => {
      code := d.code, phase := "encoding", file, pointer := d.pointer, declaration := d.declaration
      category := match d.category with | .malformed => .malformed | .unsupported => .unsupported
      message := "source encoding or conservative range admission failed" }

structure Product where
  prepared : Frontend.Pipeline.Prepared
  bounds : Bounds
  intervals : Vector IR.Expr.Interval prepared.resolved.count
  encoded : Expressions.Compiled prepared.resolved.count
  module : CheckedModule
  encoded_checked : Expressions.compile (Frontend.Pipeline.inherited prepared.document prepared.resolved)
    (targetBounds (Frontend.Pipeline.inherited prepared.document prepared.resolved) bounds)
    intervals prepared.bodies = .ok encoded
  module_checked : check { encoded.module.raw with facts := encoded.module.raw.facts ++
    [objectBudget (Frontend.Pipeline.inherited prepared.document prepared.resolved) bounds.structural.objects] } = .ok module

def Product.validated (p : Product) : IR.Inherited.Validated p.prepared.resolved.count :=
  Frontend.Pipeline.inherited p.prepared.document p.prepared.resolved

def compile (file source boundsFile boundsText : String)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Product := do
  let p ← Frontend.Pipeline.prepare file source |>.mapError Diagnostic.ofSource
  let v := Frontend.Pipeline.inherited p.document p.resolved
  let b ← bounds boundsFile boundsText
  let b := { b with structural := { b.structural with
    objects := objects.getD b.structural.objects, bitwidth := bitwidth.getD b.structural.bitwidth } }
  let ranges ← intervals boundsFile v b
  let tb := targetBounds v b
  let encoded ← match MonadAttach.attach (Expressions.compile v tb ranges p.bodies) with
    | .ok result => pure result
    | .error error => do
      -- Identify an authored body only when it actually fails; structural and
      -- bounds diagnostics keep their real input location.
      if let .ok _ := Inherited.compile v tb then
        if let .ok _ := Expressions.numericFacts v tb ranges then
          for body in p.bodies do
            if let .error (.source d) := Expressions.encodeBody v
                (Expressions.sourceBounds v tb ranges) body then
              if let some span := body.source then
                throw (Diagnostic.ofSource (Frontend.Constraints.errorAt p.document span d.code
                  "source expression exceeds the selected encoding bounds" d.category))
      throw (backendDiagnostic boundsFile error)
  let raw := { encoded.val.module.raw with
    facts := encoded.val.module.raw.facts ++ [objectBudget v b.structural.objects] }
  let target ← MonadAttach.attach (check raw) |>.mapError fun error => backendDiagnostic boundsFile
    (match error with | .malformedSyntax => .internalTarget | .unsupportedBounds => .unsupportedBounds)
  return ⟨p, b, ranges, encoded.val, target.val, encoded.property, target.property⟩

end ClaferCompiler.Driver.Source
