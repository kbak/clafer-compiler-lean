module

public import ClaferCompiler.Backend.Alloy.Structural
public import ClaferCompiler.Backend.Alloy.Semantics

@[expose] public section
/-! [impl->req~compiler-structural-representation~1] -/

namespace ClaferCompiler.Backend.Alloy.Structural

/-- A finite shared-object presentation. Object labels are opaque; reference
heads retain their own labels even when two heads have the same referent.
This record contains no satisfaction or compilation hypothesis. -/
structure Observation (n : Nat) where
  objects : List Nat
  root : Nat
  heads : Fin n → List Nat
  containment : Fin n → List (Nat × Nat)
  dereference : Fin n → List (Nat × Nat)

/-- Encode the concrete #10 layout. No auxiliary atoms are introduced. -/
def encode (v : IR.Structural.Validated n) (o : Observation n) : Instance where
  signatures := o.objects :: (order v).map o.heads
  fields := (fieldKeys v.core).map fun (d, role) =>
    (match role with | .containment => o.containment d | .dereference => o.dereference d).map
      fun (x, y) => [x, y]

/-- Read only binary tuples. Public decoding checks their arity first. -/
def readPairs (ts : Relation) : List (Nat × Nat) := ts.filterMap fun t =>
  match t with | [x, y] => some (x, y) | _ => none

/-- The declaration map fixes every extent and relation. Missing source roles
have empty relations, rather than accidentally reading field zero. -/
def observation (v : IR.Structural.Validated n) (i : Instance) (root : Nat) : Observation n where
  objects := i.signatures[0]?.getD []
  root
  heads d := i.signatures[signatureId v d]?.getD []
  containment d := readPairs (((v.core.get d).parent.bind fun _ =>
    i.fields[fieldId v.core d .containment]?).getD [])
  dereference d := readPairs (((v.core.get d).reference.target.bind fun _ =>
    i.fields[fieldId v.core d .dereference]?).getD [])

inductive DecodeError where
  | malformedInstance | rootNotSingleton | rootOutsideObjects
  deriving DecidableEq, Repr

/-- Decode raw in-memory target tables. This does not check source truth, invoke
an oracle, or parse Analyzer output. A well-formed violating candidate is retained. -/
def decode (v : IR.Structural.Validated n) (i : Instance) : Except DecodeError (Observation n) :=
  if !i.wellFormed (schema v) then .error .malformedInstance
  else match i.signatures[signatureId v v.core.root]?.getD [] with
    | [root] => if (i.signatures[0]?.getD []).contains root then .ok (observation v i root)
      else .error .rootOutsideObjects
    | _ => .error .rootNotSingleton

end ClaferCompiler.Backend.Alloy.Structural
