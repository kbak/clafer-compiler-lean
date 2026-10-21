module

public import ClaferCompiler.Backend.Alloy.ExpressionAttachments
public import ClaferCompiler.IR.ExprObservation

@[expose] public section
/-! [impl->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Backend.Alloy.Expressions

def scalarRows (v : IR.Inherited.Validated n) (i : Instance) : List (Nat × Int) :=
  (scalarIds v).flatMap fun owner => i.values[owner]?.getD []

def decodeAtom (rows : List (Nat × Int)) (a : Nat) : IR.Expr.Atom :=
  match rows.find? (fun row => row.1 == a) with
  | none => .object a
  | some row => .integer row.2

def observeLinks (g : Nat → IR.Expr.Atom) (pairs : List (Nat × Nat)) : List IR.Expr.Link :=
  pairs.zipIdx.map fun (pair, id) => ⟨id, g pair.1, g pair.2⟩

/-- Read original structural occurrences. Parent roles reverse those occurrences;
inclusion retains shared identity. Target composition retains each head/target
link pair even when multiple bag heads have equal endpoints. -/
def originalPairs (v : IR.Inherited.Validated n) (o : Structural.Observation n)
    (e : IR.Expr.MapRef n) : List (Nat × Nat) :=
  match (List.finRange n).find? (fun d => (v.core.structural.get d).id == e.owner) with
  | none => []
  | some d => match e.kind with
    | .head => o.containment d
    | .parent => (o.containment d).map Prod.swap
    | .dereference => o.dereference d
    | .inclusion => (o.heads d).map fun a => (a, a)
    | .target => (o.containment d).flatMap fun (p, h) =>
        ((o.dereference d).filter fun row => row.1 == h).map fun (_, t) => (p, t)

def observeMap (v : IR.Inherited.Validated n) (o : Structural.Observation n)
    (g : Nat → IR.Expr.Atom) (e : IR.Expr.MapRef n) : List IR.Expr.Link :=
  observeLinks g (originalPairs v o e)

def observe (v : IR.Inherited.Validated n) (s : IR.Expr.Support n m)
    (o : Structural.Observation n) (rows : List (Nat × Int)) : IR.Expr.Observation n m := {
  objects := Vector.ofFn fun d => (o.heads d).map (decodeAtom rows)
  links := Vector.ofFn fun e => observeMap v o (decodeAtom rows) s.maps[e] }

end ClaferCompiler.Backend.Alloy.Expressions
