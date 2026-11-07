module

public import ClaferCompiler.Backend.Alloy.Structural
public import ClaferCompiler.Backend.Alloy.Behavioral.Operators
public import ClaferCompiler.IR.Behavioral.Trace

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral

-- [impl->req~compiler-behavioral-encoding~1]
/-- Pools and actual parents are static; live membership and references vary.
The static M1 allocation continues to identify declarations, including heads. -/
def pool (v : IR.Structural.Layout k) (d : Fin k) : Temporal.Rel :=
  .sig (Structural.signatureId v d)

/-- An inherited pool also contains subtype identities. Actual type is the
remainder after removing immediate subtype pools. -/
def directPool (v : IR.Structural.Layout k) (d : Fin k) : Temporal.Rel :=
  .diff (pool v d) ((Structural.subtypes v.core d).map (pool v) |>.foldl
    Temporal.Rel.union (.empty .unary))

def root (v : IR.Structural.Layout k) : Temporal.Rel := pool v v.core.root
def parent : Temporal.Rel := .field 0
def live (v : IR.Structural.Layout k) : Temporal.Rel := .join (root v) (.field 1)
def head (v : IR.Structural.Layout k) (d : Fin k) : Temporal.Rel :=
  .inter (pool v d) (live v)
def deref (d : Fin k) : Temporal.Rel := .field (2 + d.val)

def contains (v : IR.Structural.Layout k) (d : Fin k) : Temporal.Rel :=
  match (v.core.get d).parent with
  | none => .empty .binary
  | some _ => .inter (.transpose parent) (.product (live v) (head v d))

def step (v : IR.Structural.Layout k) : IR.Behavioral.Step k → Temporal.Rel
  | .parent => .inter parent (.product (.sig 0) (live v))
  | .child d => contains v d
  | .deref d => .inter (deref d) (.product (live v) (live v))

def schema (v : IR.Structural.Layout k) : Temporal.Schema where
  declarations :=
    { signatures := (Structural.schema v).signatures
      fields := [{ owner := 0, target := 0 },
        { owner := Structural.signatureId v v.core.root, target := 0 }] ++
        (List.finRange k).map (fun _ => { owner := 0, target := 0 }) }
  mutableSignatures := List.replicate (k + 1) false
  mutableFields := [false, true] ++ List.replicate k true

/-- Interpret the existing static backend's relations in a live snapshot. -/
def snapshotRel (v : IR.Structural.Layout k) (r : Alloy.Rel) : Temporal.Rel :=
  r.fold {
    empty := Temporal.Rel.empty
    sig := fun id => if id == 0 then live v else
      .inter (.sig id) (live v)
    field := fun id => match (Structural.fieldKeys v.core)[id]? with
      | some (d, .containment) => contains v d
      | some (d, .dereference) => deref d
      | none => .empty .binary
    var := Temporal.Rel.var
    union := Temporal.Rel.union, inter := Temporal.Rel.inter, diff := Temporal.Rel.diff
    product := Temporal.Rel.product, join := Temporal.Rel.join
    transpose := Temporal.Rel.transpose
    diagonal := fun r => .inter .iden (.product r r) } (.empty .unary)

def snapshotInteger (v : IR.Structural.Layout k) (i : Alloy.Integer) : Temporal.Integer :=
  i.fold {
    literal := Temporal.Integer.literal
    count := fun r => .count (snapshotRel v r)
    -- No scalar constructor occurs in the admitted M1 backend.
    scalar := fun _ lo _ _ => .literal lo
    add := Temporal.Integer.add, subtract := Temporal.Integer.subtract } (.literal 0)

def snapshotFormula (v : IR.Structural.Layout k) (f : Alloy.Formula) : Temporal.Formula :=
  f.fold {
    truth := .truth, falsity := .falsity
    equal := fun a b => .equal (snapshotRel v a) (snapshotRel v b)
    subset := fun a b => .subset (snapshotRel v a) (snapshotRel v b)
    mult := fun m r => .mult m (snapshotRel v r)
    compare := fun op a b => .compare op (snapshotInteger v a) (snapshotInteger v b)
    neg := .unary .neg, conj := .binary .conj, disj := .binary .disj
    implies := .binary .implies
    all := fun r p => .all (snapshotRel v r) p
    exists_ := fun r p => .exists_ (snapshotRel v r) p } .falsity

/-- Snapshot declarations made explicit because only the identity pools are
target signatures. Source extents are their current live restrictions. -/
def snapshotDeclarations (v : IR.Structural.Layout k) : List Temporal.Formula :=
  (List.finRange k).flatMap fun d =>
    let row := v.core.get d
    let inclusion := row.super.toList.map fun p =>
      Temporal.Formula.subset (head v d) (head v p)
    let containment := row.parent.toList.map fun p =>
      Temporal.Formula.subset (contains v d) (.product (head v p) (head v d))
    let reference := match row.reference.target with
      | none => Temporal.Formula.equal (deref d) (.empty .binary)
      | some target => .binary .conj
          (.subset (deref d) (.product (head v d) (head v target)))
          (.all (head v d) (.mult .one (.join (.var 0) (deref d))))
    inclusion ++ containment ++ [reference]

-- [impl->req~compiler-behavioral-encoding~1]
def identityFacts (v : IR.Structural.Layout k) : List Temporal.Formula :=
  [.mult .one (root v),
   .equal (.join (root v) parent) (.empty .unary),
   .all (.diff (.sig 0) (root v)) (.mult .one (.join (.var 0) parent))] ++
  (List.finRange k).flatMap fun d =>
    if (v.core.get d).isAbstract then
      [.equal (pool v d) ((Structural.subtypes v.core d).map (pool v) |>.foldl
        Temporal.Rel.union (.empty .unary))]
    else
      match (v.core.get d).parent with
      | none => []
      | some p => [.all (directPool v d) (.subset (.join (.var 0) parent) (pool v p))]

def stateFacts (v : IR.Structural.Layout k) : List Temporal.Formula :=
  [.subset (root v) (live v), .subset (.join (live v) parent) (live v)] ++
  snapshotDeclarations v ++
  (Structural.facts v).map (fun (_, f) => snapshotFormula v f)

end ClaferCompiler.Backend.Alloy.Behavioral
