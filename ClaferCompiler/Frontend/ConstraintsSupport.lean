module

public import ClaferCompiler.Frontend.Surface
public import ClaferCompiler.IR.Expr

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr

abbrev ValidWiden (s : Support n m) (x y : Fin n) (p : Widen n m) : Prop := p.path.Valid s x y
instance (s : Support n m) (x y : Fin n) (p : Widen n m) : Decidable (ValidWiden s x y p) :=
  widenAt s p.budget p.path p.bound x y

/-- The original declaration, role and endpoints determine a map; names do not. -/
def MapResolved (c : IR.Structural.Core n) (e : MapRef n) : Prop :=
  ∃ i : Fin n, e.owner = (c.get i).id ∧
    match e.kind with
    | .head => (c.get i).parent = some e.source ∧ i = e.target
    | .parent => i = e.source ∧ (c.get i).parent = some e.target
    | .dereference => i = e.source ∧ (c.get i).reference.target = some e.target
    | .inclusion => i = e.source ∧ (c.get i).super = some e.target
    | .target => (c.get i).parent = some e.source ∧
        (c.get i).reference.target = some e.target

instance (c : IR.Structural.Core n) (e : MapRef n) : Decidable (MapResolved c e) := by
  unfold MapResolved
  cases e.kind <;> infer_instance

def Resolved (c : IR.Structural.Core n) (s : Support n m) : Prop :=
  (∀ i : Fin n, s.classes[i] = (c.get i).id) ∧
  (∀ i : Fin n, s.integer[i] = decide ((c.get i).origin = .integer)) ∧
  (∀ e : Fin m, MapResolved c s.maps[e])

instance (c : IR.Structural.Core n) (s : Support n m) : Decidable (Resolved c s) := by
  unfold Resolved
  infer_instance

structure Layout (c : IR.Structural.Core n) (owner : Fin n) where
  count : Nat
  support : Support n count
  resolved : Resolved c support
  context : support.context = owner

def layout (c : IR.Structural.Core n) (owner : Fin n) : Except String (Layout c owner) := do
  let maps := (List.finRange n).flatMap fun i =>
    let d := c.get i
    (d.parent.toList.flatMap fun p => [⟨d.id, .head, p, i, d.name⟩,
      ⟨d.id, .parent, i, p, "parent"⟩]) ++
    (d.reference.target.toList.map fun t => ⟨d.id, .dereference, i, t, "dref"⟩) ++
    (d.super.toList.map fun t => ⟨d.id, .inclusion, i, t, "super"⟩)
  let s : Support n maps.length := {
    classes := Vector.ofFn fun i => (c.get i).id
    maps := ⟨maps.toArray, by simp⟩
    context := owner
    integer := Vector.ofFn fun i => decide ((c.get i).origin = .integer) }
  if h : Resolved c s then return ⟨_, s, h, rfl⟩
  else throw "constraint.internal-support"

/-- Finite super paths are checked by the existing typed-core path validator. -/
def superPaths (s : Support n m) (x : Fin n) : List (Fin n × Widen n m) :=
  (List.range n).foldl (fun paths _ =>
    match paths.getLast? with
    | none => paths
    | some (y, p) =>
      match (List.finRange m).find? (fun e => s.maps[e].kind == .inclusion && s.maps[e].source == y) with
      | none => paths
      | some e => paths ++ [(s.maps[e].target, .trans y p (.inclusion e))]) [(x, .same)]

def errorAt (doc : Document) (span : SourceSpan) (code message : String)
    (category : Category := .malformed) (related : Array SourceSpan := #[]) : Diagnostic :=
  let before := String.fromUTF8! (doc.source.toUTF8.extract 0 span.startByte)
  let lines := before.splitOn "\n"
  { code, phase := "type", category, message, primary := span,
    line := lines.length, column := (lines.getLast!).length + 1, related }

end ClaferCompiler.Frontend.Constraints
