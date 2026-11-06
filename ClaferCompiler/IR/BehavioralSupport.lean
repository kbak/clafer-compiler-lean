module

public import ClaferCompiler.IR.BehavioralStructural
public import ClaferCompiler.IR.Expr

@[expose] public section
namespace ClaferCompiler.IR.BehavioralSupport
open BehavioralStructural Expr

-- [impl->req~compiler-behavioral-structural-bridge~1]
def role (v : Validated k) (d a b : Fin k) : MapKind → Prop
  | .head => (v.core.structural.get d).parent = some a ∧ b = d
  | .parent => a = d ∧ (v.core.structural.get d).parent = some b
  | .dereference => a = d ∧ ∃ o, v.analysis.referenceOwners[d] = some o ∧
      (v.core.structural.get o).reference.target = some b
  | .target => (v.core.structural.get d).parent = some a ∧
      ∃ o, v.analysis.referenceOwners[d] = some o ∧
        (v.core.structural.get o).reference.target = some b
  | .inclusion => a = d ∧ b ∈ v.analysis.ancestors[d]

instance (v : Validated k) (d a b : Fin k) (kind : MapKind) : Decidable (role v d a b kind) := by
  cases kind <;> unfold role <;> infer_instance

structure Binding (k n m : Nat) where
  classes : Vector (Fin k) n
  owners : Vector (Fin k) m

def Binding.Valid (v : Validated k) (s : Support n m) (b : Binding k n m) : Prop :=
  (∀ x : Fin n, s.classes[x] = (v.core.structural.get b.classes[x]).id) ∧
  (∀ x : Fin n, s.integer[x] = decide ((v.core.structural.get b.classes[x]).origin = .integer)) ∧
  (∀ e : Fin m, s.maps[e].owner = (v.core.structural.get b.owners[e]).id ∧
    role v b.owners[e] b.classes[s.maps[e].source] b.classes[s.maps[e].target] s.maps[e].kind)

instance (v : Validated k) (s : Support n m) (b : Binding k n m) : Decidable (b.Valid v s) := by
  unfold Binding.Valid; infer_instance

structure Checked (v : Validated k) (s : Support n m) where
  binding : Binding k n m
  valid : binding.Valid v s

def resolve (v : Validated k) (s : Support n m) : Except Structural.Diagnostic (Checked v s) := do
  let lookupId := fun id =>
    match Structural.lookup v.core.structural.declarations id with
    | some d => Except.ok d
    | none => Except.error ({category := .malformed, code := "behavioral.support-id", declaration := some id} : Structural.Diagnostic)
  let classes ← s.classes.mapM lookupId
  let owners ← s.maps.mapM (fun e => lookupId e.owner)
  let b := Binding.mk classes owners
  if h : b.Valid v s then return ⟨b, h⟩
  else throw { category := .malformed, code := "behavioral.support-role" }

/-- Reference coercion performs exactly one declared/inherited dereference.
The target's own reference is not implicitly followed a second time. -/
structure ReferenceView (k : Nat) where
  head : Fin k
  owner : Fin k
  target : Fin k
  deriving DecidableEq, Repr

def referenceView (v : Validated k) (d : Fin k) : Option (ReferenceView k) := do
  let o ← v.analysis.referenceOwners[d]
  let t ← (v.core.structural.get o).reference.target
  return ⟨d, o, t⟩

/-- Actual-parent navigation uses the retained identity's parent, including
heterogeneous parentless abstract views. It carries no invented class edge. -/
inductive Navigation (k : Nat) where
  | parent
  | child (declaration : Fin k)
  | dereference (view : ReferenceView k)
  deriving DecidableEq, Repr

def Navigation.Valid (v : Validated k) : Navigation k → Prop
  | .parent => True
  | .child d => (v.core.structural.get d).parent.isSome = true
  | .dereference r => referenceView v r.head = some r

instance (v : Validated k) (s : Navigation k) : Decidable (s.Valid v) := by
  cases s <;> unfold Navigation.Valid <;> infer_instance

end ClaferCompiler.IR.BehavioralSupport
