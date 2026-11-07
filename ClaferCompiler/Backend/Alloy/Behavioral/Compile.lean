module

public import ClaferCompiler.Backend.Alloy.Behavioral.Expressions

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral

structure Bounds extends Structural.Bounds where
  minSteps : Nat
  maxSteps : Nat

def owner (v : IR.Structural.Layout k) (a : IR.Behavioral.Attachment k) : Fin k :=
  ((List.finRange k).find? fun d => (v.core.get d).id == a.owner).getD v.core.root

/-- Bind a frozen enumeration covering the shared pool. Repeated aliases pad
small pools, so an upper identity bound never forces exactly that many objects. -/
def coverPool (capacity : Nat) (body : TFormula) : TFormula :=
  let aliases := (List.range capacity).map Temporal.Rel.var
  let cover := Temporal.Formula.equal (aliases.foldl Temporal.Rel.union (.empty .unary)) (.sig 0)
  Nat.repeat (Temporal.Formula.exists_ (.sig 0)) capacity (.binary .conj cover body)

-- [impl->req~compiler-behavioral-encoding~1]
def attached (v : IR.Structural.Layout k) (capacity : Nat) (d : Fin k)
    (a : IR.Behavioral.Formula k 0) (fuel : Nat) (enough : sizeOf a < fuel) : TFormula :=
  let context : Context 0 :=
    ⟨.var 0, Fin.elim0, (List.range capacity).map fun i => .var (i + 1)⟩
  coverPool capacity (.unary .always (.all (head v d)
    (formulaAt v fuel context a enough).positive))

def attachment (v : IR.Behavioral.Admitted k) (capacity fuel : Nat)
    (a : {a // a ∈ v.document.attachments})
    (enough : ∀ f, a.val.body = .formula f → sizeOf f < fuel) : TFormula :=
  match h : a.val.body with
  | .formula f => attached v.structural.toLayout capacity
      (owner v.structural.toLayout a.val) f fuel (enough f h)
  | .unsupported _ => False.elim (by
      have hs := (v.bodiesChecked a.val a.property).2
      simp [h] at hs)

def target (v : IR.Behavioral.Admitted k) (b : Bounds) (scopes : List Scope)
    (fuel : Nat) (enough : ∀ a ∈ v.document.attachments,
      ∀ f, a.body = .formula f → sizeOf f < fuel) : Temporal.Module where
  schema := schema v.structural.toLayout
  facts := identityFacts v.structural.toLayout ++
    (stateFacts v.structural.toLayout).map (.unary .always) ++
    v.document.attachments.attach.map (fun a => attachment v b.objects fuel a
      (enough a.val a.property))
  command := { scopes, bitwidth := b.bitwidth, minSteps := b.minSteps, maxSteps := b.maxSteps }

structure DeclarationMap where
  id : IR.Structural.DeclId
  name : String
  source : Option IR.Structural.SourceSpan
  signature : Nat
  /-- Containment is a live view of the shared parent field, not a field ID. -/
  containment : Option Temporal.Rel
  dereference : Option Nat

def declarationMap (v : IR.Structural.Layout k) (d : Fin k) : DeclarationMap where
  id := (v.core.get d).id
  name := (v.core.get d).name
  source := (v.core.get d).source
  signature := Structural.signatureId v d
  containment := (v.core.get d).parent.map fun _ => contains v d
  dereference := (v.core.get d).reference.target.map fun _ => 2 + d.val

structure Compiled where
  module : Temporal.CheckedModule
  declarations : List DeclarationMap
  attachments : List Nat

-- [impl->req~compiler-behavioral-encoding~1]
/-- Explicit first-slice compilation. Invalid bounds and target errors retain
the existing typed outcomes; compilation does not run a solver. -/
def compile (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments,
      ∀ f, a.body = .formula f → sizeOf f < fuel) : Except Structural.Error Compiled := do
  let scopes ← Structural.resolveScopes v.structural.toLayout b.toBounds
  match Temporal.check (target v b scopes fuel enough) with
  | .error .malformedSyntax => .error .internalTarget
  | .error .unsupportedBounds => .error .unsupportedBounds
  | .ok checked => .ok ⟨checked, (List.finRange k).map (declarationMap v.structural.toLayout),
      v.document.attachments.map (·.id)⟩

end ClaferCompiler.Backend.Alloy.Behavioral
