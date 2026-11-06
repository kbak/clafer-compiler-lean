module

public import ClaferCompiler.IR.Behavioral.Syntax

@[expose] public section
namespace ClaferCompiler.IR.Behavioral
open Structural

inductive RequestedBody (k : Nat) where
  | formula (body : Formula k 0)
  | unsupported (constructor : String)

inductive AttachmentKind where
  | constraint | assertion | scenario
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-ir~1]
structure Attachment (k : Nat) where
  id : Nat
  owner : DeclId
  kind : AttachmentKind := .constraint
  body : RequestedBody k
  source : Option SourceSpan := none

-- [impl->req~compiler-behavioral-interpretation~1]
def Attachment.normalize (a : Attachment k) (fuel : Nat)
    (enough : ∀ f, a.body = .formula f → sizeOf f < fuel) : Attachment k :=
  { a with body := match h : a.body with
      | .formula f => .formula (f.normalize true fuel (enough f h))
      | .unsupported name => .unsupported name }

structure Document (k : Nat) where
  version : String
  profile : String
  core : Core k
  certificate : Certificate k
  attachments : List (Attachment k)

def Attachment.Valid (core : Core k) (a : Attachment k) : Prop :=
  (∃ d : Fin k, (core.get d).id = a.owner) ∧
  (∀ span ∈ a.source, span.startByte ≤ span.endByte)

instance (core : Core k) (a : Attachment k) : Decidable (a.Valid core) := by
  unfold Attachment.Valid
  infer_instance

def Attachment.Supported (a : Attachment k) : Prop :=
  a.kind = .constraint ∧ match a.body with
    | .formula _ => True
    | .unsupported _ => False

instance (a : Attachment k) : Decidable a.Supported := by
  unfold Attachment.Supported
  cases a.body <;> infer_instance

def metadataChecks (d : Document k) : Prop :=
  (d.attachments.map (·.id)).Nodup ∧
  (∀ a ∈ d.attachments, a.Valid d.core) ∧
  ∀ i : Fin k, ∀ s ∈ (d.core.get i).source, s.startByte ≤ s.endByte

instance (d : Document k) : Decidable (metadataChecks d) := by
  unfold metadataChecks
  infer_instance

def supportedBodies (d : Document k) : Prop := ∀ a ∈ d.attachments, a.Supported
instance (d : Document k) : Decidable (supportedBodies d) := by
  unfold supportedBodies
  infer_instance

-- [impl->req~compiler-behavioral-ir~1]
/-- Retains the exact original document, including authored/effective provenance. -/
structure Admitted (k : Nat) where
  document : Document k
  version : document.version = "clafer-behavioral-ir/1"
  profile : document.profile = "behavioral-core/1"
  coreChecked : coreChecks document.core document.certificate
  supportChecked : supportChecks document.core document.certificate
  metadataChecked : metadataChecks document
  bodiesChecked : supportedBodies document

def Admitted.structural (v : Admitted k) : Validated k :=
  ⟨v.document.core, v.document.certificate, v.coreChecked, v.supportChecked⟩

-- [impl->req~compiler-behavioral-ir~1]
/-- Explicit, closed first-slice admission; it does not check model satisfaction. -/
def admitBehavioral (d : Document k) : Except Diagnostic (Admitted k) :=
  if hv : d.version = "clafer-behavioral-ir/1" then
    if hp : d.profile = "behavioral-core/1" then
      if hc : coreChecks d.core d.certificate then
        if hs : supportChecks d.core d.certificate then
          if hm : metadataChecks d then
            if hb : supportedBodies d then .ok ⟨d, hv, hp, hc, hs, hm, hb⟩
            else .error ⟨.unsupported, "behavioral.constructor", "/attachments", none⟩
          else .error ⟨.malformed, "behavioral.metadata", "", none⟩
        else .error ⟨.unsupported, "behavioral.structural-profile", "/declarations", none⟩
      else .error ⟨.malformed, "behavioral.core", "/declarations", none⟩
    else .error ⟨.unsupported, "behavioral.profile", "/profile", none⟩
  else .error ⟨.unsupported, "behavioral.version", "/version", none⟩

end ClaferCompiler.IR.Behavioral
