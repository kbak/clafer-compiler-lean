module

public import ClaferCompiler.Frontend.Parser
public import ClaferCompiler.Frontend.Constraints
public import ClaferCompiler.Backend.Alloy.ExpressionAttachments

@[expose] public section
/-! [impl->req~compiler-pipeline-correctness~1]
[impl->req~compiler-telematics~1] -/
namespace ClaferCompiler.Frontend.Pipeline

def inheritedCore (doc : Document) (c : Resolution.Candidate n) : IR.Inherited.Core n := {
  structural := c.core
  explicitAbstract := Vector.ofFn (Resolution.explicitAbstract doc c)
  realizationRank := c.realizationRank }

/-- The accepted frontend certificate discharges inherited admission directly. -/
def inherited (doc : Document) (e : Resolution.Elaborated doc) : IR.Inherited.Validated e.count where
  core := inheritedCore doc e.candidate
  certificate := e.candidate.certificate
  coreChecked := e.correspondence.1
  selectedChecked := by
    have hs := e.correspondence.2.2.2.2.2.2.2.2.2
    have hi := e.correspondence.2.2.2.2.2.2.1
    have hr := e.correspondence.2.2.2.2.2.2.2.1
    have hp := e.correspondence.2.2.2.2.2.2.2.2.1
    rcases hs with ⟨allowed, primitive, unique, nested, explicit, parentless, supers⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, allowed, ?_, unique, nested⟩
    · simpa [inheritedCore] using explicit
    · simpa [inheritedCore] using parentless
    · intro d s h
      exact ⟨by simpa [inheritedCore] using supers d s h, (hi d s h).2.2.1, (hi d s h).2.2.2.1⟩
    · exact hr
    · intro d c _ h
      exact (hi c d h).2.2.2.2
    · intro d p _ h
      exact hp d p h
    · intro d h
      exact ⟨(primitive d h).1, (primitive d h).2.1, (primitive d h).2.2.1⟩

def body {n : Nat} {doc : Document} {c : Resolution.Candidate n}
    (id : Nat) (a : (o : Constraints.Occurrence doc c) × Constraints.Attached doc c o) :
    Backend.Alloy.Expressions.Body n := {
  id, owner := a.1.owner, source := some a.1.expression.span
  mapCount := a.2.layout.count, support := a.2.layout.support
  term := a.2.body.checked.term }

/-- Retain the document and independent frontend derivations across the backend
handoff. Original source occurrences are not reconstructed from emitted facts. -/
structure Prepared where
  document : Document
  resolved : Resolution.Elaborated document
  attachments : List ((o : Constraints.Occurrence document resolved.candidate) ×
    Constraints.Attached document resolved.candidate o)
  attachments_checked : Constraints.elaborate document resolved = .ok attachments

def Prepared.bodies (p : Prepared) : List (Backend.Alloy.Expressions.Body p.resolved.count) :=
  p.attachments.zipIdx.map fun (a, id) => body id a

def prepare (file source : String) : Except Diagnostic Prepared := do
  let doc ← parse file source
  let e ← Resolution.elaborate doc
  let attachments ← MonadAttach.attach (Constraints.elaborate doc e)
  return ⟨doc, e, attachments.val, attachments.property⟩

end ClaferCompiler.Frontend.Pipeline
