module

public import ClaferCompiler.SemanticsBridge.Behavioral.Trace

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral
open IR.Behavioral

-- [impl->req~compiler-behavioral-interpretation~1]
/-- Attachment uses stable declaration identity and all live ancestor views.
It never changes the context to its parent. -/
def contexts (m : IR.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (owner : IR.Structural.DeclId) (t : Nat) : Set U :=
  {x | ∃ d : Fin k, (m.get d).id = owner ∧
    x ∈ (τ.raw (Structural.interpret m) t).head d}

def Attached (m : IR.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (owner : IR.Structural.DeclId) (a : Formula k 0) : Prop :=
  (formula a).Attached τ (.sets (Structural.interpret m) τ) (contexts m τ owner)

-- [proof->req~compiler-behavioral-interpretation~1]
theorem attached_normalize_lower (m : IR.Structural.Core k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (owner : IR.Structural.DeclId)
    (a : Formula k 0) (fuel : Nat) (enough : sizeOf a < fuel) :
    Attached m τ owner a ↔ ∀ t c, c ∈ contexts m τ owner t → c ∈ τ.live t →
      (formula (a.normalize true fuel enough)).lower.eval τ (.sets (Structural.interpret m) τ) (.closed c) t := by
  rw [normalize_interpret]
  exact Clafer.Behavioral.Formula.attached_lower_agrees _ _ _ _

theorem attachment_preserved (a : Attachment k) (fuel : Nat)
    (enough : ∀ f, a.body = .formula f → sizeOf f < fuel) :
    (a.normalize fuel enough).id = a.id ∧ (a.normalize fuel enough).owner = a.owner ∧
    (a.normalize fuel enough).kind = a.kind ∧ (a.normalize fuel enough).source = a.source := ⟨rfl, rfl, rfl, rfl⟩

theorem admitted_attachment (v : Admitted k) (a : Attachment k)
    (ha : a ∈ v.document.attachments) :
    (∃ d : Fin k, (v.document.core.get d).id = a.owner) ∧
    a.kind = .constraint ∧ ∃ f, a.body = .formula f := by
  refine ⟨(v.metadataChecked.2.1 a ha).1, (v.bodiesChecked a ha).1, ?_⟩
  have h := (v.bodiesChecked a ha).2
  cases hb : a.body with
  | formula f => exact ⟨f, rfl⟩
  | unsupported name => simp [hb] at h

theorem contexts_resolved (v : Admitted k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (d : Fin k) (t : Nat) :
    contexts v.document.core τ (v.document.core.get d).id t =
    (τ.raw (Structural.interpret v.document.core) t).head d := by
  ext x
  constructor
  · rintro ⟨e, he, hx⟩
    have := v.coreChecked.1 e d he
    subst e
    exact hx
  · intro hx
    exact ⟨d, rfl, hx⟩

end ClaferCompiler.SemanticsBridge.Behavioral
