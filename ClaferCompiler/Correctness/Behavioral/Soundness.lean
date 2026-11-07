module

public import ClaferCompiler.Correctness.Behavioral.SnapshotRepresentation
public import ClaferCompiler.Correctness.Behavioral.SnapshotGeneration
public import ClaferCompiler.Correctness.Behavioral.ExpressionsAttachment
public import ClaferCompiler.SemanticsBridge.Behavioral.Attachment

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

theorem stateFacts_built (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (f : Temporal.Formula) (hf : f ∈ stateFacts v) : f.Built := by
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact .subset _ _
      · have he := List.mem_singleton.mp hf
        subst f
        exact .subset _ _
    · exact snapshotDeclarations_built v f hf
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    exact snapshotFormula_built v
      (snapshot_facts v _ (snapshotState_wellFormed v w τ wf) q hq)

namespace Encoding

theorem resolveScopes_objects (v : IR.Structural.Layout k) (b : Alloy.Structural.Bounds)
    (scopes : List Scope) (h : Alloy.Structural.resolveScopes v b = .ok scopes) :
    scopes[0]? = some {size := b.objects} := by
  unfold Alloy.Structural.resolveScopes at h
  split at h
  · cases h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h
      rfl

variable (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
  (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
  (c : Compiled) (hc : compile v b fuel enough = .ok c)
  (τ : Temporal.Trace) (sat : Temporal.Satisfies c.module.raw τ)

include hc sat

theorem compiled_declarations : τ.Declarations (schema v.structural.toLayout) := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at sat
  exact sat.2.2.1

theorem compiled_schema : (Alloy.Structural.schema v.structural.toLayout).wellFormed = true := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at sat
  apply static_schema_wellFormed
  have hw := sat.1
  simp only [Temporal.Module.wellTyped, Temporal.Schema.wellFormed, Bool.and_eq_true] at hw
  exact hw.1.1.1.1.1

theorem compiled_states (t : Nat) (f : Temporal.Formula)
    (hf : f ∈ stateFacts v.structural.toLayout) :
    f.Holds (schema v.structural.toLayout) b.bitwidth τ [] t :=
  compiled_state_holds v b fuel enough c hc τ sat f hf
    (stateFacts_built v.structural.toLayout b.bitwidth τ
      ((compiled_declarations v b fuel enough c hc τ sat).2.1 t).1 f hf) t

theorem compiled_snapshot_declarations (t : Nat) :
    (snapshotState v.structural.toLayout b.bitwidth τ t).declarations
      (Alloy.Structural.schema v.structural.toLayout) = true := by
  have decl := (compiled_declarations v b fuel enough c hc τ sat).2.1 t
  apply snapshotState_declarations _ _ _ decl.1 decl.2.1
  intro f hf
  exact compiled_states v b fuel enough c hc τ sat t f
    (List.mem_append_left _ (List.mem_append_right _ hf))

-- [proof->req~compiler-behavioral-correctness~1]
/-- The actual temporal output entails the existing structural backend's
declarations and every generated fact on each concrete live projection. -/
theorem compiled_snapshot_facts (t : Nat) :
    Structural.FactModel v.structural.toLayout
      (snapshotState v.structural.toLayout b.bitwidth τ t) b.bitwidth := by
  refine ⟨compiled_schema v b fuel enough c hc τ sat,
    compiled_snapshot_declarations v b fuel enough c hc τ sat t, ?_⟩
  intro f hf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
  have frame := ((compiled_declarations v b fuel enough c hc τ sat).2.1 t).1
  have wf := snapshotState_wellFormed v.structural.toLayout b.bitwidth τ frame
  have emitted : snapshotFormula v.structural.toLayout q.2 ∈ stateFacts v.structural.toLayout :=
    List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
  exact snapshot_fact_value _ _ _ frame wf q hq
    ⟨compiled_state_defined v b fuel enough c hc τ sat _ emitted
      (snapshotFormula_built _ (snapshot_facts _ _ wf q hq)) t,
      compiled_states v b fuel enough c hc τ sat t _ emitted⟩

end Encoding

namespace TraceRep
variable {v : IR.Behavioral.Admitted k} {source : IR.Behavioral.Lasso k o steps}
  {target : Temporal.Lasso}

theorem compiled_capacity (rep : TraceRep v.structural.toLayout source target)
    (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (sat : Temporal.Satisfies c.module.raw target.unfold) : o ≤ b.objects := by
  classical
  obtain ⟨scopes, hs, hout, _, _⟩ := Encoding.compile_output v b fuel enough c hc
  rw [hout] at sat
  obtain ⟨used, hn, hm, hsize⟩ := sat.2.2.2.1 0 {size := b.objects}
    (Encoding.resolveScopes_objects v.structural.toLayout b.toBounds scopes hs)
  have subset : Finset.univ.image rep.label ⊆ used.toFinset := by
    intro label hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hl
    exact List.mem_toFinset.mpr ((hm _).mpr ⟨0, (rep.objects x).property⟩)
  have cardinal := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ rep.label_injective,
    Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hn] at cardinal
  exact Nat.le_trans cardinal hsize

-- [proof->req~compiler-behavioral-correctness~1]
theorem compiled_valid (rep : TraceRep v.structural.toLayout source target)
    (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (sat : Temporal.Satisfies c.module.raw target.unfold)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y) :
    (trace source).Valid (SemanticsBridge.Structural.interpret v.document.core) := by
  classical
  have states := Encoding.compiled_states v b fuel enough c hc target.unfold sat
  apply rep.source_valid b.bitwidth unique
    (Encoding.compiled_identity_holds v b fuel enough c hc target.unfold sat) states
  intro t
  have rl := rep.root_live b.bitwidth t (states t)
  have frame := ((Encoding.compiled_declarations v b fuel enough c hc target.unfold sat).2.1 t).1
  have fm := Encoding.compiled_snapshot_facts v b fuel enough c hc target.unfold sat t
  have repr := rep.snapshotRep b.bitwidth t frame fm.schema fm.declarations (states t) rl
  exact stateValid_of_liveSnapshot _ _ t rl (rep.references_live b.bitwidth t (states t))
    (Structural.represented_sound_facts _ _ _ repr b.bitwidth fm)

-- [proof->req~compiler-behavioral-correctness~1]
theorem compiled_attached (rep : TraceRep v.structural.toLayout source target)
    (b : Bounds) (capacity : o ≤ b.objects) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (sat : Temporal.Satisfies c.module.raw target.unfold)
    (a : IR.Behavioral.Attachment k) (ha : a ∈ v.document.attachments)
    (f : IR.Behavioral.Formula k 0) (hf : a.body = .formula f) :
    Attached v.document.core (trace source) a.owner f := by
  have truth := (rep.attached_meaning b.bitwidth b.objects capacity
    (owner v.structural.toLayout a) f fuel (enough a ha f hf)).mp
      (Encoding.compiled_attachment_holds v b fuel enough c hc target.unfold sat a ha f hf)
  intro t x hx _
  rw [← Encoding.owner_id v a ha, contexts_resolved v] at hx
  exact truth t x hx

end TraceRep
end ClaferCompiler.Correctness.Behavioral
