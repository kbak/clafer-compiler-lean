module

public import ClaferCompiler.Correctness.PipelineSourceShape
public import ClaferCompiler.Correctness.PipelineScalars

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

/-- Actual scalar rows supply an embedding of the decoded finite carrier into
the common atom universe. Objects outside the primitive keep ordinary identity. -/
theorem observed_embedding (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer)
    (o : Structural.Observation p.prepared.resolved.count) (hr : o.root ∈ o.objects)
    (decoded : Backend.Alloy.Inherited.decode p.validated i = .ok o) :
    ∃ g : Structural.Objects o ↪ Atom,
      (∀ x, g x = decodeAtom (scalarRows p.validated i) x.val) ∧
      (∀ x, x ∉ (Structural.realize o hr).head d → ∃ a, g x = .object a) := by
  let g : Structural.Objects o ↪ Atom := ⟨
    fun x => decodeAtom (scalarRows p.validated i) x.val,
    (decoded_atoms_injective p i hs).comp Subtype.val_injective⟩
  refine ⟨g,fun _ => rfl,?_⟩
  intro x hx
  refine ⟨x.val,?_⟩
  apply atom_object
  intro z hz
  have rows : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
    simp [scalarRows,scalarIds_singleton p.validated d hd]
  rw [rows] at hz
  have he := congrArg (fun q : Structural.Observation p.prepared.resolved.count => q.heads d)
    (Structural.decode_success p.validated.layout i o decoded).2.2.2
  apply hx
  change x.val ∈ o.heads d
  rw [he]
  exact ((scalar_rows p i hs d hd).1 _ hz).1

structure FullStructure (p : Driver.Source.Product) (d : Fin p.prepared.resolved.count)
    (o : Structural.Observation p.prepared.resolved.count) (hr : o.root ∈ o.objects)
    (g : Structural.Objects o ↪ Atom) (R : FormalCD.IntegerRealization Atom) : Prop where
  satisfies : Clafer.Semantics.Realization.Satisfies
    (SemanticsBridge.Inherited.interpret p.validated.core)
    (completePrimitive (Structural.realize o hr) d g R.domain)
  primitive : ∀ x, g x ∈ R.domain ↔ x ∈ (Structural.realize o hr).head d
  heads : ∀ e x, g x ∈ (completePrimitive (Structural.realize o hr) d g R.domain).head e ↔
    x ∈ (Structural.realize o hr).head e
  containment : ∀ e x y,
    (completePrimitive (Structural.realize o hr) d g R.domain).contains e (g x) (g y) ↔
    (Structural.realize o hr).contains e x y
  dereference : ∀ e x y,
    (completePrimitive (Structural.realize o hr) d g R.domain).deref e (g x) (g y) ↔
    (Structural.realize o hr).deref e x y

/-- Successful target satisfaction constructs a rooted selected source model
whose primitive head contains all mathematical integers. It agrees with every
observed head/containment/reference tuple under the constructed embedding.
Authored constraint agreement on this full model is a separate obligation. -/
theorem compiled_full_structure (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer) :
    ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧
    ∃ hr : o.root ∈ o.objects, ∃ g : Structural.Objects o ↪ Atom,
    (∀ x, g x = decodeAtom (scalarRows p.validated i) x.val) ∧
    ∃ R : FormalCD.IntegerRealization Atom,
      (∀ z ∈ (scalarRows p.validated i).map Prod.snd, R.encode z = .integer z) ∧
      FullStructure p d o hr g R := by
  obtain ⟨o,ho,hr,_,hsource⟩ := decoded_structure p i hs
  obtain ⟨g,hlabels,hordinary⟩ := observed_embedding p i (observation_facts p i hs) d hd o hr ho
  obtain ⟨R,hfixed,hagree,hfull⟩ := full_integer_structure
    (SemanticsBridge.Inherited.interpret p.validated.core) (Structural.realize o hr) d
    (source_primitive_shape p d hd) hsource g hordinary
    ((scalarRows p.validated i).map Prod.snd).toFinset
  exact ⟨o,ho,hr,g,hlabels,R,fun z hz => hfixed z (List.mem_toFinset.mpr hz),
    hfull,hagree,
    completed_head _ _ _ _ hagree,
    completed_contains _ _ _ (source_primitive_shape p d hd) hsource _ _ hagree,
    completed_deref _ _ _ _⟩

end ClaferCompiler.Correctness.Pipeline
