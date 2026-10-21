module

public import ClaferCompiler.Correctness.PipelineConstruction

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions

/-- The representation boundary checks only structural/numeric data. It does
not require any authored constraint to hold, so violating candidates remain
available for exact comparison. Full target satisfaction implies these facts. -/
structure ObservationFacts (p : Driver.Source.Product) (i : Instance) : Prop where
  structural : ∃ base, Backend.Alloy.Inherited.compile p.validated
    (Driver.Source.targetBounds p.validated p.bounds) = .ok base ∧ Satisfies base.module.raw i
  scalarFields : i.scalarFields p.bounds.structural.bitwidth
    (scalarSchema p.validated (Structural.schema p.validated.layout)) = true
  numeric : ∀ fact ∈ p.encoded.numericFacts,
    fact.eval p.bounds.structural.bitwidth i [] = some true

theorem compiled_width (p : Driver.Source.Product) :
    p.encoded.module.raw.command.bitwidth = p.bounds.structural.bitwidth := by
  obtain ⟨base,hb,_,_,_,hc⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  obtain ⟨scopes,_,hraw,_⟩ := Inherited.compile_output _ _ _ hb
  rw [hc,hraw]
  rfl

theorem observation_facts (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) : ObservationFacts p i := by
  have he := encoded_satisfies p i hs
  refine ⟨inherited_reduct p i hs, ?_, ?_⟩
  · have hf := module_scalarFields _ _ he.2.2.2.2.2
    simpa only [compiled_schema _ _ _ _ _ p.encoded_checked, compiled_width p, Driver.Source.Product.validated] using hf
  · intro fact hfact
    obtain ⟨base,_,_,_,hf,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
    have hm : fact ∈ p.encoded.module.raw.facts := by
      rw [hf]
      exact List.mem_append_left _ (List.mem_append_right _ hfact)
    simpa only [compiled_width p] using Module.fact_true _ _ he.2.2.2.2.2 fact hm

theorem observed_structure (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) :
    ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Structural.Represents p.validated.layout (Structural.realize o hr) i) ∧
      Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
        (Structural.realize o hr) := by
  obtain ⟨base,hb,hbase⟩ := hs.structural
  exact Inherited.compiled_sound _ _ _ hb i hbase

end ClaferCompiler.Correctness.Pipeline
