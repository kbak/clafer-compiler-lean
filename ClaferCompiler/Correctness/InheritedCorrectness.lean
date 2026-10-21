module

public import ClaferCompiler.Correctness.InheritedFacts

@[expose] public section
/-! [proof->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Correctness.Inherited
open Backend.Alloy Backend.Alloy.Inherited IR.Inherited
attribute [local instance] Classical.propDecidable

/-- Target group truth derives the original realized-field group meaning. -/
theorem represented_groups {U : Type} [Fintype U] (v : Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Structural.Represents v.layout s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) :
    Clafer.Semantics.Realization.Groups (SemanticsBridge.Inherited.interpret v.core) s := by
  have hg := (groups_iff v s i r w).mp (fun f hf =>
    Module.fact_true _ _ h.2.2.2.2.2 f (List.mem_append_right _ hf))
  intro d hd p
  exact (hg d hd p.val p.property).2

/-- Every satisfying generated target decodes to the independent selected
inherited meaning. Representation and source truth are constructed. -/
theorem compiled_sound (v : Validated n) (b : Backend.Alloy.Structural.Bounds)
    (c : Compiled) (hc : compile v b = .ok c) (i : Instance)
    (h : Satisfies c.module.raw i) :
    ∃ o, decode v i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Structural.Represents v.layout (Structural.realize o hr) i) ∧
      Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core)
        (Structural.realize o hr) := by
  obtain ⟨scopes, _, he, _, _⟩ := compile_output v b c hc
  rw [he] at h
  have hb := base_satisfies v scopes b.bitwidth i h
  obtain ⟨o, ho⟩ := Structural.satisfying_decode v.layout scopes b.bitwidth i hb
  obtain ⟨hr, ⟨r⟩⟩ := Structural.decoded_represents v.layout i o ho
    (Structural.satisfying_live v.layout scopes b.bitwidth i hb)
  refine ⟨o, ho, hr, ⟨r⟩, (SemanticsBridge.Inherited.satisfies_iff v.core _).mpr ?_⟩
  exact ⟨Structural.represented_sound v.layout _ i r scopes b.bitwidth hb,
    represented_groups v _ i r scopes b.bitwidth h⟩

/-- Every finite satisfying selected source fitting explicit scopes and integer
observations has a concrete target. No copied field or target truth is assumed. -/
theorem compiled_complete {U : Type} [Fintype U] (v : Validated n)
    (b : Backend.Alloy.Structural.Bounds) (c : Compiled) (hc : compile v b = .ok c)
    (s : Clafer.Semantics.Configuration (Fin n) U)
    (h : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core) s)
    (scopes : Structural.ObservationScopesFit v.layout c.module.raw.command.scopes
      (Structural.sourceObservation s)) (counts : CountFits v s b.bitwidth) :
    ∃ i, encode v (Structural.sourceObservation s) = i ∧
      Nonempty (Structural.Represents v.layout s i) ∧ Satisfies c.module.raw i := by
  let i := encode v (Structural.sourceObservation s)
  have hs := (SemanticsBridge.Inherited.satisfies_iff v.core s).mp h |>.1
  let r := Structural.source_represents v.layout s hs.1 hs.2.1
  refine ⟨i, rfl, ⟨r⟩, ?_⟩
  obtain ⟨qs, _, he, _, _⟩ := compile_output v b c hc
  have typed := c.module.typed
  have bounded := c.module.bounded
  rw [he] at scopes typed bounded ⊢
  refine ⟨typed, bounded, r.wellFormed, Structural.source_declarations v.layout s i r hs,
    (Structural.observation_inScope v.layout qs _).mpr scopes, ?_⟩
  apply (run_eval _ _ _ _ _).mpr
  rw [List.forall_mem_append]
  constructor
  · intro f hf
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    exact Structural.source_facts v.layout s i r hs b.bitwidth counts.1 q hq
  · apply (groups_iff v s i r b.bitwidth).mpr
    intro d hd p hp
    exact ⟨counts.2 d hd p hp, h.2.2.2.2.1 d hd ⟨p, hp⟩⟩

end ClaferCompiler.Correctness.Inherited
