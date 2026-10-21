module

public import ClaferCompiler.Correctness.PipelineConstraints

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionMeaning

/-- Exact finite-candidate completeness. Given structural/numeric data fitting
the compiled scopes, all independent source bodies plus the explicit ordinary
object budget suffice for target satisfaction. The representation is constructed
inside `candidate_constraint_iff`; none is assumed by this theorem. -/
theorem candidate_complete (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i)
    (budget : (Driver.Source.objectBudget p.validated p.bounds.structural.objects).eval
      p.bounds.structural.bitwidth i [] = some true)
    (source : ∀ (entry) (he : entry ∈ p.encoded.bodies),
      SourceHolds entry.original (candidateObservation p i entry.original.support)
        (candidateModel p i hs entry he)) : Satisfies p.module.raw i := by
  obtain ⟨base,hb,hbase⟩ := hs.structural
  obtain ⟨qs,_,hraw,_⟩ := Inherited.compile_output _ _ _ hb
  obtain ⟨actual,ha,_,_,hf,hc⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  have hsame : actual = base := Except.ok.inj (ha.symm.trans hb)
  subst actual
  have heq := module_eq p
  have hschema := compiled_schema _ _ _ _ _ p.encoded_checked
  have hshape : p.module.raw = {
      schema := scalarSchema p.validated (Structural.schema p.validated.layout)
      facts := base.module.raw.facts ++ p.encoded.numericFacts ++
        p.encoded.bodies.map EncodedBody.formula ++
        [Driver.Source.objectBudget p.validated p.bounds.structural.objects]
      command := { scopes := qs, bitwidth := p.bounds.structural.bitwidth } } := by
    rw [heq]
    cases hm : p.encoded.module.raw
    simp only [hm] at hschema hf hc ⊢
    simp only [hraw, Backend.Alloy.Inherited.target, Structural.target] at hc
    cases hschema
    cases hf
    cases hc
    rfl
  refine ⟨p.module.typed,p.module.bounded,?_,?_,?_,?_⟩
  · rw [hshape]
    rw [scalarSchema_wellFormed]
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbase.2.2.1
  · rw [hshape]
    rw [scalarSchema_declarations]
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbase.2.2.2.1
  · simpa only [hshape,hraw,Backend.Alloy.Inherited.target,Structural.target] using hbase.2.2.2.2.1
  · rw [hshape]
    apply (Inherited.run_eval _ _ _ _ i hs.scalarFields).mpr
    intro fact hfact
    rcases List.mem_append.mp hfact with hprior | hbudget
    · rcases List.mem_append.mp hprior with hprior | hbody
      · rcases List.mem_append.mp hprior with hstruct | hnum
        · have hh := Module.fact_true _ _ hbase.2.2.2.2.2 fact hstruct
          simpa only [hraw,Backend.Alloy.Inherited.target,Structural.target,Driver.Source.targetBounds] using hh
        · exact hs.numeric fact hnum
      · obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hbody
        exact (candidate_constraint_iff p i hs entry he).mpr (source entry he)
    · have hfact := List.mem_singleton.mp hbudget
      simpa only [hfact] using budget

/-- Soundness and bounded completeness for the same concrete candidate, with
false/undefined source constraints allowed on the right. The integer binding
has all integers; structural realization below is the finite observation. -/
theorem candidate_iff (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) :
    Satisfies p.module.raw i ↔
      (Driver.Source.objectBudget p.validated p.bounds.structural.objects).eval
        p.bounds.structural.bitwidth i [] = some true ∧
      ∀ (entry) (he : entry ∈ p.encoded.bodies),
        SourceHolds entry.original (candidateObservation p i entry.original.support)
          (candidateModel p i hs entry he) := by
  constructor
  · intro ht
    constructor
    · have hmem : Driver.Source.objectBudget p.validated p.bounds.structural.objects ∈ p.module.raw.facts := by
        rw [module_eq p]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hh := Module.fact_true _ _ ht.2.2.2.2.2 _ hmem
      simpa only [module_eq p, compiled_width p] using hh
    · exact source_constraints p i ht
  · rintro ⟨budget,hsource⟩
    exact candidate_complete p i hs budget hsource

/-- Unconditional composition at the current proved boundary: successful source
compilation and target satisfaction construct the finite inherited model and
establish every original body's full-integer denotation on its observed maps.
A unified infinite rooted structural extension is not asserted here. -/
theorem compiled_sound (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) :
    (∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
        (Structural.realize o hr)) ∧
    (∀ (entry) (he : entry ∈ p.encoded.bodies),
      SourceHolds entry.original (candidateObservation p i entry.original.support)
        (candidateModel p i (observation_facts p i hs) entry he)) := by
  obtain ⟨o,ho,hr,_,hsource⟩ := decoded_structure p i hs
  exact ⟨⟨o,ho,hr,hsource⟩,source_constraints p i hs⟩

end ClaferCompiler.Correctness.Pipeline
