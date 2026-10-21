module

public import ClaferCompiler.Correctness.PipelineSourceBodies

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionMeaning

/-- One common full structural configuration and integer realization for every
original attachment. Its maps are constructed from the configuration itself. -/
def FullBodies (p : Driver.Source.Product) (i : Instance)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core) state)
    (R : FormalCD.IntegerRealization Atom)
    (primitive : ∀ d, (p.validated.core.structural.get d).origin = .integer → state.head d = R.domain) : Prop :=
  ∀ (entry) (he : entry ∈ p.encoded.bodies),
    SourceHolds entry.original (candidateObservation p i entry.original.support)
      (fullBinding p.validated entry.original.support (originalResolved p entry he) state hs R primitive)

/-- Source compilation and target satisfaction construct one rooted model with
all mathematical integers, original structural maps, and every authored body.
No representation, integer binding, map agreement or source truth is supplied. -/
theorem compiled_source_sound (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer) :
    ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧
    ∃ hr : o.root ∈ o.objects, ∃ g : Structural.Objects o ↪ Atom,
    ∃ R : FormalCD.IntegerRealization Atom, ∃ full : FullStructure p d o hr g R,
      FullBodies p i (completePrimitive (Structural.realize o hr) d g R.domain)
        full.satisfies R (completed_primitive_domains p.validated d hd o hr g R) := by
  obtain ⟨o,ho,hr,g,labels,R,fixed,full⟩ := compiled_full_structure p i hs d hd
  obtain ⟨o',ho',hr',⟨rep⟩,finite⟩ := decoded_structure p i hs
  have he : o' = o := Except.ok.inj (ho'.symm.trans ho)
  subst o'
  have live := decoded_live p.validated i o ho rep.live
  have vals := decoded_values p i (observation_facts p i hs) d hd o hr ho g labels
  refine ⟨o,ho,hr,g,R,full,?_⟩
  intro entry he
  apply (query_body_iff p i (observation_facts p i hs) entry he _ ?_).mpr
  · exact source_constraints p i hs entry he
  · have obs := decoded_observation p i o ho entry.original.support
    have valid : ObservationValid entry.original.support
        (observe p.validated entry.original.support o (scalarRows p.validated i)) := by
      rw [obs]
      exact candidate_valid p i (observation_facts p i hs) entry he
    have agree := completed_model_agreement p.validated entry.original.support (originalResolved p entry he)
      d hd (source_primitive_shape p d hd) o hr live finite (scalarRows p.validated i) g labels R
      full.primitive fixed vals.1 vals.2 full.satisfies valid
    simpa only [obs] using agree

end ClaferCompiler.Correctness.Pipeline
