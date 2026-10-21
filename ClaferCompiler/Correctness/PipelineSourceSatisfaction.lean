module

public import ClaferCompiler.Correctness.PipelineSoundness

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr ExpressionMeaning

def SourceBodies (p : Driver.Source.Product)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core) state)
    (R : FormalCD.IntegerRealization Atom)
    (primitive : ∀ d, (p.validated.core.structural.get d).origin = .integer → state.head d = R.domain) : Prop :=
  ∀ (entry) (he : entry ∈ p.encoded.bodies),
    ∃ ht : entry.original.term.Typed entry.original.support [] .boolean,
      ∀ owner ∈ state.head entry.original.owner,
        (interpret entry.original.support entry.original.term.raw ht).denote
          (fullBinding p.validated entry.original.support (originalResolved p entry he) state hs R primitive)
          (Clafer.Constraints.Environment.closed owner) = some ⟨True⟩

/-- Independent source satisfaction: actual upstream inherited structure and
integer domains, with original terms interpreted on their full owner heads. -/
def SourceSat (p : Driver.Source.Product)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (R : FormalCD.IntegerRealization Atom) : Prop :=
  ∃ hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core) state,
  ∃ primitive : ∀ d, (p.validated.core.structural.get d).origin = .integer → state.head d = R.domain,
    SourceBodies p state hs R primitive

theorem completed_owners (p : Driver.Source.Product) (i : Instance)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (decoded : Backend.Alloy.Inherited.decode p.validated i = .ok o) (live : ObservationLive o)
    (d : Fin p.prepared.resolved.count) (hd : (p.validated.core.structural.get d).origin = .integer)
    (g : Structural.Objects o ↪ Atom) (labels : ∀ x, g x = decodeAtom (scalarRows p.validated i) x.val)
    (R : FormalCD.IntegerRealization Atom)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    (completePrimitive (Structural.realize o root) d g R.domain).head entry.original.owner =
      atomSet (candidateObservation p i entry.original.support).objects[entry.original.owner] := by
  have hne : entry.original.owner ≠ d := by
    intro heq
    exact original_owner_nonprimitive p entry he (heq.symm ▸ hd)
  rw [← decoded_observation p i o decoded entry.original.support]
  rw [observed_objects_source p.validated entry.original.support o root live _ g labels]
  simp only [completePrimitive,ite_eq_right hne]

/-- Whole-model soundness on the actual full owner domains. Source occurrences
are exactly those of Prepared by encoded_occurrences and source_occurrences. -/
theorem source_sound (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer) :
    ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧
    ∃ hr : o.root ∈ o.objects, ∃ g : Structural.Objects o ↪ Atom,
    ∃ R : FormalCD.IntegerRealization Atom,
      (∀ x, g x = decodeAtom (scalarRows p.validated i) x.val) ∧
      (∀ z ∈ (scalarRows p.validated i).map Prod.snd, R.encode z = .integer z) ∧
      FullStructure p d o hr g R ∧
      SourceSat p (completePrimitive (Structural.realize o hr) d g R.domain) R := by
  obtain ⟨o,ho,hr,g,labels,R,fixed,full⟩ := compiled_full_structure p i hs d hd
  obtain ⟨o',ho',hr',⟨rep⟩,finite⟩ := decoded_structure p i hs
  have he : o' = o := Except.ok.inj (ho'.symm.trans ho)
  subst o'
  have live := decoded_live p.validated i o ho rep.live
  have vals := decoded_values p i (observation_facts p i hs) d hd o hr ho g labels
  refine ⟨o,ho,hr,g,R,labels,fixed,full,full.satisfies,completed_primitive_domains p.validated d hd o hr g R,?_⟩
  intro entry he
  have obs := decoded_observation p i o ho entry.original.support
  have valid : ObservationValid entry.original.support
      (observe p.validated entry.original.support o (scalarRows p.validated i)) := by
    rw [obs]
    exact candidate_valid p i (observation_facts p i hs) entry he
  have agree := completed_model_agreement p.validated entry.original.support (originalResolved p entry he)
    d hd (source_primitive_shape p d hd) o hr live finite (scalarRows p.validated i) g labels R
    full.primitive fixed vals.1 vals.2 full.satisfies valid
  have agree' : QueryAgreement p.validated.core.structural entry.original.support
      (candidateObservation p i entry.original.support) (candidate_valid p i (observation_facts p i hs) entry he)
      (fullBinding p.validated entry.original.support (originalResolved p entry he) _ full.satisfies R
        (completed_primitive_domains p.validated d hd o hr g R)) := by
    simpa only [obs] using agree
  obtain ⟨ht,hbody⟩ := (query_body_iff p i (observation_facts p i hs) entry he _ agree').mpr
    (source_constraints p i hs entry he)
  refine ⟨ht,?_⟩
  rw [completed_owners p i o hr ho live d hd g labels R entry he]
  exact hbody

end ClaferCompiler.Correctness.Pipeline
