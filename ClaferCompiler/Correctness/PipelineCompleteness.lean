module

public import ClaferCompiler.Correctness.PipelineSourceSatisfaction
public import ClaferCompiler.Correctness.PipelineFiniteCompleteness
public import ClaferCompiler.Correctness.PipelineRestriction

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionMeaning

/-- Concrete finite observation of a full source configuration, in the common
atom universe. All fields are equations about objects, maps and integer values;
none mentions satisfaction, formula evaluation or preservation. -/
structure Observes (p : Driver.Source.Product) (d : Fin p.prepared.resolved.count)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (R : FormalCD.IntegerRealization Atom)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (g : Structural.Objects o ↪ Atom) : Prop where
  structure_eq : state = completePrimitive (Structural.realize o root) d g R.domain
  labels : ∀ x, g x = decodeAtom (scalarRows p.validated (encodeObservation p o values)) x.val
  primitive : ∀ x, g x ∈ R.domain ↔ x ∈ (Structural.realize o root).head d
  containment : ∀ x y, (Structural.realize o root).contains d x y ↔
    x = (Structural.realize o root).root ∧ y ∈ (Structural.realize o root).head d
  integers : ∀ z ∈ (scalarRows p.validated (encodeObservation p o values)).map Prod.snd,
    R.encode z = .integer z

/-- The bounded source contract adds finite capacities to the observation data.
In particular it does not contain target truth or finite source satisfaction. -/
def Fits (p : Driver.Source.Product) (d : Fin p.prepared.resolved.count)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (R : FormalCD.IntegerRealization Atom)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (g : Structural.Objects o ↪ Atom) : Prop :=
  Observes p d state R o root values g ∧ FiniteFits p o root values

/-- Bounded completeness starts with the independently defined full source
satisfaction and data-only Fits. The actual executable target is constructed,
its finite structural truth is derived by restriction, and every emitted fact
is proved. No target-satisfaction or representation premise is assumed. -/
theorem source_complete (p : Driver.Source.Product) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer)
    (state : Clafer.Semantics.Configuration (Fin p.prepared.resolved.count) Atom)
    (R : FormalCD.IntegerRealization Atom)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (g : Structural.Objects o ↪ Atom)
    (source : SourceSat p state R) (fits : Fits p d state R o root values g) :
    ∃ i, encodeObservation p o values = i ∧
      Backend.Alloy.Inherited.decode p.validated i = .ok o ∧ Satisfies p.module.raw i := by
  obtain ⟨obs,finiteFits⟩ := fits
  have stateEq := obs.structure_eq
  subst state
  obtain ⟨hs,primitive,bodies⟩ := source
  let i := encodeObservation p o values
  have finite := restricted_structure _ (Structural.realize o root) d (source_primitive_shape p d hd)
    g R.domain obs.primitive obs.containment hs
  have facts := finite_observation_facts p o root values finiteFits finite
  have decoded := encode_observation_decode p o values finiteFits.table finiteFits.rootHead root
  have vals := decoded_values p i facts d hd o root decoded g obs.labels
  refine ⟨i,rfl,decoded,candidate_complete p i facts (finite_budget p o root values finiteFits) ?_⟩
  intro entry he
  have oe := decoded_observation p i o decoded entry.original.support
  have valid : ObservationValid entry.original.support
      (observe p.validated entry.original.support o (scalarRows p.validated i)) := by
    rw [oe]
    exact candidate_valid p i facts entry he
  have agree := completed_model_agreement p.validated entry.original.support (originalResolved p entry he)
    d hd (source_primitive_shape p d hd) o root finiteFits.live finite (scalarRows p.validated i)
    g obs.labels R obs.primitive obs.integers vals.1 vals.2 hs valid
  have agree' : QueryAgreement p.validated.core.structural entry.original.support
      (candidateObservation p i entry.original.support) (candidate_valid p i facts entry he)
      (fullBinding p.validated entry.original.support (originalResolved p entry he) _ hs R primitive) := by
    simpa only [oe] using agree
  apply (query_body_iff p i facts entry he _ agree').mp
  obtain ⟨ht,hbody⟩ := bodies entry he
  refine ⟨ht,?_⟩
  rw [completed_owners p i o root decoded finiteFits.live d hd g obs.labels R entry he] at hbody
  exact hbody

end ClaferCompiler.Correctness.Pipeline
