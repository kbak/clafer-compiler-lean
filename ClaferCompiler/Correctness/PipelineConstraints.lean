module

public import ClaferCompiler.Correctness.PipelineBounds

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionRelations ExpressionMeaning

/-- Read declaration-indexed expression tables directly from the candidate.
The structural observation's root field is unused by this projection. -/
def candidateObservation (p : Driver.Source.Product) (i : Instance)
    (s : Support p.prepared.resolved.count m) : Observation p.prepared.resolved.count m :=
  observe p.validated s (Structural.observation p.validated.layout i 0) (scalarRows p.validated i)

theorem body_encoded (p : Driver.Source.Product) (entry : EncodedBody p.prepared.resolved.count)
    (he : entry ∈ p.encoded.bodies) :
    encodeBody p.validated (observationBounds p) entry.original = .ok entry := by
  obtain ⟨base,_,hbody,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  have hh := pairs_forall (mapM_pairs _ _ hbody)
    (fun entry => encodeBody p.validated (observationBounds p) entry.original = .ok entry)
    (fun body entry hb => by rw [encodeBody_original _ _ _ _ hb]; exact hb)
  exact hh entry he

theorem body_layout_exists (p : Driver.Source.Product) (entry : EncodedBody p.prepared.resolved.count)
    (he : entry ∈ p.encoded.bodies) :
    ∃ l, bindSupport p.validated entry.original.support entry.original.owner = .ok l := by
  obtain ⟨l,_,hl,_⟩ := encodeBody_output _ _ _ _ (body_encoded p entry he)
  exact ⟨l,hl⟩

noncomputable def bodyLayout (p : Driver.Source.Product) (entry : EncodedBody p.prepared.resolved.count)
    (he : entry ∈ p.encoded.bodies) : Layout p.prepared.resolved.count entry.original.mapCount :=
  Classical.choose (body_layout_exists p entry he)

theorem bodyLayout_bound (p : Driver.Source.Product) (entry : EncodedBody p.prepared.resolved.count)
    (he : entry ∈ p.encoded.bodies) :
    bindSupport p.validated entry.original.support entry.original.owner = .ok (bodyLayout p entry he) :=
  Classical.choose_spec (body_layout_exists p entry he)

theorem candidate_valid (p : Driver.Source.Product) (i : Instance) (hs : ObservationFacts p i)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    ObservationValid entry.original.support (candidateObservation p i entry.original.support) :=
  target_observation_valid p i hs 0 _ _ _ (bodyLayout_bound p entry he)

/-- Construct the accepted full-Int expression binding from original finite
link occurrences. This does not assert full primitive containment/rootedness. -/
def candidateModel (p : Driver.Source.Product) (i : Instance) (hs : ObservationFacts p i)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :=
  extend entry.original.support (candidateObservation p i entry.original.support)
    (candidate_valid p i hs entry he)

noncomputable def bodyRealization (p : Driver.Source.Product) (i : Instance) (hs : ObservationFacts p i)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    Realization p.validated (observationBounds p) entry.original i :=
  let witness := target_layout_rep p i hs
  let f := Classical.choose witness
  let hf := Classical.choose_spec witness
  { layout := bodyLayout p entry he
    bound := bodyLayout_bound p entry he
    observation := candidateObservation p i entry.original.support
    valid := candidate_valid p i hs entry he
    bounded := target_observation_bounded p i hs 0 _ _ _ (bodyLayout_bound p entry he)
    atoms := f
    leaves := hf.2 0 _ _ _ (bodyLayout_bound p entry he)
    model := candidateModel p i hs entry he
    fullExtension := extend_realizes (candidate_valid p i hs entry he) }

/-- Exact per-candidate preservation, including violating/undefined bodies.
All representation premises of #15 are constructed from structural/numeric
facts, independent of the body being compared. -/
theorem candidate_constraint_iff (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (entry : EncodedBody p.prepared.resolved.count)
    (he : entry ∈ p.encoded.bodies) :
    entry.formula.eval p.bounds.structural.bitwidth i [] = some true ↔
      SourceHolds entry.original (candidateObservation p i entry.original.support)
        (candidateModel p i hs entry he) := by
  exact encoded_body_iff _ _ _ _ (body_encoded p entry he) i (bodyRealization p i hs entry he)

/-- Generated target truth entails every original attachment's independent
source denotation. No source-truth or representation premise is assumed. -/
theorem source_constraints (p : Driver.Source.Product) (i : Instance)
    (hs : Satisfies p.module.raw i) :
    ∀ (entry) (he : entry ∈ p.encoded.bodies),
      SourceHolds entry.original (candidateObservation p i entry.original.support)
        (candidateModel p i (observation_facts p i hs) entry he) := by
  intro entry he
  apply (candidate_constraint_iff p i (observation_facts p i hs) entry he).mp
  have hh := encoded_satisfies p i hs
  obtain ⟨base,_,_,_,hf,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  have hm : entry.formula ∈ p.encoded.module.raw.facts := by
    rw [hf]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨entry,he,rfl⟩)
  simpa only [compiled_width p] using Module.fact_true _ _ hh.2.2.2.2.2 _ hm

end ClaferCompiler.Correctness.Pipeline
