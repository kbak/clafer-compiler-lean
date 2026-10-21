module

public import ClaferCompiler.Correctness.PipelineDecoded

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr Frontend
open SemanticsBridge.Expr ExpressionMeaning

/-- Properties of the actual authored bodies, recovered through the compiler's
occurrence equality. These are not additional admission assumptions. -/
theorem original_body_properties (p : Driver.Source.Product)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    Constraints.Resolved p.validated.core.structural entry.original.support ∧
    entry.original.support.context = entry.original.owner ∧
    entry.original.term.Typed entry.original.support [] .boolean ∧
    entry.original.term.Observed entry.original.support ∧
    NavigationOnly p.validated.core.structural entry.original.support entry.original.term.raw := by
  have hm : entry.original ∈ p.prepared.bodies := by
    rw [← encoded_occurrences p]
    exact List.mem_map.mpr ⟨entry,he,rfl⟩
  obtain ⟨⟨a,k⟩,_,ha⟩ := List.mem_map.mp hm
  change Pipeline.body k a = entry.original at ha
  rw [← ha]
  exact ⟨a.2.layout.resolved,a.2.layout.context,a.2.body.checked.typed,
    a.2.body.checked.observed,elaborated_navigation a.2.body.derivation trivial⟩

/-- Synthetic primitive declarations have no authored constraints. -/
theorem original_owner_nonprimitive (p : Driver.Source.Product)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    (p.validated.core.structural.get entry.original.owner).origin ≠ .integer := by
  have hm : entry.original ∈ p.prepared.bodies := by
    rw [← encoded_occurrences p]
    exact List.mem_map.mpr ⟨entry,he,rfl⟩
  obtain ⟨⟨a,k⟩,_,ha⟩ := List.mem_map.mp hm
  change Pipeline.body k a = entry.original at ha
  rw [← ha]
  intro hp
  let c := p.prepared.resolved.candidate
  let doc := p.prepared.document
  have checked := p.prepared.resolved.correspondence
  change Resolution.Elaboration doc c at checked
  have notRoot := (source_primitive_shape p a.1.owner hp).notRoot
  change a.1.owner ≠ c.core.root at notRoot
  have row := checked.2.2.2.2.1 a.1.owner
  have hp' : (c.core.get a.1.owner).origin = .integer := hp
  simp only [ite_eq_right notRoot,ite_eq_left hp'] at row
  have empty : Resolution.constraints doc c a.1.owner = [] := by
    simp [Resolution.constraints,notRoot,row.1]
  have lt := a.1.group.isLt
  change a.1.group.val < (Resolution.constraints doc c a.1.owner).length at lt
  have len := congrArg List.length empty
  simp only [List.length_nil] at len
  omega

theorem originalResolved (p : Driver.Source.Product)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    Constraints.Resolved p.validated.core.structural entry.original.support :=
  (original_body_properties p entry he).1

/-- Transfer body truth, including all original owners, by a denotation equality
that is proved independently of either side's truth. -/
theorem query_body_iff (p : Driver.Source.Product) (i : Instance) (hs : ObservationFacts p i)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support entry.original.support) Atom)
    (hm : QueryAgreement p.validated.core.structural entry.original.support
      (candidateObservation p i entry.original.support) (candidate_valid p i hs entry he) model) :
    SourceHolds entry.original (candidateObservation p i entry.original.support) model ↔
      SourceHolds entry.original (candidateObservation p i entry.original.support)
        (candidateModel p i hs entry he) := by
  have props := original_body_properties p entry he
  have hb := target_observation_bounded p i hs 0 _ _ _ (bodyLayout_bound p entry he)
  have eq (ht : entry.original.term.Typed entry.original.support [] .boolean)
      (owner : Atom) (ho : owner ∈ atomSet (candidateObservation p i entry.original.support).objects[entry.original.owner]) :=
    query_agreement (candidate_valid p i hs entry he) hb model hm entry.original.term.raw ht
      props.2.2.2.2 props.2.2.2.1 (Clafer.Constraints.Environment.closed owner)
      (show Correctness.Expressions.RecordedEnvironment (candidateObservation p i entry.original.support)
        (Clafer.Constraints.Environment.closed owner) from by
          constructor
          · simpa only [Clafer.Constraints.Environment.closed,props.2.1] using ho
          · intro k v; cases v)
  unfold SourceHolds
  constructor
  · rintro ⟨ht,h⟩; exact ⟨ht,fun owner ho => (eq ht owner ho).symm.trans (h owner ho)⟩
  · rintro ⟨ht,h⟩; exact ⟨ht,fun owner ho => (eq ht owner ho).trans (h owner ho)⟩

end ClaferCompiler.Correctness.Pipeline
