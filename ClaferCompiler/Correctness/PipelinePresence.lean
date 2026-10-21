module

public import ClaferCompiler.Correctness.PipelineCompleteness

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Frontend Backend.Alloy Backend.Alloy.Expressions

theorem occurrence_has_constraints (doc : Document) (c : Resolution.Candidate n)
    (a : Constraints.Occurrence doc c) : Resolution.hasConstraints doc c = true := by
  have hmem := List.getElem_mem a.group.isLt
  change (Resolution.constraints doc c a.owner)[a.group] ∈ Resolution.constraints doc c a.owner at hmem
  unfold Resolution.constraints at hmem
  obtain ⟨e,he,hpayload⟩ := List.mem_filterMap.mp hmem
  have here : Resolution.constraintHere
      (if a.owner == c.core.root then doc.elements else (c.paths[a.owner].bind (Resolution.childrenAt doc)).getD []) = true := by
    unfold Resolution.constraintHere
    apply List.any_eq_true.mpr
    refine ⟨e,he,?_⟩
    cases e with
    | declaration => simp at hpayload
    | constraint => rfl
  unfold Resolution.hasConstraints
  simp only [Bool.or_eq_true]
  by_cases hr : a.owner = c.core.root
  · exact .inl (by simpa [hr] using here)
  · apply Or.inr
    apply Vector.any_eq_true.mpr
    exact ⟨a.owner.val,a.owner.isLt,by simpa [hr] using here⟩

/-- Any authored body forces the primitive carrier needed by IntegerBinding.
Constraint-free documents without integer references retain their finite model. -/
theorem body_has_primitive (p : Driver.Source.Product)
    (entry : EncodedBody p.prepared.resolved.count) (he : entry ∈ p.encoded.bodies) :
    ∃ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer := by
  have hm : entry.original ∈ p.prepared.bodies := by
    rw [← encoded_occurrences p]
    exact List.mem_map.mpr ⟨entry,he,rfl⟩
  obtain ⟨⟨a,_⟩,_,_⟩ := List.mem_map.mp hm
  have checked := p.prepared.resolved.correspondence
  have row := checked.2.2.2.2.1 p.prepared.resolved.candidate.core.root
  simp only [↓reduceIte] at row
  exact row.2.2.2.2.2 (occurrence_has_constraints _ _ a.1)

theorem no_primitive_no_bodies (p : Driver.Source.Product)
    (h : ¬ ∃ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer) :
    p.encoded.bodies = [] :=
  List.eq_nil_iff_forall_not_mem.mpr (fun entry he => h (body_has_primitive p entry he))

/-- The no-primitive branch is purely structural and has no authored constraints;
otherwise source_sound supplies the common full-integer configuration. -/
theorem all_source_sound (p : Driver.Source.Product) (i : Instance) (hs : Satisfies p.module.raw i) :
    (p.encoded.bodies = [] ∧ ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧
      ∃ root : o.root ∈ o.objects,
        Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
          (Structural.realize o root)) ∨
    (∃ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer ∧
      ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧
      ∃ root : o.root ∈ o.objects, ∃ g : Structural.Objects o ↪ IR.Expr.Atom,
      ∃ R : FormalCD.IntegerRealization IR.Expr.Atom,
        (∀ x, g x = decodeAtom (scalarRows p.validated i) x.val) ∧
        (∀ z ∈ (scalarRows p.validated i).map Prod.snd, R.encode z = .integer z) ∧
        FullStructure p d o root g R ∧
        SourceSat p (completePrimitive (Structural.realize o root) d g R.domain) R) := by
  by_cases hp : ∃ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer
  · obtain ⟨d,hd⟩ := hp
    exact .inr ⟨d,hd,source_sound p i hs d hd⟩
  · obtain ⟨o,ho,root,_,finite⟩ := decoded_structure p i hs
    exact .inl ⟨no_primitive_no_bodies p hp,o,ho,root,finite⟩

/-- The structural branch has the same data-only finite capacities. -/
theorem constraint_free_complete (p : Driver.Source.Product)
    (empty : p.encoded.bodies = [])
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (fits : FiniteFits p o root values)
    (source : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
      (Structural.realize o root)) : Satisfies p.module.raw (encodeObservation p o values) := by
  apply candidate_complete p _ (finite_observation_facts p o root values fits source)
    (finite_budget p o root values fits)
  intro entry he
  simp [empty] at he

end ClaferCompiler.Correctness.Pipeline
