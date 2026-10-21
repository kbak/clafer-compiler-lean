module

public import ClaferCompiler.Correctness.PipelineFacts
public import ClaferCompiler.Correctness.PipelineAtoms

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

theorem scalar_signature (v : IR.Inherited.Validated n) (d : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) :
    ∃ decl, (scalarSchema v (Structural.schema v.layout)).signatures[Structural.signatureId v.layout d]? =
      some decl ∧ decl.scalar = true := by
  have hmem : Structural.signatureId v.layout d ∈ scalarIds v := by
    simp only [scalarIds, List.mem_map, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq]
    exact ⟨d, hd, rfl⟩
  simp only [scalarSchema, List.getElem?_map, List.getElem?_zipIdx,
    Structural.schema_signature, Option.map_some, Nat.zero_add]
  exact ⟨_, rfl, List.contains_iff_mem.mpr hmem⟩

theorem scalarIds_singleton (v : IR.Inherited.Validated n) (d : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) :
    scalarIds v = [Structural.signatureId v.layout d] := by
  let ds := (List.finRange n).filter fun e => (v.core.structural.get e).origin == .integer
  have hm : d ∈ ds := by simp [ds, hd]
  have hn : ds.Nodup := (List.nodup_finRange n).filter _
  have hu : ∀ e ∈ ds, e = d := by
    intro e he
    have he' : (v.core.structural.get e).origin = .integer := by simpa [ds] using he
    exact v.selectedChecked.2.2.2.2.2.2.2.2.1 e d he' hd
  have he : ds = [d] := by
    cases hs : ds with
    | nil => simp [hs] at hm
    | cons a tail =>
      have ha : a = d := hu a (by simp [hs])
      have ht : tail = [] := List.eq_nil_iff_forall_not_mem.mpr (by
        intro e he
        have heq := hu e (by simp [hs, he])
        have hnot := (List.nodup_cons.mp (hs ▸ hn)).1
        exact hnot (by simpa [ha, heq] using he))
      simp [ha, ht]
  change ds.map (Structural.signatureId v.layout) = _
  rw [he]; rfl

theorem scalarIds_empty (v : IR.Inherited.Validated n)
    (h : ∀ d, (v.core.structural.get d).origin ≠ .integer) : scalarIds v = [] := by
  simp [scalarIds, List.filter_eq_nil_iff, h]

theorem scalar_rows (p : Driver.Source.Product) (i : Instance)
    (h : ObservationFacts p i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin = .integer) :
    (∀ row ∈ i.values[Structural.signatureId p.validated.layout d]?.getD [],
      row.1 ∈ i.signatures[Structural.signatureId p.validated.layout d]?.getD [] ∧
      p.intervals[d].Contains row.2) ∧
    ((i.values[Structural.signatureId p.validated.layout d]?.getD []).map Prod.fst).Nodup ∧
    (∀ a ∈ i.signatures[Structural.signatureId p.validated.layout d]?.getD [],
      ∃ z, (a, z) ∈ i.values[Structural.signatureId p.validated.layout d]?.getD []) ∧
    (∀ row ∈ i.values[Structural.signatureId p.validated.layout d]?.getD [],
      ∀ other ∈ i.values[Structural.signatureId p.validated.layout d]?.getD [],
      row.2 = other.2 → row.1 = other.1) := by
  obtain ⟨decl, hdecl, hflag⟩ := scalar_signature p.validated d hd
  obtain ⟨htyped, hkeys, htotal⟩ := ExpressionMeaning.scalar_field_rows i _ _ _ decl hdecl hflag
    h.scalarFields
  obtain ⟨base,_,_,hn,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  obtain ⟨hfit,hfacts⟩ := ExpressionMeaning.numericFacts_member _ _ _ _ hn d hd
  obtain ⟨hrange, hinj⟩ := ExpressionMeaning.scalarFacts_enforce i _ _ _ decl hdecl hflag
    h.scalarFields p.intervals[d] hfit (fun fact hf => h.numeric fact (hfacts fact hf))
  exact ⟨fun row hm => ⟨(htyped row hm).1, hrange row hm⟩, hkeys, htotal, hinj⟩

/-- Actual emitted totality and injectivity facts justify decoding integer
identity. This is derived from target satisfaction, not a representation axiom. -/
theorem decoded_atoms_injective (p : Driver.Source.Product) (i : Instance)
    (h : ObservationFacts p i) : Function.Injective (decodeAtom (scalarRows p.validated i)) := by
  by_cases hp : ∃ d, (p.validated.core.structural.get d).origin = .integer
  · obtain ⟨d, hd⟩ := hp
    have hr : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
      simp [scalarRows, scalarIds_singleton p.validated d hd]
    rw [hr]
    exact atom_injective _ (scalar_rows p i h d hd).2.2.2
  · have hz : scalarRows p.validated i = [] := by
      simp [scalarRows, scalarIds_empty p.validated (by simpa using hp)]
    rw [hz]
    exact atom_injective _ (by simp)

theorem target_atom_encoding (p : Driver.Source.Product) (i : Instance)
    (h : ObservationFacts p i) :
    ∃ f : Atom → Nat, Function.Injective f ∧
      ∀ a ∈ i.signatures[0]?.getD [], f (decodeAtom (scalarRows p.validated i) a) = a :=
  exists_encoding _ _ (decoded_atoms_injective p i h)

end ClaferCompiler.Correctness.Pipeline
