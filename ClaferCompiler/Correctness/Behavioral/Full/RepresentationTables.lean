module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationIdentities

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral (sameTables sameRelation)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encodeState_object_agrees (v : IR.BehavioralStructural.Validated k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (values : Vector Int o) (state : Instance)
    (wf : state.wellFormed (schema v).declarations = true)
    (objects : ∀ label, label ∈ state.signatures[0]?.getD [] ↔ ∃ x : Fin o, label = ids.ids[x])
    (pools : ∀ d label, label ∈ state.signatures[signatureId d]?.getD [] ↔
      ∃ x : Fin o, ids.directType[x] = d ∧ label = ids.ids[x])
    (parents : ∀ row, row ∈ state.fields[0]?.getD [] ↔
      ∃ x p : Fin o, ids.parent[x] = some p ∧ row = [ids.ids[x], ids.ids[p]])
    (lives : ∀ row, row ∈ state.fields[1]?.getD [] ↔
      ∃ x : Fin o, frame.live[x] = true ∧ row = [ids.ids[ids.root], ids.ids[x]])
    (references : ∀ d row, row ∈ state.fields[2 + d.val]?.getD [] ↔
      ∃ x y : Fin o, (d, x, y) ∈ frame.references ∧ row = [ids.ids[x], ids.ids[y]]) :
    (sameTables state.signatures (encodeState ids frame values).signatures &&
      sameTables state.fields (encodeState ids frame values).fields) = true := by
  obtain ⟨sigLen, fieldLen⟩ := table_lengths v state wf
  have encSig : (encodeState ids frame values).signatures.length = k + 1 := by
    simp [encodeState]
  have encField : (encodeState ids frame values).fields.length = k + 2 := by
    simp [encodeState, Nat.add_comm, Nat.add_left_comm]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply sameTables_complete _ _ (sigLen.trans encSig.symm)
    intro i label
    by_cases hi : i < k + 1
    · by_cases hzero : i = 0
      · subst i
        rw [objects]
        simp only [encodeState, List.getElem?_cons_zero, Option.getD_some]
        constructor
        · rintro ⟨x, rfl⟩
          simp
        · intro h
          obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
          exact ⟨⟨i, by simpa using hi⟩, he.symm⟩
      · obtain ⟨d, rfl⟩ := signatureId_surjective i (by omega) hi
        rw [pools, encode_direct]
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq]
        constructor <;> rintro ⟨x, hx, he⟩ <;> exact ⟨x, hx, he.symm⟩
    · have ha : state.signatures[i]? = none := List.getElem?_eq_none (by omega)
      have hb : (encodeState ids frame values).signatures[i]? = none := List.getElem?_eq_none (by omega)
      simp [ha, hb]
  · apply sameTables_complete _ _ (fieldLen.trans encField.symm)
    intro i row
    by_cases hi : i < k + 2
    · cases i with
      | zero =>
        rw [parents]
        simp only [encodeState, List.getElem?_append, List.length_cons, List.length_nil,
          Nat.zero_lt_succ, ↓reduceIte, List.getElem?_cons_zero, Option.getD_some,
          List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, Option.mem_toList]
        constructor
        · rintro ⟨x, p, hp, he⟩
          exact ⟨x, p, hp, he.symm⟩
        · rintro ⟨x, p, hp, he⟩
          exact ⟨x, p, hp, he.symm⟩
      | succ i =>
        cases i with
        | zero =>
          rw [lives]
          simp only [encodeState, List.getElem?_append, List.length_cons, List.length_nil,
            Nat.lt_add_one, ↓reduceIte, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.getD_some, List.mem_map, List.mem_filter,
            List.mem_finRange, true_and]
          constructor <;> rintro ⟨x, hx, he⟩ <;> exact ⟨x, hx, he.symm⟩
        | succ j =>
          let d : Fin k := ⟨j, by omega⟩
          have he : j + 1 + 1 = 2 + d.val := by dsimp [d]; omega
          rw [he, references, encode_references]
          simp only [List.mem_map, List.mem_filter, beq_iff_eq]
          constructor
          · rintro ⟨x, y, hxy, hrow⟩
            exact ⟨(d, x, y), ⟨hxy, rfl⟩, hrow.symm⟩
          · rintro ⟨⟨e, x, y⟩, ⟨hxy, he⟩, hrow⟩
            change e = d at he
            subst e
            exact ⟨x, y, hxy, hrow.symm⟩
    · have ha : state.fields[i]? = none := List.getElem?_eq_none (by omega)
      have hb : (encodeState ids frame values).fields[i]? = none := List.getElem?_eq_none (by omega)
      simp [ha, hb]

theorem encodeState_agrees (v : IR.BehavioralStructural.Validated k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (values : Vector Int o) (state : Instance)
    (wf : state.wellFormed (schema v).declarations = true)
    (objects : ∀ label, label ∈ state.signatures[0]?.getD [] ↔ ∃ x : Fin o, label = ids.ids[x])
    (pools : ∀ d label, label ∈ state.signatures[signatureId d]?.getD [] ↔
      ∃ x : Fin o, ids.directType[x] = d ∧ label = ids.ids[x])
    (parents : ∀ row, row ∈ state.fields[0]?.getD [] ↔
      ∃ x p : Fin o, ids.parent[x] = some p ∧ row = [ids.ids[x], ids.ids[p]])
    (lives : ∀ row, row ∈ state.fields[1]?.getD [] ↔
      ∃ x : Fin o, frame.live[x] = true ∧ row = [ids.ids[ids.root], ids.ids[x]])
    (references : ∀ d row, row ∈ state.fields[2 + d.val]?.getD [] ↔
      ∃ x y : Fin o, (d, x, y) ∈ frame.references ∧ row = [ids.ids[x], ids.ids[y]])
    (scalars : ∀ row, row ∈ state.values[0]?.getD [] ↔ ∃ x : Fin o, row = (ids.ids[x], values[x])) :
    sameState state (encodeState ids frame values) = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨encodeState_object_agrees v ids frame values state wf objects pools parents lives references, ?_⟩
  apply sameTables_complete _ _ (by simp only [List.length_cons, List.length_nil])
  intro i row
  cases i with
  | zero =>
    change row ∈ state.values[0]?.getD [] ↔ row ∈ (List.finRange o).map (fun x => (ids.ids[x], values[x]))
    rw [scalars]
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx.symm⟩
  | succ i => rfl

end ClaferCompiler.Correctness.Behavioral.Full
