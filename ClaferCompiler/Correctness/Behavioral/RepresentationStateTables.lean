module

public import ClaferCompiler.Correctness.Behavioral.RepresentationFrames

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

theorem behavioral_table_lengths (v : IR.Structural.Layout k) (state : Instance)
    (wf : state.wellFormed (schema v).declarations = true) :
    state.signatures.length = k + 1 ∧ state.fields.length = k + 2 := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).1)
  constructor
  · simpa [schema, Structural.schema, Structural.order_length] using beq_iff_eq.mp h.1
  · simpa [schema, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using beq_iff_eq.mp h.2

theorem signatureId_surjective (v : IR.Structural.Layout k) (i : Nat)
    (hpos : 0 < i) (hlt : i < k + 1) : ∃ d, Structural.signatureId v d = i := by
  have hi : i - 1 < (Structural.order v).length := by rw [Structural.order_length]; omega
  refine ⟨(Structural.order v)[i - 1], ?_⟩
  simp only [Structural.signatureId, (Structural.order_nodup v).idxOf_getElem (i - 1)]
  omega

-- [proof->req~compiler-trace-representation~1]
theorem encodeState_agrees (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (state : Instance)
    (wf : state.wellFormed (schema v).declarations = true)
    (objects : ∀ label, label ∈ state.signatures[0]?.getD [] ↔ ∃ x : Fin o, label = ids.ids[x])
    (pools : ∀ d label, label ∈ state.signatures[Structural.signatureId v d]?.getD [] ↔
      ∃ x : Fin o, IR.Behavioral.ancestor v.core ids.directType[x] d = true ∧ label = ids.ids[x])
    (parents : ∀ row, row ∈ state.fields[0]?.getD [] ↔
      ∃ x p : Fin o, ids.parent[x] = some p ∧ row = [ids.ids[x], ids.ids[p]])
    (lives : ∀ row, row ∈ state.fields[1]?.getD [] ↔
      ∃ x : Fin o, frame.live[x] = true ∧ row = [ids.ids[ids.root], ids.ids[x]])
    (references : ∀ d row, row ∈ state.fields[2 + d.val]?.getD [] ↔
      ∃ x y : Fin o, (d, x, y) ∈ frame.references ∧ row = [ids.ids[x], ids.ids[y]]) :
    sameState state (encodeState v ids frame) = true := by
  obtain ⟨sigLen, fieldLen⟩ := behavioral_table_lengths v state wf
  have encSig : (encodeState v ids frame).signatures.length = k + 1 := by
    simp [encodeState, Structural.order_length]
  have encField : (encodeState v ids frame).fields.length = k + 2 := by
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
      · obtain ⟨d, rfl⟩ := signatureId_surjective v i (by omega) hi
        rw [pools, encode_pool]
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and]
        constructor <;> rintro ⟨x, hx, he⟩ <;> exact ⟨x, hx, he.symm⟩
    · have ha : state.signatures[i]? = none := List.getElem?_eq_none (by omega)
      have hb : (encodeState v ids frame).signatures[i]? = none := List.getElem?_eq_none (by omega)
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
      have hb : (encodeState v ids frame).fields[i]? = none := List.getElem?_eq_none (by omega)
      simp [ha, hb]

end ClaferCompiler.Correctness.Behavioral
