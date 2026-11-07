module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionState
public import ClaferCompiler.Correctness.Behavioral.RepresentationTables
public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationTarget

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encodeState_wellFormed (v : IR.BehavioralStructural.Validated k) (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o) (values : Vector Int o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (references : f.references.Nodup) :
    (encodeState ids f values).wellFormed (schema v).declarations = true := by
  have hn (d : Fin k) :
      (((List.finRange o).filter fun x => ids.directType[x] == d).map
        fun x => ids.ids[x]).Nodup := List.Nodup.map unique ((List.nodup_finRange o).filter _)
  have parent := encoded_parent_nodup ids unique
  have live := encoded_live_nodup ids f unique
  have refs := encoded_references_nodup ids f unique references
  have good {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (h : xs.Nodup) :
      (xs.eraseDups.length == xs.length) = true := by
    apply beq_iff_eq.mpr
    have he : xs.eraseDups.Perm xs :=
      List.perm_ext_iff_of_nodup (Structural.eraseDups_nodup xs) h |>.mpr (by simp)
    exact he.length_eq
  have binary (rows : List (List Nat)) (h : rows.Nodup)
      (arity : ∀ row ∈ rows, row.length = 2) :
      (rows.eraseDups.length == rows.length && rows.all (fun row => row.length == 2)) = true := by
    rw [good rows h]
    simp only [Bool.true_and, List.all_eq_true, beq_iff_eq]
    exact arity
  unfold Instance.wellFormed
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [encodeState, schema]
  · simp [encodeState, schema]
  · apply List.all_eq_true.mpr
    intro xs hxs
    change xs ∈ ids.ids.toList :: _ at hxs
    rcases List.mem_cons.mp hxs with rfl | hxs
    · exact good _ (labels_nodup ids.ids unique)
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hxs
      exact good _ (hn d)
  · apply List.all_eq_true.mpr
    intro rows hrows
    change rows ∈ [_ , _] ++ _ at hrows
    rcases List.mem_append.mp hrows with hrows | hrows
    · rcases List.mem_cons.mp hrows with rfl | hrows
      · apply binary _ parent
        intro row hr
        obtain ⟨x, _, hrow⟩ := List.mem_flatMap.mp hr
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp hrow
        rfl
      · have he := List.mem_singleton.mp hrows
        subst rows
        apply binary _ live
        intro row hr
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
        rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hrows
      apply binary _ (refs d)
      intro row hr
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr
      rfl


theorem schema_signature_cases (v : IR.BehavioralStructural.Validated k) (i : Nat) (decl : Signature)
    (h : (schema v).declarations.signatures[i]? = some decl) :
    (i = 0 ∧ decl = { isAbstract := true, scalar := true }) ∨
      ∃ d : Fin k, i = signatureId d ∧ decl = { parent := some 0 } := by
  cases i with
  | zero => exact Or.inl ⟨rfl, by simpa [schema] using h.symm⟩
  | succ i =>
    have hi : i < k := by
      have hi := (List.getElem?_eq_some_iff.mp h).1
      simp only [schema, List.length_cons, List.length_map, List.length_finRange] at hi
      omega
    exact Or.inr ⟨⟨i, hi⟩, by simp [signatureId, Nat.add_comm], by
      simpa [schema, hi] using h.symm⟩

theorem encoded_direct_member (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (values : Vector Int o) (d : Fin k) (label : Nat) :
    label ∈ (encodeState ids frame values).signatures[signatureId d]?.getD [] ↔
      ∃ x : Fin o, ids.directType[x] = d ∧ label = ids.ids[x] := by
  simp only [encode_direct, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, beq_iff_eq]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, he.symm⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, he.symm⟩

theorem encodeState_extent_live (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (values : Vector Int o) (j a : Nat)
    (h : a ∈ (encodeState ids frame values).signatures[j]?.getD []) : a ∈ ids.ids.toList := by
  cases j with
  | zero => exact h
  | succ j =>
    simp only [encodeState, List.getElem?_cons_succ, List.getElem?_map] at h
    cases he : (List.finRange k)[j]? with
    | none => simp [he] at h
    | some d =>
      simp only [he, Option.map_some, Option.getD_some, List.mem_map, List.mem_filter] at h
      obtain ⟨x, _, rfl⟩ := h
      simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
      exact ⟨x.val, x.isLt, rfl⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encodeState_declarations (v : IR.BehavioralStructural.Validated k)
    (ids : IR.Behavioral.Identities k o) (frame : IR.Behavioral.Frame k o) (values : Vector Int o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y) :
    (encodeState ids frame values).declarations (schema v).declarations = true := by
  have label_mem (x : Fin o) : ids.ids[x] ∈ ids.ids.toList := by
    simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
    exact ⟨x.val, x.isLt, rfl⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    rintro ⟨decl, i⟩ hi
    have hi := List.mk_mem_zipIdx_iff_getElem?.mp hi
    rcases schema_signature_cases v i decl hi with ⟨rfl, rfl⟩ | ⟨d, rfl, rfl⟩
    · simp only [Id.run, pure, Option.all_none, Bool.true_and, Bool.not_true,
        Bool.false_or, Multiplicity.holds, Bool.and_true, Bool.and_eq_true]
      constructor
      · apply Bool.or_eq_true_iff.mpr
        right
        apply List.all_eq_true.mpr
        intro label member
        obtain ⟨j, hj, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp member)
        let x : Fin o := ⟨j, hj⟩
        apply List.any_eq_true.mpr
        refine ⟨signatureId ids.directType[x], List.mem_map.mpr ⟨_, List.mem_filter.mpr
          ⟨List.mk_mem_zipIdx_iff_getElem?.mpr (schema_signature v ids.directType[x]), rfl⟩, rfl⟩, ?_⟩
        apply List.contains_iff_mem.mpr
        exact (encoded_direct_member ids frame values _ label).mpr ⟨x, rfl, he.symm⟩
      · apply List.all_eq_true.mpr
        rintro ⟨other, j⟩ hj
        rcases schema_signature_cases v j other (List.mk_mem_zipIdx_iff_getElem?.mp hj) with
          ⟨rfl, rfl⟩ | ⟨e, rfl, rfl⟩
        · simp
        · simp
    · simp only [Id.run, pure, Option.all_some, Bool.not_false, Bool.true_or,
        Bool.and_true, Multiplicity.holds, Bool.and_eq_true]
      constructor
      · apply List.all_eq_true.mpr
        intro label member
        exact List.contains_iff_mem.mpr (encodeState_extent_live ids frame values _ label member)
      · apply List.all_eq_true.mpr
        rintro ⟨other, j⟩ hj
        rcases schema_signature_cases v j other (List.mk_mem_zipIdx_iff_getElem?.mp hj) with
          ⟨rfl, rfl⟩ | ⟨e, rfl, rfl⟩
        · simp
        · by_cases same : d = e
          · subst e; simp
          · apply Bool.or_eq_true_iff.mpr
            right
            apply List.all_eq_true.mpr
            intro label member
            simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
            intro otherMember
            obtain ⟨x, hx, he⟩ := (encoded_direct_member ids frame values d label).mp member
            obtain ⟨y, hy, he'⟩ := (encoded_direct_member ids frame values e label).mp otherMember
            have eq : x = y := unique x y (he.symm.trans he')
            subst y
            exact same (hx.symm.trans hy)
  · apply List.all_eq_true.mpr
    rintro ⟨field, j⟩ hj
    have hj := List.mk_mem_zipIdx_iff_getElem?.mp hj
    cases j with
    | zero =>
      have hf : field = { owner := 0, target := 0 } := by simpa [schema] using hj.symm
      subst field
      simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
      refine ⟨?_, fun _ _ => True.intro⟩
      intro row hr
      simp only [encodeState, List.cons_append, List.getElem?_cons_zero, Option.getD_some,
        List.mem_flatMap, List.mem_map, Option.mem_toList] at hr
      obtain ⟨x, _, y, _, rfl⟩ := hr
      exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (label_mem x), List.contains_iff_mem.mpr (label_mem y)⟩
    | succ j => cases j with
      | zero =>
        have hf : field = { owner := 0, target := 0 } := by simpa [schema] using hj.symm
        subst field
        simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
        refine ⟨?_, fun _ _ => True.intro⟩
        intro row hr
        simp only [encodeState, List.cons_append, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, List.mem_map] at hr
        obtain ⟨x, _, rfl⟩ := hr
        exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (label_mem ids.root), List.contains_iff_mem.mpr (label_mem x)⟩
      | succ j =>
        have hj' : j < k := by
          have := (List.getElem?_eq_some_iff.mp hj).1
          simpa [schema] using this
        have hf : field = { owner := 0, target := 0 } := by
          simpa [schema, List.getElem?_append_right, hj'] using hj.symm
        subst field
        simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
        refine ⟨?_, fun _ _ => True.intro⟩
        intro row hr
        rw [show j + 1 + 1 = 2 + (⟨j, hj'⟩ : Fin k).val by change j + 1 + 1 = 2 + j; omega, encode_references] at hr
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr
        exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (label_mem r.2.1), List.contains_iff_mem.mpr (label_mem r.2.2)⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encode_declarations (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps)
    (unique : ∀ x y : Fin o, source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y)
    (refs : ∀ t, (source.objects.at t).references.Nodup) :
    (encode source).unfold.Declarations (schema v) := by
  have decl t := encodeState_declarations v source.objects.identities (source.objects.at t) (source.valuesAt t) unique
  refine ⟨labels_nodup source.objects.identities.ids unique, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [encode_unfold]
    refine ⟨encodeState_wellFormed v source.objects.identities (source.objects.at t) (source.valuesAt t) unique (refs t), decl t, ?_⟩
    intro xs hxs a ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hxs
    exact encodeState_extent_live source.objects.identities (source.objects.at t) (source.valuesAt t) j a (by simp [hj, ha])
  · intro j _ t a
    simp only [encode_unfold, encodeState]
  · intro j hj t row
    have hz : j = 0 := by
      cases j with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => simp [schema] at hj
        | succ j => simp [schema, List.getElem?_replicate] at hj
    subst j
    simp [encodeState]
  · intro i j a b hi hj hij hp t u x hx hy
    apply hij
    apply Structural.declaration_siblings (schema v).declarations
      (encodeState source.objects.identities (source.objects.at 0) (source.valuesAt 0)) (decl 0) i j a b hi hj hp x
    · simpa only [encode_unfold, encodeState] using hx
    · simpa only [encode_unfold, encodeState] using hy

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encode_scalarFields (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps)
    (unique : ∀ x y : Fin o, source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y)
    (w t : Nat) (fits : ∀ x : Fin o, fitsInt w (source.valuesAt t)[x] = true) :
    ((encode source).unfold.state t).scalarFields w (schema v).declarations = true := by
  rw [encode_unfold]
  unfold Instance.scalarFields
  apply List.all_eq_true.mpr
  rintro ⟨decl, i⟩ hi
  rcases schema_signature_cases v i decl (List.mk_mem_zipIdx_iff_getElem?.mp hi) with
    ⟨rfl, rfl⟩ | ⟨d, rfl, rfl⟩
  · simp only [Bool.not_true, Bool.false_or, encodeState, List.getElem?_cons_zero,
      Option.getD_some, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply List.all_eq_true.mpr
      intro row member
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
      apply Bool.and_eq_true_iff.mpr
      refine ⟨List.contains_iff_mem.mpr ?_, fits x⟩
      simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
      exact ⟨x.val, x.isLt, rfl⟩
    · exact decide_eq_true (by
        simpa only [List.map_map, Function.comp_def, List.Nodup] using (List.nodup_finRange o).map unique)
    · apply List.all_eq_true.mpr
      intro label member
      obtain ⟨j, hj, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp member)
      apply List.any_eq_true.mpr
      exact ⟨_, List.mem_map.mpr ⟨⟨j, hj⟩, List.mem_finRange _, rfl⟩, beq_iff_eq.mpr he⟩
  · simp

end ClaferCompiler.Correctness.Behavioral.Full
