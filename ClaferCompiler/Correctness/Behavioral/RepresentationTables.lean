module

public import ClaferCompiler.Correctness.Behavioral.Representation
public import ClaferCompiler.Correctness.StructuralRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

theorem labels_nodup (objects : Vector Nat o)
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y) : objects.toList.Nodup := by
  have he : objects.toList = (List.finRange o).map (fun x => objects[x]) := by
    rw [List.finRange, List.map_ofFn]
    change objects.toList = List.ofFn (fun i => objects[i.val])
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [he]
  exact List.Nodup.map unique (List.nodup_finRange o)

theorem encoded_parent_nodup (ids : IR.Behavioral.Identities k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y) :
    ((List.finRange o).flatMap fun x => (ids.parent[x]).toList.map
      fun p => [ids.ids[x], ids.ids[p]]).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro x _
    cases ids.parent[x] <;> simp
  · apply (List.nodup_finRange o).imp
    intro x y hxy
    apply List.disjoint_left.mpr
    intro row hx hy
    obtain ⟨p, _, hp⟩ := List.mem_map.mp hx
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hy
    exact hxy (unique x y (List.cons.inj (hp.trans hq.symm)).1)

theorem encoded_live_nodup (ids : IR.Behavioral.Identities k o) (f : IR.Behavioral.Frame k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y) :
    (((List.finRange o).filter fun x => f.live[x]).map
      fun x => [ids.ids[ids.root], ids.ids[x]]).Nodup := by
  apply List.Nodup.map _ ((List.nodup_finRange o).filter _)
  intro x y he
  exact unique x y (List.cons.inj (List.cons.inj he).2).1

theorem encoded_references_nodup (ids : IR.Behavioral.Identities k o) (f : IR.Behavioral.Frame k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (references : f.references.Nodup) (d : Fin k) :
    ((f.references.filter fun r => r.1 == d).map fun r => [ids.ids[r.2.1], ids.ids[r.2.2]]).Nodup := by
  apply List.Nodup.map_on _ (references.filter _)
  intro x hx y hy he
  have hdx : x.1 = d := by simpa using (List.mem_filter.mp hx).2
  have hdy : y.1 = d := by simpa using (List.mem_filter.mp hy).2
  have hhead := unique x.2.1 y.2.1 (List.cons.inj he).1
  have htarget := unique x.2.2 y.2.2 (List.cons.inj (List.cons.inj he).2).1
  exact Prod.ext (hdx.trans hdy.symm) (Prod.ext hhead htarget)

-- [proof->req~compiler-trace-representation~1]
theorem encodeState_wellFormed (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (references : f.references.Nodup) :
    (encodeState v ids f).wellFormed (schema v).declarations = true := by
  have hn (d : Fin k) :
      (((List.finRange o).filter fun x => IR.Behavioral.ancestor v.core ids.directType[x] d).map
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
  · simp [encodeState, schema, Structural.schema, Structural.order_length]
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

end ClaferCompiler.Correctness.Behavioral
