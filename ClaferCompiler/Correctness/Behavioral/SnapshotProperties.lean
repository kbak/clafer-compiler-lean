module

public import ClaferCompiler.Correctness.Behavioral.SnapshotTables
public import ClaferCompiler.Correctness.Behavioral.Compilation
public import ClaferCompiler.Correctness.StructuralCompletionDeclarations

public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

theorem nodup_of_eraseDups_length [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) (h : xs.eraseDups.length = xs.length) : xs.Nodup := by
  have hn := Structural.eraseDups_nodup xs
  have he : xs.eraseDups.toFinset = xs.toFinset := by ext; simp
  have hc : xs.toFinset.card = xs.length := by
    rw [← he, List.toFinset_card_of_nodup hn, h]
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hc

theorem table_signature_nodup (s : Schema) (i : Instance)
    (hw : i.wellFormed s = true) (n : Nat) : (i.signatures[n]?.getD []).Nodup := by
  cases hn : i.signatures[n]? with
  | none => simp
  | some xs =>
    have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
      xs (List.mem_of_getElem? hn)
    exact nodup_of_eraseDups_length xs (beq_iff_eq.mp hs)

theorem table_field_nodup (s : Schema) (i : Instance)
    (hw : i.wellFormed s = true) (n : Nat) : (i.fields[n]?.getD []).Nodup := by
  cases hn : i.fields[n]? with
  | none => simp
  | some xs =>
    have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2
      xs (List.mem_of_getElem? hn)
    exact nodup_of_eraseDups_length xs (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hs).1)

theorem signature_restriction (s : Schema) (i j : Instance) (P : Nat → Prop)
    (h : i.declarations s = true)
    (hm : ∀ d ∈ s.signatures, d.multiplicity = .set)
    (hp : ∀ (n x : Nat), x ∈ j.signatures[n]?.getD [] ↔ x ∈ i.signatures[n]?.getD [] ∧ P x) :
    j.declarations {s with fields := []} = true := by
  have hs := (Bool.and_eq_true_iff.mp h).1
  unfold Instance.declarations
  simp only [List.zipIdx_nil, List.all_nil, Bool.and_true]
  apply List.all_eq_true.mpr
  rintro ⟨d, n⟩ hd
  have old := List.all_eq_true.mp hs (d,n) hd
  simp only [Id.run, pure, Bool.and_eq_true] at old ⊢
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · cases he : d.parent with
    | none => simp
    | some p =>
      simp only [he, Option.all_some] at old ⊢
      apply List.all_eq_true.mpr
      intro x hx
      exact List.contains_iff_mem.mpr ((hp p x).mpr
        ⟨List.contains_iff_mem.mp (List.all_eq_true.mp old.1.1.1 x ((hp n x).mp hx).1),
          ((hp n x).mp hx).2⟩)
  · simp only [Bool.or_eq_true] at old ⊢
    rcases old.1.1.2 with hh | hh
    · exact Or.inl hh
    · apply Or.inr
      apply List.all_eq_true.mpr
      intro x hx
      obtain ⟨child, hc, hcx⟩ := List.any_eq_true.mp
        (List.all_eq_true.mp hh x ((hp n x).mp hx).1)
      exact List.any_eq_true.mpr ⟨child, hc, List.contains_iff_mem.mpr
        ((hp child x).mpr ⟨List.contains_iff_mem.mp hcx, ((hp n x).mp hx).2⟩)⟩
  · apply List.all_eq_true.mpr
    rintro ⟨other, m⟩ ho
    have hh := List.all_eq_true.mp old.1.2 (other,m) ho
    simp only [Bool.or_eq_true] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl hh
    · apply Or.inr
      apply List.all_eq_true.mpr
      intro x hx
      have hn := List.all_eq_true.mp hh x ((hp n x).mp hx).1
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hn ⊢
      exact fun hmem => hn (List.contains_iff_mem.mpr
        ((hp m x).mp (List.contains_iff_mem.mp hmem)).1)
  · rw [hm d (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hd))]
    rfl

theorem snapshotSig_nodup (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) :
    ((snapshotRel v (.sig n)).eval (schema v) w τ [] t).Nodup := by
  change ((if n == 0 then live v else Temporal.Rel.inter (.sig n) (live v)).eval
    (schema v) w τ [] t).Nodup
  simp only [live, root, pool]
  split
  · rw [Temporal.Rel.eval_join (.sig _) (.field _)]
    exact Structural.eraseDups_nodup _
  · rw [Temporal.Rel.eval_inter (.sig _) (.join (.sig _) (.field _))]
    apply List.Nodup.filter
    exact (table_signature_nodup (schema v).declarations (τ.state t) wf n).map
      (by intro a b h; simpa using h)

theorem snapshotField_nodup (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) :
    ((snapshotRel v (.field n)).eval (schema v) w τ [] t).Nodup := by
  change ((match (Structural.fieldKeys v.core)[n]? with
    | some (d, .containment) => contains v d
    | some (d, .dereference) => deref d
    | none => Temporal.Rel.empty .binary).eval (schema v) w τ [] t).Nodup
  split
  · rename_i d hd
    unfold contains
    split
    · exact List.nodup_nil
    · simp only [parent, live, root, pool, head]
      rw [Temporal.Rel.eval_inter (.transpose (.field _))
        (.product (.join (.sig _) (.field _)) (.inter (.sig _) (.join (.sig _) (.field _))))]
      apply List.Nodup.filter
      rw [Temporal.Rel.eval_transpose (.field _)]
      exact Structural.eraseDups_nodup _
  · rename_i d hd
    exact (table_field_nodup (schema v).declarations (τ.state t) wf (2 + d.val)).map
      objectRow_injective
  · exact List.nodup_nil

theorem unaryValues_nodup {rows : Temporal.Relation} (hn : rows.Nodup)
    (h : ∀ row ∈ rows, ∃ x, row = [.object x]) : (unaryValues rows).Nodup := by
  have he := unaryValues_exact h
  have hm : (objectRows ((unaryValues rows).map (fun x => [x]))).Nodup := by rw [he]; exact hn
  exact (hm.of_map _).of_map _

theorem rowValues_nodup {rows : Temporal.Relation} (hn : rows.Nodup)
    (h : ∀ row ∈ rows, ∃ x y, row = [.object x, .object y]) : (rowValues rows).Nodup := by
  have he := rowValues_exact h
  have hm : (objectRows (rowValues rows)).Nodup := by rw [he]; exact hn
  exact hm.of_map _

-- [proof->req~compiler-behavioral-correctness~1]
theorem snapshotState_wellFormed (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) :
    (snapshotState v w τ t).wellFormed (Structural.schema v) = true := by
  simp only [Instance.wellFormed, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [snapshotState, Structural.schema, Structural.order_length]
  · simp [snapshotState, Structural.schema]
  · apply List.all_eq_true.mpr
    intro xs hxs
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hxs
    rw [eraseDups_of_nodup (unaryValues_nodup (snapshotSig_nodup v w τ wf n)
      (snapshotSig_unary v w τ wf n))]
    simp
  · apply List.all_eq_true.mpr
    intro xs hxs
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hxs
    rw [eraseDups_of_nodup (rowValues_nodup (snapshotField_nodup v w τ wf n)
      (snapshotField_binary v w τ wf n))]
    simp only [beq_self_eq_true, Bool.true_and]
    apply List.all_eq_true.mpr
    intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨x, y, rfl⟩ := snapshotField_binary v w τ wf n r hr
    rfl

theorem static_schema_wellFormed (v : IR.Structural.Layout k)
    (hw : (schema v).declarations.wellFormed = true) :
    (Structural.schema v).wellFormed = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨(Bool.and_eq_true_iff.mp hw).1, ?_⟩
  apply List.all_eq_true.mpr
  intro f hf
  obtain ⟨⟨d, role⟩, _, rfl⟩ := List.mem_map.mp hf
  have hsig := Structural.signatureId_bounds v d
  simp only [Structural.signature_inventory, Structural.fieldDeclaration,
    Structural.allocation_signatures]
  cases role
  · cases hp : (v.core.get d).parent with
    | none => simpa using hsig.2
    | some p => simpa using And.intro (Structural.signatureId_bounds v p).2 hsig.2
  · cases hp : (v.core.get d).reference.target with
    | none => simpa using hsig.2
    | some p => simpa using And.intro hsig.2 (Structural.signatureId_bounds v p).2

theorem snapshot_extent_mem (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n x : Nat) :
    x ∈ (snapshotState v w τ t).signatures[n]?.getD [] ↔
      [.object x] ∈ (snapshotRel v (.sig n)).eval (schema v) w τ [] t := by
  have he := snapshotState_signatures v w τ wf n []
  simp only [List.map_nil] at he
  rw [he]
  simp [objectRows, Rel.eval_sig, List.map_map]

theorem live_mem_pool (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (x : Nat) (hx : [.object x] ∈ (live v).eval (schema v) w τ [] t) :
    x ∈ (τ.state t).signatures[0]?.getD [] := by
  have hrel := Relations.unary_image Function.injective_id (.sig _) (.field _)
    (raw_signature_unary (schema v) w τ [] t (Structural.signatureId v v.core.root))
    (raw_field_binary (schema v) w τ wf [] 1)
  obtain ⟨y, ⟨p, _, hp⟩, he⟩ := (hrel [.object x]).mp hx
  have he : x = y := by simpa using he
  subst y
  have hm : (({owner := Structural.signatureId v v.core.root, target := 0} : Field), 1) ∈
      (schema v).declarations.fields.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rfl
  have hf := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hd).2 _ hm
  have hrow := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hf).1 [p,x] hp
  exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hrow).2

theorem snapshot_extent_restriction (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true) (n x : Nat) :
    x ∈ (snapshotState v w τ t).signatures[n]?.getD [] ↔
      x ∈ (τ.state t).signatures[n]?.getD [] ∧
        [.object x] ∈ (live v).eval (schema v) w τ [] t := by
  rw [snapshot_extent_mem v w τ wf n x]
  change [.object x] ∈ (if n == 0 then live v else
    Temporal.Rel.inter (.sig n) (live v)).eval (schema v) w τ [] t ↔ _
  by_cases hn : n = 0
  · subst n
    simp only [beq_self_eq_true, ↓reduceIte]
    exact ⟨fun h => ⟨live_mem_pool v w τ wf hd x h, h⟩, And.right⟩
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    simp only [live, root, pool]
    rw [Temporal.Rel.eval_inter (.sig _) (.join (.sig _) (.field _))]
    simp [List.mem_filter, Temporal.Rel.eval, Temporal.Rel.fold,
      Temporal.Rel.sig, Temporal.RelAlgebra.step, Temporal.relationAlgebra]

-- [proof->req~compiler-behavioral-correctness~1]
/-- Applying one live restriction to every static pool retains the complete
signature forest: inclusion, abstract cover, and sibling separation. -/
theorem snapshot_signature_declarations (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true) :
    (snapshotState v w τ t).declarations {Structural.schema v with fields := []} = true := by
  have h := signature_restriction (schema v).declarations (τ.state t)
    (snapshotState v w τ t) (fun x => [.object x] ∈ (live v).eval (schema v) w τ [] t) hd
  apply h
  · intro d hd
    simp only [schema, Structural.schema, List.mem_cons, List.mem_map] at hd
    rcases hd with rfl | ⟨e, _, rfl⟩ <;> rfl
  · exact snapshot_extent_restriction v w τ wf hd

theorem snapshotRel_head (v : IR.Structural.Layout k) (d : Fin k) :
    snapshotRel v (Structural.head v d) = head v d := by
  change (if Structural.signatureId v d == 0 then live v else head v d) = _
  simp [Nat.ne_of_gt (Structural.signatureId_bounds v d).1]

def snapshotFieldRelation (v : IR.Structural.Layout k) (d : Fin k) : Structural.FieldRole → Temporal.Rel
  | .containment => contains v d
  | .dereference => deref d

theorem snapshotRel_key (v : IR.Structural.Layout k) (d : Fin k) (role : Structural.FieldRole)
    (hk : (d, role) ∈ Structural.fieldKeys v.core) :
    snapshotRel v (.field (Structural.fieldId v.core d role)) =
      snapshotFieldRelation v d role := by
  change (match (Structural.fieldKeys v.core)[Structural.fieldId v.core d role]? with
    | some (d, .containment) => contains v d
    | some (d, .dereference) => deref d
    | none => Temporal.Rel.empty .binary) = _
  simp only [Structural.fieldId, List.getElem?_idxOf hk]
  cases role <;> rfl

theorem field_fiber_card (s : Schema) (i : Instance) (hw : i.wellFormed s = true)
    (n a : Nat) :
    ((Rel.join (.var 0) (.field n)).eval i [a]).eraseDups.length =
      ((i.fields[n]?.getD []).filter fun row => row.head? == some a).length := by
  let rows := (i.fields[n]?.getD []).filter fun row => row.head? == some a
  have he : (Rel.join (.var 0) (.field n)).eval i [a] = (rows.map (List.drop 1)).eraseDups := by
    rw [Rel.eval_join (.var _) (.field _)]
    simp only [Rel.eval_var, Rel.eval_field, List.getElem?_cons_zero, Option.toList_some,
      List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getLast?_singleton, List.dropLast_singleton, List.nil_append]
    congr 2
    apply List.filter_congr
    intro row _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  have hn : rows.Nodup := (Structural.field_nodup s i hw n).filter _
  have hm : (rows.map (List.drop 1)).Nodup := hn.map_on (by
    intro x hx y hy he
    obtain ⟨hx, hxa⟩ := List.mem_filter.mp hx
    obtain ⟨hy, hya⟩ := List.mem_filter.mp hy
    obtain ⟨u, b, rfl⟩ := Structural.field_binary s i hw n x hx
    obtain ⟨v, c, rfl⟩ := Structural.field_binary s i hw n y hy
    have hu : u = a := by simpa using hxa
    have hv : v = a := by simpa using hya
    simpa [hu, hv] using he)
  rw [he, eraseDups_of_nodup hm, eraseDups_of_nodup hm]
  exact List.length_map _

theorem snapshot_reference_one (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (d : Fin k) (hk : (d, .dereference) ∈ Structural.fieldKeys v.core)
    (hh : (Temporal.Formula.all (head v d)
      (.mult .one (.join (.var 0) (deref d)))).Holds (schema v) w τ [] t)
    (a : Nat) (ha : a ∈ (snapshotState v w τ t).signatures[Structural.signatureId v d]?.getD []) :
    (((snapshotState v w τ t).fields[Structural.fieldId v.core d .dereference]?.getD []).filter
      (fun row => row.head? == some a)).length = 1 := by
  let p := Formula.all (Structural.head v d)
    (.mult .one (.join (.var 0) (Structural.deref v.core d)))
  have shape : SnapshotFormula (snapshotState v w τ t) p :=
    .all (.sig _) (by
      intro env row hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact ⟨x, rfl⟩) (.mult .one (.join (.var _) (.field _)))
  have emitted : snapshotFormula v p = Temporal.Formula.all (head v d)
      (.mult .one (.join (.var 0) (deref d))) := by
    dsimp only [p, Structural.deref]
    rw [snapshotFormula_all (i := snapshotState v w τ t) v _
      (.mult .one (.join (.var _) (.field _))), snapshotRel_head]
    change Temporal.Formula.all (head v d) (.mult .one (snapshotRel v
      (.join (.var 0) (.field (Structural.fieldId v.core d .dereference))))) = _
    rw [snapshotRel_join v (.var _) (.field _), snapshotRel_key v d .dereference hk]
    rfl
  have hp : p.eval w (snapshotState v w τ t) [] = some true := by
    apply (snapshotFormula_eval v shape (schema v) w τ t
      (snapshotState_signatures v w τ wf) (snapshotState_fields v w τ wf) []).mp
    rw [emitted]
    refine ⟨?_, hh⟩
    simp only [Temporal.Formula.Defined, Temporal.Formula.fold_all _ _ _ (.mult _ _)]
    change ∀ x, [x] ∈ (head v d).eval (schema v) w τ [] t → True
    exact fun _ _ => trivial
  rw [Formula.eval_all_true (.mult _ _)] at hp
  have hp := hp [a] (by simpa [Structural.head, Rel.eval_sig] using ha)
  change some (((Rel.join (.var 0) (.field (Structural.fieldId v.core d .dereference))).eval
    (snapshotState v w τ t) [a]).eraseDups.length == 1) = some true at hp
  have hp := beq_iff_eq.mp (Option.some.inj hp)
  simpa only [List.headD_cons, Structural.deref,
    field_fiber_card (Structural.schema v) (snapshotState v w τ t)
      (snapshotState_wellFormed v w τ wf)] using hp

theorem snapshot_field_typed (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (d owner target : Fin k) (role : Structural.FieldRole)
    (hk : (d, role) ∈ Structural.fieldKeys v.core)
    (hh : (Temporal.Formula.subset
      (snapshotFieldRelation v d role)
      (.product (head v owner) (head v target))).Holds (schema v) w τ [] t)
    (x y : Nat)
    (hxy : [x,y] ∈ (snapshotState v w τ t).fields[Structural.fieldId v.core d role]?.getD []) :
    x ∈ (snapshotState v w τ t).signatures[Structural.signatureId v owner]?.getD [] ∧
      y ∈ (snapshotState v w τ t).signatures[Structural.signatureId v target]?.getD [] := by
  let p := Formula.subset (.field (Structural.fieldId v.core d role))
    (.product (Structural.head v owner) (Structural.head v target))
  have shape : SnapshotFormula (snapshotState v w τ t) p :=
    .subset (.field _) (.product (.sig _) (.sig _))
  have emitted : snapshotFormula v p = Temporal.Formula.subset
      (snapshotFieldRelation v d role)
      (.product (head v owner) (head v target)) := by
    change Temporal.Formula.subset (snapshotRel v (.field (Structural.fieldId v.core d role)))
      (snapshotRel v (.product (Structural.head v owner) (Structural.head v target))) = _
    rw [snapshotRel_product v (show SnapshotRel (Structural.head v owner) from .sig _)
      (show SnapshotRel (Structural.head v target) from .sig _), snapshotRel_key v d role hk,
      snapshotRel_head, snapshotRel_head]
  have hp : p.eval w (snapshotState v w τ t) [] = some true := by
    apply (snapshotFormula_eval v shape (schema v) w τ t
      (snapshotState_signatures v w τ wf) (snapshotState_fields v w τ wf) []).mp
    rw [emitted]
    exact ⟨trivial, hh⟩
  change some (relationSubset ((snapshotState v w τ t).fields[Structural.fieldId v.core d role]?.getD [])
    ((Rel.product (Structural.head v owner) (Structural.head v target)).eval (snapshotState v w τ t) [])) =
      some true at hp
  have hm := List.contains_iff_mem.mp (List.all_eq_true.mp (Option.some.inj hp) [x,y] hxy)
  simpa [Structural.head, Rel.eval, Rel.fold, Rel.product, Rel.sig, RelAlgebra.step,
    List.mem_flatMap, List.mem_map] using hm

theorem snapshot_containment_generated (v : IR.Structural.Layout k) (d p : Fin k)
    (hp : (v.core.get d).parent = some p) :
    Temporal.Formula.subset (contains v d) (.product (head v p) (head v d)) ∈ snapshotDeclarations v := by
  apply List.mem_flatMap.mpr
  refine ⟨d, List.mem_finRange d, ?_⟩
  simp [hp]

theorem snapshot_reference_generated (v : IR.Structural.Layout k) (d p : Fin k)
    (hp : (v.core.get d).reference.target = some p) :
    Temporal.Formula.binary .conj
      (.subset (deref d) (.product (head v d) (head v p)))
      (.all (head v d) (.mult .one (.join (.var 0) (deref d)))) ∈ snapshotDeclarations v := by
  apply List.mem_flatMap.mpr
  refine ⟨d, List.mem_finRange d, ?_⟩
  simp [hp]

theorem snapshotDeclarations_built (v : IR.Structural.Layout k) (f : Temporal.Formula)
    (hf : f ∈ snapshotDeclarations v) : f.Built := by
  obtain ⟨d, _, hf⟩ := List.mem_flatMap.mp hf
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | rfl
  · exact .subset _ _
  · exact .subset _ _
  · cases (v.core.get d).reference.target
    · exact .equal _ _
    · exact .binary .conj (.subset _ _) (.all _ (.mult _ _))

theorem snapshotDeclaration_state_generated (v : IR.Structural.Layout k) (f : Temporal.Formula)
    (hf : f ∈ snapshotDeclarations v) : f ∈ stateFacts v := by
  simp only [stateFacts, List.mem_append]
  exact Or.inl (Or.inr hf)

-- [proof->req~compiler-behavioral-correctness~1]
/-- The emitted current-state field clauses enforce the static backend's field
typing and exactly one referent for each live reference head. -/
theorem snapshot_field_declarations (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hs : ∀ f ∈ snapshotDeclarations v, f.Holds (schema v) w τ [] t) :
    ((Structural.schema v).fields.zipIdx.all fun (field, id) =>
      let tuples := (snapshotState v w τ t).fields[id]?.getD []
      let owner := (snapshotState v w τ t).signatures[field.owner]?.getD []
      let target := (snapshotState v w τ t).signatures[field.target]?.getD []
      (tuples.all fun tuple => match tuple with
        | [a, b] => owner.contains a && target.contains b
        | _ => false) &&
      owner.all (fun atom => field.multiplicity.holds
        (tuples.filter fun tuple => tuple.head? == some atom).length)) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨field, n⟩ hn
  obtain ⟨⟨d, role⟩, hk, rfl, rfl⟩ := Structural.field_preimage v n field
    (List.mk_mem_zipIdx_iff_getElem?.mp hn)
  cases role with
  | containment =>
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((Structural.containment_inventory v.core d).mp hk)
      have hh := hs _ (snapshot_containment_generated v d p hp)
      simp only [Structural.fieldDeclaration, hp, Option.map_some, Option.getD_some,
        Structural.allocation_signatures, Multiplicity.holds, Bool.and_eq_true]
      refine ⟨?_, by simp⟩
      apply List.all_eq_true.mpr
      intro row hr
      obtain ⟨x,y,rfl⟩ := Structural.field_binary (Structural.schema v) (snapshotState v w τ t)
        (snapshotState_wellFormed v w τ wf) _ row hr
      simpa only [Bool.and_eq_true, List.contains_iff_mem] using
        snapshot_field_typed v w τ wf d p d .containment hk hh x y hr
  | dereference =>
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((Structural.dereference_inventory v.core d).mp hk)
      have hh := hs _ (snapshot_reference_generated v d p hp)
      simp only [Temporal.Formula.Holds, Temporal.Formula.fold_binary _ _ _ _ _ (.subset _ _)
        (.all _ (.mult _ _))] at hh
      change (_ ∧ _) at hh
      simp only [Structural.fieldDeclaration, hp, Option.map_some, Option.getD_some,
        Structural.allocation_signatures, Bool.and_eq_true]
      constructor
      · apply List.all_eq_true.mpr
        intro row hr
        obtain ⟨x,y,rfl⟩ := Structural.field_binary (Structural.schema v) (snapshotState v w τ t)
          (snapshotState_wellFormed v w τ wf) _ row hr
        simpa only [Bool.and_eq_true, List.contains_iff_mem] using
          snapshot_field_typed v w τ wf d d p .dereference hk hh.1 x y hr
      · apply List.all_eq_true.mpr
        intro a ha
        simpa only [Multiplicity.holds, beq_iff_eq] using snapshot_reference_one v w τ wf d hk hh.2 a ha

theorem snapshotState_declarations (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (hs : ∀ f ∈ snapshotDeclarations v, f.Holds (schema v) w τ [] t) :
    (snapshotState v w τ t).declarations (Structural.schema v) = true := by
  have sigs := snapshot_signature_declarations v w τ wf hd
  simp only [Instance.declarations, List.zipIdx_nil, List.all_nil, Bool.and_true] at sigs
  exact Bool.and_eq_true_iff.mpr ⟨sigs, snapshot_field_declarations v w τ wf hs⟩

end ClaferCompiler.Correctness.Behavioral
