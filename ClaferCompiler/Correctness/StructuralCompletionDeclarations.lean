module

public import ClaferCompiler.Correctness.StructuralCompletionFacts

public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

theorem ancestor_rank (v : IR.Structural.Validated n) {d e : Fin n}
    (h : (interpret v.core).Ancestor d e) :
    v.certificate.superRank[e] ≤ v.certificate.superRank[d] := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail path edge ih => exact Nat.le_trans (Nat.le_of_lt (v.coreChecked.2.2.2.2.1 _ _ edge)) ih

theorem sibling_ancestor (v : IR.Structural.Validated n) {d e : Fin n}
    (hp : (v.core.get d).super = (v.core.get e).super)
    (h : (interpret v.core).Ancestor d e) : d = e := by
  rcases h.cases_head with he | ⟨p, hd, path⟩
  · exact he
  · have he : (v.core.get e).super = some p := hp.symm.trans hd
    have lt := v.coreChecked.2.2.2.2.1 e p he
    have le := ancestor_rank v path
    omega

theorem source_siblings {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U)
    (h : s.DeclarationDisjoint (interpret v.core)) (d e : Fin n)
    (hp : (v.core.get d).super = (v.core.get e).super) (x : U)
    (hd : x ∈ s.head d) (he : x ∈ s.head e) : d = e := by
  rcases h d e x hd he with ha | ha
  · exact sibling_ancestor v hp ha
  · exact (sibling_ancestor v hp.symm ha).symm

theorem source_top {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U)
    (h : s.Inherits (interpret v.core)) (d : Fin n) (x : U) (hx : x ∈ s.head d) :
    ∃ e, (v.core.get e).super = none ∧ x ∈ s.head e := by
  generalize hk : v.certificate.superRank[d] = k
  induction k using Nat.strong_induction_on generalizing d with
  | h k ih =>
    cases hp : (v.core.get d).super with
    | none => exact ⟨d, hp, hx⟩
    | some p =>
      exact ih v.certificate.superRank[p] (hk ▸ v.coreChecked.2.2.2.2.1 d p hp)
        p (h d p hp x hx) rfl

theorem fieldKeys_nodup (m : IR.Structural.Core n) : (fieldKeys m).Nodup := by
  unfold fieldKeys
  rw [List.nodup_flatMap]
  constructor
  · intro d _
    cases (m.get d).parent <;> cases (m.get d).reference.target <;> simp
  · apply (List.nodup_finRange n).imp
    intro d e hde
    apply List.disjoint_left.mpr
    intro key hd he
    have fst_eq (q : Fin n) :
        key ∈ ((m.get q).parent.toList.map (fun _ => (q, FieldRole.containment)) ++
          (m.get q).reference.target.toList.map (fun _ => (q, FieldRole.dereference))) → key.1 = q := by
      intro hk
      simp only [List.mem_append, List.mem_map] at hk
      rcases hk with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
    exact hde ((fst_eq d hd).symm.trans (fst_eq e he))

theorem field_preimage (v : IR.Structural.Validated n) (k : Nat) (f : Field)
    (hk : (schema v).fields[k]? = some f) :
    ∃ key ∈ fieldKeys v.core, k = fieldId v.core key.1 key.2 ∧ f = fieldDeclaration v key := by
  cases ht : (fieldKeys v.core)[k]? with
  | none => simp [schema, ht] at hk
  | some key =>
    have hf : f = fieldDeclaration v key := by simpa [schema, ht] using hk.symm
    obtain ⟨hbound, he⟩ := List.getElem?_eq_some_iff.mp ht
    have hi := (fieldKeys_nodup v.core).idxOf_getElem k hbound
    rw [he] at hi
    exact ⟨key, List.mem_of_getElem? ht, hi.symm, hf⟩

theorem raw_extent_live {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (k a : Nat) (ha : a ∈ i.signatures[k]?.getD []) :
    a ∈ i.signatures[0]?.getD [] := by
  cases hk : i.signatures[k]? with
  | none => simp [hk] at ha
  | some xs => exact r.live.1 xs (List.mem_of_getElem? hk) a (by simpa [hk] using ha)

theorem source_signature_declarations {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s) :
    ((schema v).signatures.zipIdx.all fun (decl, id) => Id.run do
      let extent := i.signatures[id]?.getD []
      let children := ((schema v).signatures.zipIdx.filter fun (child, _) => child.parent == some id).map Prod.snd
      let included := decl.parent.all fun parent => extent.all (i.signatures[parent]?.getD []).contains
      let covered := !decl.isAbstract || children.isEmpty ||
        extent.all (fun atom => children.any fun child => (i.signatures[child]?.getD []).contains atom)
      let disjoint := (schema v).signatures.zipIdx.all fun (other, j) =>
        id == j || decl.parent != other.parent ||
        extent.all (fun atom => !(i.signatures[j]?.getD []).contains atom)
      return included && covered && disjoint && decl.multiplicity.holds extent.length) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨decl, k⟩ hk
  have hk := List.mk_mem_zipIdx_iff_getElem?.mp hk
  have sigmem (d : Fin n) := List.mk_mem_zipIdx_iff_getElem?.mpr (schema_signature v d)
  have ih := h.2.2.1
  have dh := h.2.2.2.2.2.2.2.2.2
  by_cases hz : k = 0
  · subst k
    have hd : decl = { isAbstract := true } := by simpa [schema] using hk.symm
    subst decl
    simp only [Id.run, pure, Option.all_none, Bool.true_and, Bool.not_true,
      Bool.false_or, Multiplicity.holds, Bool.and_true, Bool.and_eq_true]
    constructor
    · apply Bool.or_eq_true_iff.mpr
      right
      apply List.all_eq_true.mpr
      intro a ha
      let x := r.objects.symm ⟨a, ha⟩
      have hx : (r.objects x).val = a := by simp [x]
      obtain ⟨d, hd⟩ : ∃ d, x ∈ s.head d := by
        rcases h.2.1.2.2 x with hr | ⟨d, _, hd⟩
        · exact ⟨v.core.root, h.2.1.1 x |>.mpr hr⟩
        · exact ⟨d, hd⟩
      obtain ⟨e, he, hxe⟩ := source_top v s ih d x hd
      apply List.any_eq_true.mpr
      refine ⟨signatureId v e, List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨sigmem e, ?_⟩, rfl⟩, ?_⟩
      · simp [he]
      · exact List.contains_iff_mem.mpr (by simpa [hx] using (r.heads e x).mp hxe)
    · apply List.all_eq_true.mpr
      rintro ⟨other, j⟩ hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · have hp : other.parent ≠ none := by
          intro hp
          exact hj0 (schema_parentless v j other (List.mk_mem_zipIdx_iff_getElem?.mp hj) hp)
        simp [Ne.symm hp]
  · obtain ⟨d, rfl⟩ := signature_preimage v k decl hk hz
    have he := (schema_signature v d).symm.trans hk
    cases Option.some.inj he
    simp only [Id.run, pure, Option.all_some, Multiplicity.holds, Bool.and_true,
      Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply List.all_eq_true.mpr
      intro a ha
      cases hp : (v.core.get d).super with
      | none => simpa [hp] using List.contains_iff_mem.mpr (raw_extent_live v s i r _ a ha)
      | some p =>
        have hm := raw_extent_live v s i r _ a ha
        let x := r.objects.symm ⟨a, hm⟩
        have hx : (r.objects x).val = a := by simp [x]
        have hs := ih d p hp x ((r.heads d x).mpr (by simpa [hx] using ha))
        simpa [hp, hx] using List.contains_iff_mem.mpr ((r.heads p x).mp hs)
    · cases ha : (v.core.get d).isAbstract with
      | false => simp
      | true =>
        apply Bool.or_eq_true_iff.mpr
        right
        apply List.all_eq_true.mpr
        intro a hx
        have hm := raw_extent_live v s i r _ a hx
        let x := r.objects.symm ⟨a, hm⟩
        have hx' : (r.objects x).val = a := by simp [x]
        obtain ⟨e, he, hxe⟩ := (h.2.2.2.1 d ha).1 x ((r.heads d x).mpr (by simpa [hx'] using hx))
        apply List.any_eq_true.mpr
        refine ⟨signatureId v e, List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨sigmem e, ?_⟩, rfl⟩, ?_⟩
        · change (v.core.get e).super = some d at he
          simp [he]
        · exact List.contains_iff_mem.mpr (by simpa [hx'] using (r.heads e x).mp hxe)
    · apply List.all_eq_true.mpr
      rintro ⟨other, j⟩ hj
      have hj := List.mk_mem_zipIdx_iff_getElem?.mp hj
      by_cases hj0 : j = 0
      · subst j
        have he : other = { isAbstract := true } := by simpa [schema] using hj.symm
        simp [he]
      · obtain ⟨e, rfl⟩ := signature_preimage v j other hj hj0
        have he := (schema_signature v e).symm.trans hj
        cases Option.some.inj he
        by_cases hde : d = e
        · simp [hde]
        · by_cases hp : (v.core.get d).super = (v.core.get e).super
          · apply Bool.or_eq_true_iff.mpr
            right
            apply List.all_eq_true.mpr
            intro a ha
            simp only [Bool.not_eq_true']
            apply Bool.eq_false_iff.mpr
            intro hb
            have hb := List.contains_iff_mem.mp hb
            have hm := raw_extent_live v s i r _ a ha
            let x := r.objects.symm ⟨a, hm⟩
            have hx : (r.objects x).val = a := by simp [x]
            exact hde (source_siblings v s dh d e hp x
              ((r.heads d x).mpr (by simpa [hx] using ha))
              ((r.heads e x).mpr (by simpa [hx] using hb)))
          · have he : ((v.core.get d).super.map (signatureId v) |>.getD 0) ≠
                ((v.core.get e).super.map (signatureId v) |>.getD 0) := by
              cases hd : (v.core.get d).super <;> cases he : (v.core.get e).super <;>
                simp_all [signatureId_injective v |>.eq_iff,
                  Nat.ne_of_lt (signatureId_bounds v _).1, (Nat.ne_of_lt (signatureId_bounds v _).1).symm]
            simp [he]

theorem field_nodup (s : Schema) (i : Instance) (hw : i.wellFormed s = true) (k : Nat) :
    (i.fields[k]?.getD []).Nodup := by
  cases hk : i.fields[k]? with
  | none => simp
  | some ts =>
    have ht := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 ts (List.mem_of_getElem? hk)
    have hl := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).1
    apply List.nodup_iff_length_dedup_eq.mpr
    simpa [List.card_toFinset] using (eraseDups_card ts).symm.trans hl

theorem source_field_typed {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.Typed (interpret v.core))
    (key : Fin n × FieldRole) (hk : key ∈ fieldKeys v.core) :
    ((i.fields[fieldId v.core key.1 key.2]?.getD []).all fun tuple => match tuple with
      | [a, b] => (i.signatures[(fieldDeclaration v key).owner]?.getD []).contains a &&
          (i.signatures[(fieldDeclaration v key).target]?.getD []).contains b
      | _ => false) = true := by
  apply List.all_eq_true.mpr
  intro tuple ht
  obtain ⟨a, b, rfl⟩ := field_binary _ _ r.wellFormed _ tuple ht
  have live := field_atom_live i r.live _ a b ht
  let x := r.objects.symm ⟨a, live.1⟩
  let y := r.objects.symm ⟨b, live.2⟩
  have hx : (r.objects x).val = a := by simp [x]
  have hy : (r.objects y).val = b := by simp [y]
  rcases key with ⟨d, role⟩
  cases role with
  | containment =>
    have active := (containment_inventory _ _).mp hk
    have hr := (r.containment d x y).mpr ⟨active, by simpa [hx, hy] using ht⟩
    obtain ⟨heady, p, hp, headx⟩ := h.1 d x y hr
    change (v.core.get d).parent = some p at hp
    simp only [fieldDeclaration, hp, Option.map_some, Option.getD_some, Bool.and_eq_true,
      List.contains_iff_mem]
    exact ⟨by simpa [hx] using (r.heads p x).mp headx,
      by simpa [hy] using (r.heads d y).mp heady⟩
  | dereference =>
    have active := (dereference_inventory _ _).mp hk
    have hr := (r.dereference d x y).mpr ⟨active, by simpa [hx, hy] using ht⟩
    obtain ⟨headx, t, ht, heady⟩ := h.2 d x y hr
    have ht : (v.core.get d).reference.target = some t := by simpa [interpret] using ht
    simp only [fieldDeclaration, ht, Option.map_some, Option.getD_some, Bool.and_eq_true,
      List.contains_iff_mem]
    exact ⟨by simpa [hx] using (r.heads d x).mp headx,
      by simpa [hy] using (r.heads t y).mp heady⟩

theorem source_reference_one {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.References (interpret v.core))
    (d t : Fin n) (ht : (v.core.get d).reference.target = some t)
    (a : Nat) (ha : a ∈ i.signatures[signatureId v d]?.getD []) :
    ((i.fields[fieldId v.core d .dereference]?.getD []).filter fun tuple => tuple.head? == some a).length = 1 := by
  classical
  have live := raw_extent_live v s i r _ a ha
  let x := r.objects.symm ⟨a, live⟩
  have hx : (r.objects x).val = a := by simp [x]
  obtain ⟨y, hy, hu⟩ := h d t (by simpa [interpret] using ht)
    x ((r.heads d x).mpr (by simpa [hx] using ha))
  let xs := (i.fields[fieldId v.core d .dereference]?.getD []).filter fun tuple => tuple.head? == some a
  have hm : ∀ tuple, tuple ∈ xs ↔ tuple = [a, (r.objects y).val] := by
    intro tuple
    constructor
    · intro hm
      obtain ⟨hm, hp⟩ := List.mem_filter.mp hm
      obtain ⟨p, b, rfl⟩ := field_binary _ _ r.wellFormed _ tuple hm
      have hp : p = a := by simpa using hp
      subst p
      have hl := (field_atom_live i r.live _ _ b hm).2
      let z := r.objects.symm ⟨b, hl⟩
      have hz : (r.objects z).val = b := by simp [z]
      have hr := (r.dereference d x z).mpr ⟨by simp [ht], by simpa [hx, hz] using hm⟩
      have he := hu z hr
      simp only [List.cons.injEq, and_true, true_and]
      exact hz.symm.trans (congrArg (fun u => (r.objects u).val) he)
    · rintro rfl
      exact List.mem_filter.mpr ⟨by simpa [hx] using (r.dereference d x y).mp hy |>.2, by simp⟩
  have hn : xs.Nodup := (field_nodup _ _ r.wellFormed _).filter _
  have he : xs.toFinset = {[a, (r.objects y).val]} := by ext; simp [hm]
  rw [← List.toFinset_card_of_nodup hn, he]
  simp

theorem source_declarations {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s) :
    i.declarations (schema v) = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨source_signature_declarations v s i r h, List.all_eq_true.mpr ?_⟩
  rintro ⟨f, k⟩ hk
  obtain ⟨⟨d, role⟩, hkey, rfl, rfl⟩ := field_preimage v k f (List.mk_mem_zipIdx_iff_getElem?.mp hk)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨source_field_typed v s i r h.1 _ hkey, ?_⟩
  cases role with
  | containment => simp [fieldDeclaration, Multiplicity.holds]
  | dereference =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((dereference_inventory _ _).mp hkey)
    apply List.all_eq_true.mpr
    intro a ha
    exact beq_iff_eq.mpr (source_reference_one v s i r h.2.2.2.2.2.1 d t ht a ha)

end ClaferCompiler.Correctness.Structural
