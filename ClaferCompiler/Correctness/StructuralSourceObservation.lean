module

public import ClaferCompiler.Correctness.StructuralReferences
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

noncomputable def sourceLabel {U : Type} [Fintype U] (x : U) : Nat := (Fintype.equivFin U x).val

theorem sourceLabel_injective {U : Type} [Fintype U] : Function.Injective (@sourceLabel U _) :=
  Fin.val_injective.comp (Fintype.equivFin U).injective

/-- Canonical finite presentation of a source configuration. This is an existence
construction in the proof layer; production encoding still consumes executable
observations. No constraint truth is used to enumerate objects or relations. -/
noncomputable def sourceObservation {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) : Observation n := by
  classical
  exact {
    objects := (Finset.univ.image (@sourceLabel U _)).toList
    root := sourceLabel s.root
    heads := fun d => ((Finset.univ.filter (fun x => x ∈ s.head d)).image sourceLabel).toList
    containment := fun d => ((Finset.univ.filter (fun z : U × U => s.contains d z.1 z.2)).image
      (fun z => (sourceLabel z.1, sourceLabel z.2))).toList
    dereference := fun d => ((Finset.univ.filter (fun z : U × U => s.deref d z.1 z.2)).image
      (fun z => (sourceLabel z.1, sourceLabel z.2))).toList }

theorem source_object_mem {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) (a : Nat) :
    a ∈ (sourceObservation s).objects ↔ ∃ x : U, sourceLabel x = a := by
  classical
  simp [sourceObservation]

theorem source_head_mem {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) (d : Fin n) (a : Nat) :
    a ∈ (sourceObservation s).heads d ↔ ∃ x : U, x ∈ s.head d ∧ sourceLabel x = a := by
  classical
  simp [sourceObservation]

theorem source_contains_mem {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) (d : Fin n) (a b : Nat) :
    (a, b) ∈ (sourceObservation s).containment d ↔
      ∃ p x, s.contains d p x ∧ sourceLabel p = a ∧ sourceLabel x = b := by
  classical
  simp only [sourceObservation, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists, Prod.mk.injEq]

theorem source_deref_mem {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) (d : Fin n) (a b : Nat) :
    (a, b) ∈ (sourceObservation s).dereference d ↔
      ∃ x t, s.deref d x t ∧ sourceLabel x = a ∧ sourceLabel t = b := by
  classical
  simp only [sourceObservation, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists, Prod.mk.injEq]

noncomputable def sourceObjects {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) : U ≃ Objects (sourceObservation s) :=
  Equiv.ofBijective (fun x => ⟨sourceLabel x, (source_object_mem s _).mpr ⟨x, rfl⟩⟩) ⟨
    fun _ _ h => sourceLabel_injective (congrArg Subtype.val h),
    fun a => by
      obtain ⟨x, hx⟩ := (source_object_mem s a.val).mp a.property
      exact ⟨x, Subtype.ext hx⟩⟩

theorem source_table {U : Type} [Fintype U] (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (h : s.Typed (interpret v.core)) :
    TableWellFormed v (sourceObservation s) := by
  classical
  refine ⟨Finset.nodup_toList _, (fun _ => Finset.nodup_toList _),
    (fun _ => ⟨Finset.nodup_toList _, Finset.nodup_toList _⟩), ?_, ?_⟩
  · intro d hd
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨a, b⟩ hab
    obtain ⟨p, x, hx, _, _⟩ := (source_contains_mem s d a b).mp hab
    obtain ⟨_, c, hc, _⟩ := h.1 d p x hx
    change (v.core.get d).parent = some c at hc
    simp [hd] at hc
  · intro d hd
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨a, b⟩ hab
    obtain ⟨x, t, hx, _, _⟩ := (source_deref_mem s d a b).mp hab
    obtain ⟨_, c, hc, _⟩ := h.2 d x t hx
    have hc : (v.core.get d).reference.target = some c := by simpa [interpret] using hc
    simp [hd] at hc

theorem source_root {U : Type} [Fintype U] (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (h : s.Rooted (interpret v.core)) :
    (sourceObservation s).heads v.core.root = [(sourceObservation s).root] := by
  classical
  have hh : ∀ x, x ∈ s.head v.core.root ↔ x = s.root := h.1
  have he : (Finset.univ.filter (fun x => x ∈ s.head v.core.root)).image sourceLabel = {sourceLabel s.root} := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    simp only [hh, exists_eq_left, eq_comm]
  simp only [sourceObservation, he, Finset.toList_singleton]

theorem source_live {U : Type} [Fintype U] (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) : Live (encode v (sourceObservation s)) := by
  constructor
  · intro xs hxs a ha
    simp only [encode, List.mem_cons, List.mem_map] at hxs
    rcases hxs with rfl | ⟨d, _, rfl⟩
    · exact ha
    · obtain ⟨x, _, hx⟩ := (source_head_mem s d a).mp ha
      exact (source_object_mem s a).mpr ⟨x, hx⟩
  · intro ts hts tuple ht a ha
    obtain ⟨⟨d, role⟩, _, rfl⟩ := List.mem_map.mp hts
    obtain ⟨⟨p, x⟩, hx, rfl⟩ := List.mem_map.mp ht
    have hm : (∃ z : U, sourceLabel z = p) ∧ (∃ z : U, sourceLabel z = x) := by
      cases role with
      | containment =>
        obtain ⟨p', x', _, hp, hx⟩ := (source_contains_mem s d p x).mp hx
        exact ⟨⟨p', hp⟩, ⟨x', hx⟩⟩
      | dereference =>
        obtain ⟨p', x', _, hp, hx⟩ := (source_deref_mem s d p x).mp hx
        exact ⟨⟨p', hp⟩, ⟨x', hx⟩⟩
    rcases (by simpa using ha : a = p ∨ a = x) with ha | ha
    · exact ha ▸ (source_object_mem s p).mpr hm.1
    · exact ha ▸ (source_object_mem s x).mpr hm.2

/-- Every finite typed rooted source configuration has a concrete target-table
representation, before imposing target declarations or generated facts. -/
noncomputable def source_represents {U : Type} [Fintype U] (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (ht : s.Typed (interpret v.core))
    (hr : s.Rooted (interpret v.core)) : Represents v s (encode v (sourceObservation s)) where
  wellFormed := encode_wellFormed v _ (source_table v s ht)
  live := source_live v s
  objects := sourceObjects s
  root := by
    rw [encode_heads]
    exact source_root v s hr
  heads := by
    intro d x
    simp only [encode_heads, Option.getD_some]
    change x ∈ s.head d ↔ sourceLabel x ∈ (sourceObservation s).heads d
    rw [source_head_mem]
    simp [sourceLabel_injective.eq_iff]
  containment := by
    intro d p x
    change s.contains d p x ↔ (v.core.get d).parent.isSome = true ∧
      [sourceLabel p, sourceLabel x] ∈ _
    cases hp : (v.core.get d).parent with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_and, iff_false]
      intro hx
      obtain ⟨_, c, hc, _⟩ := ht.1 d p x hx
      change (v.core.get d).parent = some c at hc
      simp [hp] at hc
    | some c =>
      rw [encode_field v _ d .containment ((containment_inventory _ _).mpr (by simp [hp]))]
      simp only [Option.isSome_some, true_and, Option.getD_some, List.mem_map]
      have hm := source_contains_mem s d (sourceLabel p) (sourceLabel x)
      simp only [sourceLabel_injective.eq_iff] at hm
      simpa [Prod.exists] using hm.symm
  dereference := by
    intro d x t
    change s.deref d x t ↔ (v.core.get d).reference.target.isSome = true ∧
      [sourceLabel x, sourceLabel t] ∈ _
    cases hp : (v.core.get d).reference.target with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_and, iff_false]
      intro hx
      obtain ⟨_, c, hc, _⟩ := ht.2 d x t hx
      have hc : (v.core.get d).reference.target = some c := by simpa [interpret] using hc
      simp [hp] at hc
    | some c =>
      rw [encode_field v _ d .dereference ((dereference_inventory _ _).mpr (by simp [hp]))]
      simp only [Option.isSome_some, true_and, Option.getD_some, List.mem_map]
      have hm := source_deref_mem s d (sourceLabel x) (sourceLabel t)
      simp only [sourceLabel_injective.eq_iff] at hm
      simpa [Prod.exists] using hm.symm

end ClaferCompiler.Correctness.Structural
