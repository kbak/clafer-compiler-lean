module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsSelectionComplete
public import ClaferCompiler.Correctness.Behavioral.Full.StructureMixed

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal

namespace Mixed
variable {U : Type} {f : U → Atom} {S : Set U} {rows : Relation}

/-- The fixed injective map preserves the exact number of observed source
members. No finite ambient carrier is required for primitive integers. -/
theorem unary_card (hf : Function.Injective f) (represented : Unary f S rows) :
    rows.toFinset.card = S.ncard := by
  have he : (rows.toFinset : Set (List Atom)) = (fun x => [f x]) '' S := by
    ext row
    simpa only [Finset.mem_coe, List.mem_toFinset, Set.mem_image, eq_comm] using represented row
  rw [← Set.ncard_coe_finset, he]
  apply Set.ncard_image_of_injective
  intro x y h
  exact hf (by simpa using h)

theorem unary_finite (hf : Function.Injective f) (represented : Unary f S rows) : S.Finite := by
  have he : (rows.toFinset : Set (List Atom)) = (fun x => [f x]) '' S := by
    ext row
    simpa only [Finset.mem_coe, List.mem_toFinset, Set.mem_image, eq_comm] using represented row
  have imageFinite : ((fun x => [f x]) '' S).Finite := he ▸ rows.toFinset.finite_toSet
  apply Set.Finite.of_finite_image imageFinite
  intro x _ y _ h
  exact hf (by simpa using h)

theorem unary_singleton_rows (represented : Unary f {x} rows) : rows.eraseDups = [[f x]] := by
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup (Structural.eraseDups_nodup rows) (by simp)).mpr
  intro row
  simp only [List.mem_eraseDups, List.mem_singleton]
  simpa using represented row

end Mixed

variable {U : Type} {f : U → Atom} {S : Set U}
  {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {domain : Rel} {aliases selected : List Rel} {budget : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem source_selection_cardinality (hf : Function.Injective f)
    (represented : Mixed.Unary f S (domain.eval s w τ e t))
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ x ∈ S, ∃ entry ∈ aliases, Mixed.Unary f {x} (entry.eval s w τ e t))
    (bound : S.ncard ≤ budget)
    (chosen : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) selected) :
    selected.length = S.ncard := by
  rw [← Mixed.unary_card hf represented]
  apply Selection.selections_cardinality aliases domain budget terms ?_ ?_ chosen
  · intro row hr
    obtain ⟨x, hx, rfl⟩ := (represented row).mp hr
    obtain ⟨entry, he, hs⟩ := cover x hx
    exact ⟨entry, he, Mixed.unary_singleton_rows hs⟩
  · rwa [Mixed.unary_card hf represented]

theorem source_capture_complete (hf : Function.Injective f)
    (represented : Mixed.Unary f S (domain.eval s w τ e t))
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ x ∈ S, ∃ entry ∈ aliases, Mixed.Unary f {x} (entry.eval s w τ e t))
    (bound : S.ncard ≤ budget) :
    ∃ frozen, Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen ∧
      Mixed.Unary f S (frozen.eval s w τ e t) := by
  have rowCover : ∀ row ∈ domain.eval s w τ e t,
      ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row] := by
    intro row hr
    obtain ⟨x, hx, rfl⟩ := (represented row).mp hr
    obtain ⟨entry, he, hs⟩ := cover x hx
    exact ⟨entry, he, Mixed.unary_singleton_rows hs⟩
  have rowBound : (domain.eval s w τ e t).toFinset.card ≤ budget := by
    rwa [Mixed.unary_card hf represented]
  obtain ⟨frozen, h⟩ := Selection.capture_complete aliases domain budget terms rowCover rowBound
  refine ⟨frozen, h, ?_⟩
  intro row
  rw [← Value.capture_sound aliases domain budget h row]
  exact represented row

/-- Captured aliases keep their rows across time, even when the corresponding
object is absent from a later live extent. -/
structure Stable (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (r : Rel) : Prop where
  term : r.Term
  rows : ∀ t u row, row ∈ r.eval s w τ e t ↔ row ∈ r.eval s w τ e u

theorem Stable.union (rs : List Rel) (stable : ∀ r ∈ rs, Stable s w τ e r) :
    Stable s w τ e (Backend.Alloy.Behavioral.Full.union rs) := by
  have terms : ∀ r ∈ rs, r.Term := fun r hr => (stable r hr).term
  refine ⟨union_term rs terms _ (.empty _), ?_⟩
  intro t u row
  rw [Backend.Alloy.Behavioral.Full.union, union_rows rs terms _ (.empty _),
    union_rows rs terms _ (.empty _)]
  change (row ∈ ([] : Relation) ∨ _) ↔ (row ∈ ([] : Relation) ∨ _)
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨r, hr, hrow⟩
    exact ⟨r, hr, ((stable r hr).rows t u row).mp hrow⟩
  · rintro ⟨r, hr, hrow⟩
    exact ⟨r, hr, ((stable r hr).rows t u row).mpr hrow⟩

theorem capture_origin (h : Value.Meaning s w τ e t
    (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen) :
    ∃ chosen, Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) chosen ∧
      frozen = Backend.Alloy.Behavioral.Full.union chosen := by
  have body (chosen : List Rel) : Value.Built
      (Backend.Alloy.Behavioral.Full.Value.mk
        [(Formula.equal domain (Backend.Alloy.Behavioral.Full.union chosen),
          Backend.Alloy.Behavioral.Full.union chosen)]) := by
    intro g x hg
    simp at hg
    rw [hg.1]
    exact .equal _ _
  obtain ⟨chosen, hc, g, hg, _⟩ := (Value.bind_meaning _ _
    (Value.selections_built aliases domain budget) body).mp h
  simp at hg
  exact ⟨chosen, hc, hg.2⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem capture_stable (stable : ∀ entry ∈ aliases, Stable s w τ e entry)
    (h : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen) :
    Stable s w τ e frozen := by
  obtain ⟨chosen, hc, rfl⟩ := capture_origin h
  exact Stable.union chosen (fun entry he => stable entry
    (Selection.selections_members aliases domain budget hc entry he))

theorem source_capture_frozen (represented : Mixed.Unary f S (domain.eval s w τ e t))
    (stable : ∀ entry ∈ aliases, Stable s w τ e entry)
    (h : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen) :
    ∀ u, Mixed.Unary f S (frozen.eval s w τ e u) := by
  intro u row
  rw [← (capture_stable stable h).rows t u row, ← Value.capture_sound aliases domain budget h row]
  exact represented row

end ClaferCompiler.Correctness.Behavioral.Full
