module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsObservations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
namespace Selection
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {f : U → Atom} {S : Set U} {aliases chosen : List Rel} {domain : Rel} {budget : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Every successful selected head denotes one distinct source member. The
surjective source list is deduplicated even when the allocation aliases repeat. -/
theorem source_heads (fallback : U) (hf : Function.Injective f)
    (rows : Mixed.Unary f S (domain.eval s w τ e t))
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ x ∈ S, ∃ entry ∈ aliases, Mixed.Unary f {x} (entry.eval s w τ e t))
    (bound : S.ncard ≤ budget)
    (selected : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) chosen) :
    ∃ decode : Rel → U,
      (∀ entry ∈ chosen, entry.Term ∧ Mixed.Unary f {decode entry} (entry.eval s w τ e t)) ∧
      (chosen.map decode).Nodup ∧
      (∀ x, x ∈ chosen.map decode ↔ x ∈ S) := by
  classical
  have rowBound : (domain.eval s w τ e t).toFinset.card ≤ budget := by
    rw [Mixed.unary_card hf rows]
    exact bound
  obtain ⟨final, runFinal, invariant, _, covered⟩ := run_complete
    (empty_invariant (s := s) (w := w) (τ := τ) (e := e) (t := t) domain) terms rowBound
  have selectedEq : chosen = final.1.reverse := by
    rw [selections_correct, runFinal] at selected
    exact (Option.some.inj selected).symm
  subst chosen
  have singleton : ∀ entry ∈ final.1, ∃ x ∈ S,
      Mixed.Unary f {x} (entry.eval s w τ e t) := by
    intro entry he
    obtain ⟨row, hr⟩ := invariant.singleton entry he
    have mem : row ∈ entry.eval s w τ e t := (singleton_rows hr row).mpr rfl
    have inside := invariant.subset row ((invariant.rows row).mpr ⟨entry, he, mem⟩)
    obtain ⟨x, hx, rfl⟩ := (rows row).mp inside
    refine ⟨x, hx, ?_⟩
    intro other
    rw [singleton_rows hr]
    simp
  let decode : Rel → U := fun entry =>
    if h : ∃ x ∈ S, Mixed.Unary f {x} (entry.eval s w τ e t) then h.choose else fallback
  have decoded : ∀ entry ∈ final.1, decode entry ∈ S ∧
      Mixed.Unary f {decode entry} (entry.eval s w τ e t) := by
    intro entry he
    have hex := singleton entry he
    simpa only [decode, dite_eq_left hex] using hex.choose_spec
  have pairwise : final.1.Pairwise (fun a b => decode a ≠ decode b) := by
    apply invariant.disjoint.imp_of_mem
    intro a b ha hb disjoint equal
    have ma := (decoded a ha).2 [f (decode a)] |>.mpr ⟨decode a, Set.mem_singleton _, rfl⟩
    have mb := (decoded b hb).2 [f (decode b)] |>.mpr ⟨decode b, Set.mem_singleton _, rfl⟩
    rw [← equal] at mb
    exact disjoint _ ma mb
  refine ⟨decode, ?_, ?_, ?_⟩
  · intro entry he
    have hm := List.mem_reverse.mp he
    exact ⟨invariant.terms entry hm, (decoded entry hm).2⟩
  · rw [List.map_reverse]
    exact List.nodup_reverse.mpr (List.pairwise_map.mpr pairwise)
  · intro x
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨entry, he, rfl⟩
      exact (decoded entry he).1
    · intro hx
      obtain ⟨entry, he, entryRows⟩ := cover x hx
      have mem : [f x] ∈ domain.eval s w τ e t := (rows _).mpr ⟨x, hx, rfl⟩
      have hm := covered entry he [f x] (Mixed.unary_singleton_rows entryRows) mem
      obtain ⟨head, hh, mem⟩ := (invariant.rows _).mp hm
      obtain ⟨value, hv, eq⟩ := ((decoded head hh).2 _).mp mem
      have valueEq := Set.mem_singleton_iff.mp hv
      have atomEq : f x = f value := by simpa using eq
      exact ⟨head, hh, valueEq.symm.trans (hf atomEq).symm⟩

end Selection
end ClaferCompiler.Correctness.Behavioral.Full
