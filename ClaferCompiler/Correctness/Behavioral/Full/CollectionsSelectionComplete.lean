module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsSelection
public import ClaferCompiler.Correctness.Behavioral.Full.StructureRelations
public import ClaferCompiler.Correctness.StructuralRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
namespace Selection
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {entry domain seen : Rel} {state initial : State} {aliases : List Rel} {budget : Nat}
  {row : List Atom}

/-- The accumulated rows are the disjoint singleton observations already
selected, all inside the domain. This invariant records no formula truth. -/
structure Invariant (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (domain : Rel) (state : State) : Prop where
  term : state.2.Term
  terms : ∀ entry ∈ state.1, entry.Term
  singleton : ∀ entry ∈ state.1, ∃ row, (entry.eval s w τ e t).eraseDups = [row]
  disjoint : state.1.Pairwise (fun a b => ∀ row ∈ a.eval s w τ e t, row ∉ b.eval s w τ e t)
  rows : ∀ row, row ∈ state.2.eval s w τ e t ↔ ∃ entry ∈ state.1, row ∈ entry.eval s w τ e t
  subset : ∀ row ∈ state.2.eval s w τ e t, row ∈ domain.eval s w τ e t
  card : (state.2.eval s w τ e t).toFinset.card = state.1.length

theorem singleton_rows (h : (entry.eval s w τ e t).eraseDups = [row]) (other : List Atom) :
    other ∈ entry.eval s w τ e t ↔ other = row := by
  rw [← List.mem_eraseDups, h, List.mem_singleton]

theorem eligible_row (hp : Eligible s w τ e t domain state.2 entry) :
    ∃ row, (entry.eval s w τ e t).eraseDups = [row] ∧
      row ∈ domain.eval s w τ e t ∧ row ∉ state.2.eval s w τ e t := by
  obtain ⟨row, hr⟩ := List.length_eq_one_iff.mp hp.1
  have member := (singleton_rows hr row).mpr rfl
  refine ⟨row, hr, hp.2.1 row member, ?_⟩
  intro hs
  apply hp.2.2
  intro other ho
  exact (singleton_rows hr other).mp ho ▸ hs

theorem union_singleton (hi : seen.Term) (he : entry.Term)
    (hr : (entry.eval s w τ e t).eraseDups = [row]) :
    ((seen.union entry).eval s w τ e t).toFinset = insert row (seen.eval s w τ e t).toFinset := by
  ext other
  rw [Rel.eval_union hi he]
  simp only [List.mem_toFinset, List.mem_eraseDups, List.mem_append, Finset.mem_insert]
  rw [singleton_rows hr]
  exact or_comm

theorem insert_invariant (hi : Invariant s w τ e t domain state) (he : entry.Term)
    (hp : Eligible s w τ e t domain state.2 entry) :
    Invariant s w τ e t domain (entry :: state.1, state.2.union entry) := by
  obtain ⟨row, hr, _, fresh⟩ := eligible_row hp
  have hu (other : List Atom) : other ∈ (state.2.union entry).eval s w τ e t ↔
      other ∈ state.2.eval s w τ e t ∨ other ∈ entry.eval s w τ e t := by
    rw [Rel.eval_union hi.term he]
    simp
  refine ⟨.union hi.term he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact he
    · exact hi.terms value hv
  · intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨row, hr⟩
    · exact hi.singleton value hv
  · rw [List.pairwise_cons]
    refine ⟨?_, hi.disjoint⟩
    intro other ho value hv hv'
    have same := (singleton_rows hr value).mp hv
    subst value
    exact fresh ((hi.rows row).mpr ⟨other, ho, hv'⟩)
  · intro other
    rw [hu other, hi.rows other]
    simp only [List.mem_cons]
    aesop
  · intro other ho
    rcases (hu other).mp ho with ho | ho
    · exact hi.subset other ho
    · exact hp.2.1 other ho
  · rw [union_singleton hi.term he hr, Finset.card_insert_of_notMem (by simpa using fresh)]
    simpa using hi.card

theorem room_of_bound (hi : Invariant s w τ e t domain state) (he : entry.Term)
    (hp : Eligible s w τ e t domain state.2 entry)
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget) : state.1.length < budget := by
  have hn := insert_invariant hi he hp
  have subset : ((state.2.union entry).eval s w τ e t).toFinset ⊆
      (domain.eval s w τ e t).toFinset := by
    intro row hr
    exact List.mem_toFinset.mpr (hn.subset row (List.mem_toFinset.mp hr))
  have hcard := (Finset.card_le_card subset).trans bound
  rw [hn.card] at hcard
  simpa using hcard

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem select_complete (hi : Invariant s w τ e t domain state) (he : entry.Term)
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget) :
    ∃ next, select s w τ e t domain budget state entry = some next ∧
      Invariant s w τ e t domain next ∧
      (∀ row ∈ state.2.eval s w τ e t, row ∈ next.2.eval s w τ e t) ∧
      (∀ row, (entry.eval s w τ e t).eraseDups = [row] →
        row ∈ domain.eval s w τ e t → row ∈ next.2.eval s w τ e t) := by
  classical
  by_cases hp : Eligible s w τ e t domain state.2 entry
  · have room := room_of_bound hi he hp bound
    refine ⟨(entry :: state.1, state.2.union entry), by simp [select, hp, room],
      insert_invariant hi he hp, ?_, ?_⟩
    · intro row hr
      rw [Rel.eval_union hi.term he]
      simp [hr]
    · intro row hr _
      rw [Rel.eval_union hi.term he]
      have hx := (singleton_rows hr row).mpr rfl
      simp [hx]
  · refine ⟨state, by simp [select, hp], hi, fun _ h => h, ?_⟩
    intro row hr hd
    by_contra fresh
    apply hp
    refine ⟨by rw [hr]; rfl, ?_, ?_⟩
    · intro other ho
      exact (singleton_rows hr other).mp ho ▸ hd
    · intro all
      exact fresh (all row ((singleton_rows hr row).mpr rfl))

theorem run_complete (hi : Invariant s w τ e t domain initial)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget) :
    ∃ final, run s w τ e t domain budget aliases (some initial) = some final ∧
      Invariant s w τ e t domain final ∧
      (∀ row ∈ initial.2.eval s w τ e t, row ∈ final.2.eval s w τ e t) ∧
      (∀ entry ∈ aliases, ∀ row, (entry.eval s w τ e t).eraseDups = [row] →
        row ∈ domain.eval s w τ e t → row ∈ final.2.eval s w τ e t) := by
  induction aliases generalizing initial with
  | nil => exact ⟨initial, rfl, hi, fun _ h => h, by simp⟩
  | cons entry aliases ih =>
    obtain ⟨next, hs, hn, mono, covered⟩ := select_complete hi
      (terms entry List.mem_cons_self) bound
    obtain ⟨final, hf, hfinal, mono', covered'⟩ := ih hn
      (fun value hv => terms value (List.mem_cons_of_mem _ hv))
    refine ⟨final, ?_, hfinal, fun row hr => mono' row (mono row hr), ?_⟩
    · change run s w τ e t domain budget aliases
        ((some initial).bind fun state => select s w τ e t domain budget state entry) = some final
      simpa only [Option.bind_some, hs] using hf
    · intro value hv row hr hd
      rcases List.mem_cons.mp hv with rfl | hv
      · exact mono' row (covered row hr hd)
      · exact covered' value hv row hr hd

theorem empty_invariant (domain : Rel) : Invariant s w τ e t domain ([], .empty .unary) := by
  refine ⟨.empty _, by simp, by simp, by simp, ?_, ?_, rfl⟩
  · intro row
    change row ∈ ([] : Relation) ↔ _
    simp
  · intro row hr
    change row ∈ ([] : Relation) at hr
    simp at hr

/-- A concrete finite singleton cover and a checked row budget ensure capture
is defined. Alias duplication does not consume budget or duplicate members. -/
theorem selections_complete (aliases : List Rel) (domain : Rel) (budget : Nat)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ row ∈ domain.eval s w τ e t,
      ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row])
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget) :
    ∃ selected, Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) selected ∧
      selected.length = (domain.eval s w τ e t).toFinset.card ∧
      (∀ entry ∈ selected, entry.Term) ∧
      (∀ row, row ∈ (Backend.Alloy.Behavioral.Full.union selected).eval s w τ e t ↔
        row ∈ domain.eval s w τ e t) := by
  obtain ⟨final, hf, hi, _, hc⟩ := run_complete (empty_invariant (s := s) (w := w)
    (τ := τ) (e := e) (t := t) domain) terms bound
  have rows (row : List Atom) : row ∈ final.2.eval s w τ e t ↔ row ∈ domain.eval s w τ e t := by
    constructor
    · exact hi.subset row
    · intro hr
      obtain ⟨entry, he, single⟩ := cover row hr
      exact hc entry he row single hr
  have cards : (final.2.eval s w τ e t).toFinset = (domain.eval s w τ e t).toFinset := by
    ext row
    simp only [List.mem_toFinset, rows]
  refine ⟨final.1.reverse, ?_, ?_, ?_, ?_⟩
  · rw [selections_correct, hf]
    rfl
  · rw [List.length_reverse, ← hi.card, cards]
  · intro entry he
    exact hi.terms entry (List.mem_reverse.mp he)
  · intro row
    rw [Backend.Alloy.Behavioral.Full.union,
      union_rows _ (fun entry he => hi.terms entry (List.mem_reverse.mp he)) _ (.empty _)]
    change (row ∈ ([] : Relation) ∨ _) ↔ _
    simp only [List.not_mem_nil, false_or, List.mem_reverse]
    exact (hi.rows row).symm.trans (rows row)

theorem selections_unique (aliases : List Rel) (domain : Rel) (budget : Nat)
    (ha : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) a)
    (hb : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) b) : a = b := by
  rw [selections_correct] at ha hb
  exact Option.some.inj (ha.symm.trans hb)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem selections_cardinality (aliases : List Rel) (domain : Rel) (budget : Nat)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ row ∈ domain.eval s w τ e t,
      ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row])
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget)
    (selected : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) chosen) :
    chosen.length = (domain.eval s w τ e t).toFinset.card := by
  obtain ⟨complete, hc, hcard, _, _⟩ := selections_complete aliases domain budget terms cover bound
  exact selections_unique aliases domain budget selected hc ▸ hcard

theorem capture_complete (aliases : List Rel) (domain : Rel) (budget : Nat)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ row ∈ domain.eval s w τ e t,
      ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row])
    (bound : (domain.eval s w τ e t).toFinset.card ≤ budget) :
    ∃ frozen, Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen := by
  obtain ⟨chosen, hc, _, _, rows⟩ := selections_complete aliases domain budget terms cover bound
  refine ⟨Backend.Alloy.Behavioral.Full.union chosen, ?_⟩
  apply (Value.bind_meaning _ _ (Value.selections_built aliases domain budget) ?_).mpr
  · refine ⟨chosen, hc, ?_⟩
    refine ⟨.equal domain (Backend.Alloy.Behavioral.Full.union chosen), by simp, ?_⟩
    exact fun row => (rows row).symm
  · intro chosen g x hg
    simp at hg
    rw [hg.1]
    exact .equal _ _

theorem run_none (aliases : List Rel) : run s w τ e t domain budget aliases none = none := by
  induction aliases with
  | nil => rfl
  | cons entry aliases ih => exact ih

theorem select_members (h : select s w τ e t domain budget state entry = some next) :
    ∀ value ∈ next.1, value = entry ∨ value ∈ state.1 := by
  classical
  unfold select at h
  split at h
  · split at h
    · cases Option.some.inj h
      exact fun value hv => List.mem_cons.mp hv
    · contradiction
  · cases Option.some.inj h
    exact fun _ hv => Or.inr hv

theorem run_members (h : run s w τ e t domain budget aliases (some initial) = some final) :
    ∀ value ∈ final.1, value ∈ aliases ∨ value ∈ initial.1 := by
  induction aliases generalizing initial with
  | nil =>
    cases Option.some.inj h
    exact fun _ hv => Or.inr hv
  | cons entry aliases ih =>
    change run s w τ e t domain budget aliases
      (select s w τ e t domain budget initial entry) = some final at h
    cases step : select s w τ e t domain budget initial entry with
    | none =>
      rw [step, run_none] at h
      contradiction
    | some next =>
      rw [step] at h
      intro value hv
      rcases ih h value hv with ha | hn
      · exact Or.inl (List.mem_cons_of_mem _ ha)
      · rcases select_members step value hn with rfl | hi
        · exact Or.inl List.mem_cons_self
        · exact Or.inr hi

theorem selections_members (aliases : List Rel) (domain : Rel) (budget : Nat)
    (h : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) selected) :
    ∀ entry ∈ selected, entry ∈ aliases := by
  rw [selections_correct, Option.map_eq_some_iff] at h
  obtain ⟨final, hf, rfl⟩ := h
  intro entry he
  rcases run_members hf entry (List.mem_reverse.mp he) with ha | hi
  · exact ha
  · simp at hi

end Selection
end ClaferCompiler.Correctness.Behavioral.Full
