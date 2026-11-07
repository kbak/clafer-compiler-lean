module

public import ClaferCompiler.Correctness.Behavioral.Full.Collections

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Encoding
attribute [local instance] Classical.propDecidable

namespace Selection
abbrev State := List Rel × Rel

def member (domain seen entry : Rel) : Formula :=
  .binary .conj (.mult .one entry)
    (.binary .conj (.subset entry domain) (.unary .neg (.subset entry seen)))

def choices (domain : Rel) (budget : Nat) (state : State) (entry : Rel) :
    Backend.Alloy.Behavioral.Full.Value State :=
  let present := (member domain state.2 entry, (entry :: state.1, .union state.2 entry))
  let absent := (Formula.unary .neg (member domain state.2 entry), state)
  ⟨if state.1.length < budget then [present, absent] else [absent]⟩

/-- Selection is determined by finite relation observations. This predicate
does not mention target formula truth or source expression truth. -/
def Eligible (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (domain seen entry : Rel) : Prop :=
  (entry.eval s w τ e t).eraseDups.length = 1 ∧
    (∀ row ∈ entry.eval s w τ e t, row ∈ domain.eval s w τ e t) ∧
    ¬ (∀ row ∈ entry.eval s w τ e t, row ∈ seen.eval s w τ e t)

def select (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (domain : Rel) (budget : Nat) (state : State) (entry : Rel) : Option State :=
  if Eligible s w τ e t domain state.2 entry then
    if state.1.length < budget then some (entry :: state.1, .union state.2 entry) else none
  else some state

theorem member_built (domain seen entry : Rel) : (member domain seen entry).Built :=
  .binary .conj (.mult _ _) (.binary .conj (.subset _ _) (.unary .neg (.subset _ _)))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem member_correct (domain seen entry : Rel) :
    (member domain seen entry).Holds s w τ e t ↔ Eligible s w τ e t domain seen entry := by
  rw [member, holds_and (.mult _ _) (.binary .conj (.subset _ _) (.unary .neg (.subset _ _))),
    holds_and (.subset _ _) (.unary .neg (.subset _ _)), holds_neg (.subset _ _)]
  change ((Backend.Alloy.Multiplicity.one.holds (entry.eval s w τ e t).eraseDups.length = true) ∧ _) ↔ _
  simp only [Backend.Alloy.Multiplicity.holds, beq_iff_eq, Eligible]
  rfl

theorem choices_built (domain : Rel) (budget : Nat) (state : State) (entry : Rel) :
    Value.Built (choices domain budget state entry) := by
  intro g x h
  dsimp [choices] at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with h | h
    · rw [h.1]; exact member_built _ _ _
    · rw [h.1]; exact .unary .neg (member_built _ _ _)
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    rw [h.1]; exact .unary .neg (member_built _ _ _)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem choices_correct (domain : Rel) (budget : Nat) (state result : State) (entry : Rel) :
    Value.Meaning s w τ e t (choices domain budget state entry) result ↔
      select s w τ e t domain budget state entry = some result := by
  have hm := member_correct (s := s) (w := w) (τ := τ) (e := e) (t := t) domain state.2 entry
  have hn := holds_neg (s := s) (w := w) (τ := τ) (e := e) (t := t)
    (member_built domain state.2 entry)
  by_cases room : state.1.length < budget
  · simp only [Value.Meaning, choices, ite_eq_left room, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq]
    constructor
    · rintro ⟨g, (⟨rfl, he⟩ | ⟨rfl, he⟩), hg⟩
      · have hp := hm.mp hg
        simp [select, hp, room, he]
      · have hp := hn.mp hg
        have hp' : ¬ Eligible s w τ e t domain state.2 entry := fun h => hp (hm.mpr h)
        simp [select, hp', he]
    · intro h
      by_cases hp : Eligible s w τ e t domain state.2 entry
      · have he : (entry :: state.1, Rel.union state.2 entry) = result := by
          simpa [select, hp, room] using h
        exact ⟨_, Or.inl ⟨rfl, he.symm⟩, hm.mpr hp⟩
      · have he : state = result := by simpa [select, hp] using h
        exact ⟨_, Or.inr ⟨rfl, he.symm⟩, hn.mpr (fun h => hp (hm.mp h))⟩
  · simp only [Value.Meaning, choices, ite_eq_right room, List.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨g, ⟨rfl, he⟩, hg⟩
      have hp : ¬ Eligible s w τ e t domain state.2 entry := fun h => hn.mp hg (hm.mpr h)
      simp [select, hp, he]
    · intro h
      by_cases hp : Eligible s w τ e t domain state.2 entry
      · simp [select, hp, room] at h
      · have he : state = result := by simpa [select, hp] using h
        exact ⟨_, ⟨rfl, he.symm⟩, hn.mpr (fun h => hp (hm.mp h))⟩

def run (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (domain : Rel) (budget : Nat) (aliases : List Rel) (initial : Option State) : Option State :=
  aliases.foldl (fun states entry => states.bind (fun state =>
    select s w τ e t domain budget state entry)) initial

theorem fold_built (domain : Rel) (budget : Nat) (aliases : List Rel)
    (initial : Backend.Alloy.Behavioral.Full.Value State) (hi : Value.Built initial) :
    Value.Built (aliases.foldl (fun values entry =>
      values.bind (fun state => choices domain budget state entry)) initial) := by
  induction aliases generalizing initial with
  | nil => exact hi
  | cons entry aliases ih =>
    exact ih _ (Value.bind_built initial _ hi (fun state => choices_built _ _ state entry))

theorem fold_correct (domain : Rel) (budget : Nat) (aliases : List Rel)
    (initial : Backend.Alloy.Behavioral.Full.Value State) (hi : Value.Built initial)
    (observed : Option State)
    (represented : ∀ state, Value.Meaning s w τ e t initial state ↔ observed = some state) :
    ∀ result, Value.Meaning s w τ e t (aliases.foldl (fun values entry =>
      values.bind (fun state => choices domain budget state entry)) initial) result ↔
      run s w τ e t domain budget aliases observed = some result := by
  induction aliases generalizing initial observed with
  | nil => exact represented
  | cons entry aliases ih =>
    apply ih _ (Value.bind_built initial _ hi (fun state => choices_built _ _ state entry))
      (observed.bind (fun state => select s w τ e t domain budget state entry))
    intro result
    rw [Value.bind_meaning _ _ hi (fun state => choices_built _ _ state entry)]
    simp only [represented, choices_correct, Option.bind_eq_some_iff]

/-- The actual compiler's guarded enumeration is exactly the finite greedy
selection on target rows, including duplicate aliases and explicit exhaustion.
Coverage and source cardinality are separate premises for completeness. -/
theorem selections_correct (aliases : List Rel) (domain : Rel) (budget : Nat) (result : List Rel) :
    Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) result ↔
      (run s w τ e t domain budget aliases (some ([], .empty .unary))).map
        (fun state => state.1.reverse) = some result := by
  rw [Backend.Alloy.Behavioral.Full.Value.selections, Value.map_meaning]
  have initial (state : State) : Value.Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.pure ([], .empty .unary)) state ↔
      some ([], Rel.empty .unary) = some state := by simp [eq_comm]
  have hf := fold_correct (s := s) (w := w) (τ := τ) (e := e) (t := t) domain budget aliases
    _ (Value.pure_built ([], .empty .unary)) _ initial
  change (∃ state, Value.Meaning s w τ e t
    (aliases.foldl (fun values entry => values.bind (fun state => choices domain budget state entry))
      (Backend.Alloy.Behavioral.Full.Value.pure ([], .empty .unary))) state ∧
    state.1.reverse = result) ↔ _
  simp only [hf, Option.map_eq_some_iff]

end Selection
end ClaferCompiler.Correctness.Behavioral.Full
