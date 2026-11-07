module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsValueMap
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open IR.Behavioral.Expression.Ranges
namespace FoldSelections
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def selected (aliases : List Rel) (domain : Rel) (budget : Nat) : Value (List Rel) :=
  (Value.selections aliases domain budget).bind fun heads =>
    ⟨[(.equal domain (Backend.Alloy.Behavioral.Full.union heads), heads)]⟩

def choices (aliases : List Rel) (pairs : List (Rel × CollectionEstimate))
    (initial : Value (List Rel) := .pure []) : Value (List Rel) :=
  pairs.foldl (fun before pair => (before.pair (selected aliases pair.1 pair.2.budget)).map
    fun (old, now) => old ++ now) initial

theorem selected_built (aliases : List Rel) (domain : Rel) (budget : Nat) :
    Full.Value.Built (selected aliases domain budget) := SyntaxBuilt.selectionChecked aliases domain budget

theorem selected_meaning (aliases : List Rel) (domain : Rel) (budget : Nat) :
    Full.Value.Meaning s w τ e t (selected aliases domain budget) heads ↔
      Full.Value.Meaning s w τ e t (Value.selections aliases domain budget) heads ∧
        (Formula.equal domain (Backend.Alloy.Behavioral.Full.union heads)).Holds s w τ e t := by
  unfold selected
  have body (heads : List Rel) : Full.Value.Built
      (Value.mk [(Formula.equal domain (Backend.Alloy.Behavioral.Full.union heads), heads)]) := by
    intro g x hx
    simp at hx
    rw [hx.1]
    exact .equal _ _
  rw [Full.Value.bind_meaning _ _ (Full.Value.selections_built _ _ _) body]
  simp only [Full.Value.Meaning, List.mem_singleton, Prod.mk.injEq]
  aesop

theorem choices_built (aliases : List Rel) (pairs : List (Rel × CollectionEstimate))
    (hi : Full.Value.Built initial) : Full.Value.Built (choices aliases pairs initial) :=
  SyntaxBuilt.occurrenceChoices aliases pairs initial hi

theorem choices_meaning (aliases : List Rel) (pairs : List (Rel × CollectionEstimate))
    (hi : Full.Value.Built initial) :
    Full.Value.Meaning s w τ e t (choices aliases pairs initial) heads ↔
      ∃ start groups, Full.Value.Meaning s w τ e t initial start ∧
        List.Forall₂ (fun pair group =>
          Full.Value.Meaning s w τ e t (selected aliases pair.1 pair.2.budget) group) pairs groups ∧
        heads = start ++ groups.flatten := by
  induction pairs generalizing initial with
  | nil => simp [choices, List.forall₂_nil_left_iff]
  | cons pair pairs ih =>
    change Full.Value.Meaning s w τ e t
      (choices aliases pairs ((initial.pair (selected aliases pair.1 pair.2.budget)).map
        fun (old, now) => old ++ now)) heads ↔ _
    rw [ih (Full.Value.map_built _ _ (Full.Value.pair_built _ _ hi (selected_built _ _ _)))]
    constructor
    · rintro ⟨start, groups, hm, hs, rfl⟩
      obtain ⟨⟨old, now⟩, pairMeaning, rfl⟩ := (Full.Value.map_meaning _ _).mp hm
      obtain ⟨ho, hn⟩ := (Full.Value.pair_meaning _ _ hi (selected_built _ _ _)).mp pairMeaning
      exact ⟨old, now :: groups, ho, .cons hn hs, by simp [List.append_assoc]⟩
    · rintro ⟨start, groups, hs, hg, rfl⟩
      cases hg with
      | cons hnow hrest =>
        refine ⟨_, _, (Full.Value.map_meaning _ _).mpr
          ⟨(start, _), (Full.Value.pair_meaning _ _ hi (selected_built _ _ _)).mpr ⟨hs, hnow⟩, rfl⟩,
          hrest, ?_⟩
        simp [List.append_assoc]

theorem choices_initial_meaning (aliases : List Rel) (pairs : List (Rel × CollectionEstimate)) :
    Full.Value.Meaning s w τ e t (choices aliases pairs) heads ↔
      ∃ groups, List.Forall₂ (fun pair group =>
          Full.Value.Meaning s w τ e t (selected aliases pair.1 pair.2.budget) group) pairs groups ∧
        heads = groups.flatten := by
  rw [choices_meaning aliases pairs (Full.Value.pure_built _)]
  simp only [Full.Value.pure_meaning]
  simp

def HeadRows (labels : Fin o ↪ Nat) (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (r : Rel) (x : Completion o) : Prop :=
  r.Term ∧ ∀ u, Mixed.Unary (completionAtom labels) {x} (r.eval s w τ e u)

def DomainRows (labels : Fin o ↪ Nat) (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (pair : Rel × CollectionEstimate) (S : Set (Completion o)) : Prop :=
  Mixed.Unary (completionAtom labels) S (pair.1.eval s w τ e t) ∧
    S.ncard ≤ pair.2.budget ∧ S ⊆ observedDomain w

theorem selected_sources {b : Inputs k} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
    {ρ : Clafer.Behavioral.Environment (Completion o) n} {labels : Fin o ↪ Nat}
    (hc : LexicalRows b s τ labels c ρ e)
    (rows : DomainRows labels s b.width τ e t pair S)
    (meaning : Full.Value.Meaning s b.width τ e t (selected c.lexical.aliases pair.1 pair.2.budget) heads) :
    ∃ xs, (xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) ∧
      List.Forall₂ (HeadRows labels s b.width τ e) heads xs := by
  have selected := (selected_meaning _ _ _).mp meaning |>.1
  have terms : ∀ entry ∈ c.lexical.aliases, entry.Term := fun r hr => (hc.aliases r hr).term
  have cover : ∀ x ∈ S, ∃ entry ∈ c.lexical.aliases,
      Mixed.Unary (completionAtom labels) {x} (entry.eval s b.width τ e t) := by
    intro x hx
    obtain ⟨entry, he, hs⟩ := hc.cover x (rows.2.2 hx)
    exact ⟨entry, he, hs t⟩
  obtain ⟨decode, singles, distinct, members⟩ := Selection.source_heads (Sum.inr 0)
    (completionAtom labels).injective rows.1 terms cover rows.2.1 selected
  refine ⟨heads.map decode, ⟨distinct, members⟩, ?_⟩
  rw [List.forall₂_map_right_iff, List.forall₂_same]
  intro entry he
  refine ⟨(singles entry he).1, ?_⟩
  have stable := hc.aliases entry (Selection.selections_members _ _ _ selected entry he)
  intro u row
  rw [← stable.rows t u row]
  exact (singles entry he).2 row

theorem selected_complete {b : Inputs k} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
    {ρ : Clafer.Behavioral.Environment (Completion o) n} {labels : Fin o ↪ Nat}
    (hc : LexicalRows b s τ labels c ρ e)
    (rows : DomainRows labels s b.width τ e t pair S) :
    ∃ heads, Full.Value.Meaning s b.width τ e t (selected c.lexical.aliases pair.1 pair.2.budget) heads := by
  have cover : ∀ row ∈ pair.1.eval s b.width τ e t,
      ∃ entry ∈ c.lexical.aliases, (entry.eval s b.width τ e t).eraseDups = [row] := by
    intro row hr
    obtain ⟨x, hx, rfl⟩ := (rows.1 row).mp hr
    obtain ⟨entry, he, hrows⟩ := hc.cover x (rows.2.2 hx)
    exact ⟨entry, he, Mixed.unary_singleton_rows (hrows t)⟩
  have bound : (pair.1.eval s b.width τ e t).toFinset.card ≤ pair.2.budget := by
    rw [Mixed.unary_card (completionAtom labels).injective rows.1]
    exact rows.2.1
  obtain ⟨heads, hm, _, _, equal⟩ := Selection.selections_complete c.lexical.aliases pair.1 pair.2.budget
    (fun r hr => (hc.aliases r hr).term) cover bound
  exact ⟨heads, (selected_meaning _ _ _).mpr ⟨hm, fun row => (equal row).symm⟩⟩

theorem forall₂_append {R : α → β → Prop}
    (ha : List.Forall₂ R as bs) (hb : List.Forall₂ R cs ds) :
    List.Forall₂ R (as ++ cs) (bs ++ ds) := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

theorem groups_sources {b : Inputs k} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
    {ρ : Clafer.Behavioral.Environment (Completion o) n} {labels : Fin o ↪ Nat}
    (hc : LexicalRows b s τ labels c ρ e)
    (rows : List.Forall₂ (DomainRows labels s b.width τ e t) pairs sets)
    (meaning : List.Forall₂ (fun pair group =>
      Full.Value.Meaning s b.width τ e t (selected c.lexical.aliases pair.1 pair.2.budget) group) pairs groups) :
    ∃ lists, List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists ∧
      List.Forall₂ (HeadRows labels s b.width τ e) groups.flatten lists.flatten := by
  induction rows generalizing groups with
  | nil => cases meaning; exact ⟨[], .nil, .nil⟩
  | cons row rows ih =>
    cases meaning with
    | cons hm tail =>
      obtain ⟨xs, hx, hrep⟩ := selected_sources hc row hm
      obtain ⟨lists, hl, hrels⟩ := ih tail
      exact ⟨xs :: lists, .cons hx hl, forall₂_append hrep hrels⟩

theorem choices_sources {b : Inputs k} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
    {ρ : Clafer.Behavioral.Environment (Completion o) n} {labels : Fin o ↪ Nat}
    (hc : LexicalRows b s τ labels c ρ e)
    (rows : List.Forall₂ (DomainRows labels s b.width τ e t) pairs sets)
    (meaning : Full.Value.Meaning s b.width τ e t (choices c.lexical.aliases pairs) heads) :
    ∃ lists, List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists ∧
      List.Forall₂ (HeadRows labels s b.width τ e) heads lists.flatten := by
  obtain ⟨groups, hm, rfl⟩ := (choices_initial_meaning _ _).mp meaning
  exact groups_sources hc rows hm

theorem choices_complete {b : Inputs k} {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
    {ρ : Clafer.Behavioral.Environment (Completion o) n} {labels : Fin o ↪ Nat}
    (hc : LexicalRows b s τ labels c ρ e)
    (rows : List.Forall₂ (DomainRows labels s b.width τ e t) pairs sets) :
    ∃ heads, Full.Value.Meaning s b.width τ e t (choices c.lexical.aliases pairs) heads := by
  have groups : ∃ groups, List.Forall₂ (fun pair group =>
      Full.Value.Meaning s b.width τ e t (selected c.lexical.aliases pair.1 pair.2.budget) group) pairs groups := by
    induction rows with
    | nil => exact ⟨[], .nil⟩
    | cons row rows ih =>
      obtain ⟨head, hh⟩ := selected_complete hc row
      obtain ⟨rest, hr⟩ := ih
      exact ⟨head :: rest, .cons hh hr⟩
  obtain ⟨groups, hm⟩ := groups
  exact ⟨groups.flatten, (choices_initial_meaning _ _).mpr ⟨groups, hm, rfl⟩⟩

end FoldSelections
end ClaferCompiler.Correctness.Behavioral.Full.Expressions
