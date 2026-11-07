module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Collections
public import ClaferCompiler.Correctness.Behavioral.ExpressionsMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Encoding

namespace Value

def Built (a : Backend.Alloy.Behavioral.Full.Value α) : Prop :=
  ∀ g x, (g, x) ∈ a.cases → g.Built

def Meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (a : Backend.Alloy.Behavioral.Full.Value α) (x : α) : Prop :=
  ∃ g, (g, x) ∈ a.cases ∧ g.Holds s w τ e t

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem pure_built (x : α) : Built (Backend.Alloy.Behavioral.Full.Value.pure x) := by
  intro g y h
  simp only [Backend.Alloy.Behavioral.Full.Value.pure, List.mem_singleton, Prod.mk.injEq] at h
  rw [h.1]
  exact .truth

theorem use_built (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Formula)
    (ha : Built a) (hf : ∀ x, (f x).Built) : (a.use f).Built := by
  rcases a with ⟨choices⟩
  induction choices with
  | nil => exact .falsity
  | cons choice choices ih =>
    rcases choice with ⟨g, x⟩
    exact .binary .disj (.binary .conj (ha g x (by simp)) (hf x))
      (ih (fun h y hy => ha h y (by simp [hy])))

theorem use_meaning (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Formula)
    (ha : Built a) (hf : ∀ x, (f x).Built) :
    (a.use f).Holds s w τ e t ↔ ∃ x, Meaning s w τ e t a x ∧ (f x).Holds s w τ e t := by
  rcases a with ⟨choices⟩
  induction choices with
  | nil =>
    change False ↔ ∃ x, Meaning s w τ e t ⟨[]⟩ x ∧ (f x).Holds s w τ e t
    simp [Meaning]
  | cons choice choices ih =>
    rcases choice with ⟨g, x⟩
    have hg := ha g x (by simp)
    have ht : Built (Backend.Alloy.Behavioral.Full.Value.mk choices) :=
      fun h y hy => ha h y (by simp [hy])
    change (Formula.binary .disj (.binary .conj g (f x))
      ((Backend.Alloy.Behavioral.Full.Value.mk choices).use f)).Holds s w τ e t ↔ _
    rw [holds_or (.binary .conj hg (hf x)) (use_built _ _ ht hf),
      holds_and hg (hf x), ih ht]
    simp only [Meaning, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨y, ⟨guard, hy, hguard⟩, hfy⟩)
      · exact ⟨x, ⟨g, Or.inl ⟨rfl, rfl⟩, h.1⟩, h.2⟩
      · exact ⟨y, ⟨guard, Or.inr hy, hguard⟩, hfy⟩
    · rintro ⟨y, ⟨guard, (h | h), hguard⟩, hfy⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨hguard, hfy⟩
      · exact Or.inr ⟨y, ⟨guard, h, hguard⟩, hfy⟩

@[simp] theorem pure_meaning (x y : α) :
    Meaning s w τ e t (Backend.Alloy.Behavioral.Full.Value.pure x) y ↔ y = x := by
  simp [Meaning, Backend.Alloy.Behavioral.Full.Value.pure, eq_comm]

@[simp] theorem missing_meaning (x : α) :
    ¬ Meaning s w τ e t (Backend.Alloy.Behavioral.Full.Value.missing) x := by
  simp [Meaning, Backend.Alloy.Behavioral.Full.Value.missing]

theorem defined_meaning (a : Backend.Alloy.Behavioral.Full.Value α) (ha : Built a) :
    a.defined.Holds s w τ e t ↔ ∃ x, Meaning s w τ e t a x := by
  rw [Backend.Alloy.Behavioral.Full.Value.defined, use_meaning _ _ ha (fun _ => .truth)]
  simp

theorem map_built (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → β) (ha : Built a) :
    Built (a.map f) := by
  intro g y h
  obtain ⟨⟨h, x⟩, hx, he⟩ := List.mem_map.mp h
  have hh := ha h x hx
  cases he
  exact hh

theorem map_meaning (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → β) :
    Meaning s w τ e t (a.map f) y ↔ ∃ x, Meaning s w τ e t a x ∧ f x = y := by
  simp only [Meaning, Backend.Alloy.Behavioral.Full.Value.map, List.mem_map]
  constructor
  · rintro ⟨g, ⟨⟨h, x⟩, hx, he⟩, hg⟩
    cases he
    exact ⟨x, ⟨h, hx, hg⟩, rfl⟩
  · rintro ⟨x, ⟨g, hx, hg⟩, rfl⟩
    exact ⟨g, ⟨(g, x), hx, rfl⟩, hg⟩

theorem bind_built (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Backend.Alloy.Behavioral.Full.Value β) (ha : Built a) (hf : ∀ x, Built (f x)) :
    Built (a.bind f) := by
  intro g y h
  obtain ⟨⟨p, x⟩, hx, hy⟩ := List.mem_flatMap.mp h
  obtain ⟨⟨q, z⟩, hz, he⟩ := List.mem_map.mp hy
  have hh := Formula.Built.binary .conj (ha p x hx) (hf x q z hz)
  cases he
  exact hh

theorem bind_meaning (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Backend.Alloy.Behavioral.Full.Value β) (ha : Built a) (hf : ∀ x, Built (f x)) :
    Meaning s w τ e t (a.bind f) y ↔
      ∃ x, Meaning s w τ e t a x ∧ Meaning s w τ e t (f x) y := by
  constructor
  · rintro ⟨g, hg, htruth⟩
    obtain ⟨⟨p, x⟩, hx, hy⟩ := List.mem_flatMap.mp hg
    obtain ⟨⟨q, z⟩, hz, he⟩ := List.mem_map.mp hy
    have hh := holds_and (s := s) (w := w) (τ := τ) (e := e) (t := t) (ha p x hx) (hf x q z hz)
    cases he
    have h := hh.mp htruth
    exact ⟨x, ⟨p, hx, h.1⟩, ⟨q, hz, h.2⟩⟩
  · rintro ⟨x, ⟨p, hx, hp⟩, ⟨q, hy, hq⟩⟩
    refine ⟨.binary .conj p q, ?_, (holds_and (ha p x hx) (hf x q y hy)).mpr ⟨hp, hq⟩⟩
    exact List.mem_flatMap.mpr ⟨(p, x), hx, List.mem_map.mpr ⟨(q, y), hy, rfl⟩⟩

theorem pair_built (a : Backend.Alloy.Behavioral.Full.Value α)
    (b : Backend.Alloy.Behavioral.Full.Value β) (ha : Built a) (hb : Built b) :
    Built (a.pair b) := bind_built a _ ha (fun _ => map_built b _ hb)

theorem pair_meaning (a : Backend.Alloy.Behavioral.Full.Value α)
    (b : Backend.Alloy.Behavioral.Full.Value β) (ha : Built a) (hb : Built b) :
    Meaning s w τ e t (a.pair b) (x, y) ↔
      Meaning s w τ e t a x ∧ Meaning s w τ e t b y := by
  rw [Backend.Alloy.Behavioral.Full.Value.pair,
    bind_meaning a _ ha (fun _ => map_built b _ hb)]
  simp only [map_meaning, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ha, _, hb, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨x, ha, y, hb, rfl, rfl⟩

def conditionalChoices (c : Backend.Alloy.Behavioral.Partial.Translation) (x y : α) :
    Backend.Alloy.Behavioral.Full.Value α :=
  ⟨[(.binary .conj c.defined c.truth.raw, x),
    (.binary .conj c.defined (.unary .neg c.truth.raw), y)]⟩

theorem conditionalChoices_built (hd : c.defined.Built) (hr : c.truth.raw.Built) (x y : α) :
    Built (conditionalChoices c x y) := by
  intro g z hg
  simp [conditionalChoices] at hg
  rcases hg with h | h
  · rw [h.1]
    exact .binary .conj hd hr
  · rw [h.1]
    exact .binary .conj hd (.unary .neg hr)

theorem conditionalChoices_meaning (hd : c.defined.Built) (hr : c.truth.raw.Built) (x y z : α) :
    Meaning s w τ e t (conditionalChoices c x y) z ↔
      c.defined.Holds s w τ e t ∧
        ((c.truth.raw.Holds s w τ e t ∧ z = x) ∨ (¬ c.truth.raw.Holds s w τ e t ∧ z = y)) := by
  constructor
  · rintro ⟨g, hg, htruth⟩
    simp [conditionalChoices] at hg
    rcases hg with h | h
    · obtain ⟨rfl, rfl⟩ := h
      have hh := (holds_and hd hr).mp htruth
      exact ⟨hh.1, Or.inl ⟨hh.2, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      have hh := (holds_and hd (.unary .neg hr)).mp htruth
      exact ⟨hh.1, Or.inr ⟨(holds_neg hr).mp hh.2, rfl⟩⟩
  · rintro ⟨hdef, (⟨hraw, rfl⟩ | ⟨hraw, rfl⟩)⟩
    · exact ⟨.binary .conj c.defined c.truth.raw, by simp [conditionalChoices],
        (holds_and hd hr).mpr ⟨hdef, hraw⟩⟩
    · exact ⟨.binary .conj c.defined (.unary .neg c.truth.raw), by simp [conditionalChoices],
        (holds_and hd (.unary .neg hr)).mpr ⟨hdef, (holds_neg hr).mpr hraw⟩⟩

theorem conditional_built (a b : Backend.Alloy.Behavioral.Full.Value α)
    (ha : Built a) (hb : Built b) (hd : c.defined.Built) (hr : c.truth.raw.Built) :
    Built (Backend.Alloy.Behavioral.Full.Value.conditional c a b) :=
  bind_built _ _ (pair_built a b ha hb) (fun (x, y) => conditionalChoices_built hd hr x y)

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The emitted original domain requires both source branches even when raw
condition truth selects just one of their values. -/
theorem conditional_defined (a b : Backend.Alloy.Behavioral.Full.Value α)
    (ha : Built a) (hb : Built b) (hd : c.defined.Built) (hr : c.truth.raw.Built) :
    (Backend.Alloy.Behavioral.Full.Value.conditional c a b).defined.Holds s w τ e t ↔
      c.defined.Holds s w τ e t ∧ a.defined.Holds s w τ e t ∧ b.defined.Holds s w τ e t := by
  rw [defined_meaning _ (conditional_built a b ha hb hd hr),
    defined_meaning a ha, defined_meaning b hb]
  change (∃ z, Meaning s w τ e t ((a.pair b).bind
    (fun p => conditionalChoices c p.1 p.2)) z) ↔ _
  have bindLaw (z : α) := bind_meaning (s := s) (w := w) (τ := τ) (e := e) (t := t)
    (y := z) (a.pair b) (fun p => conditionalChoices c p.1 p.2)
    (pair_built a b ha hb) (fun p => conditionalChoices_built hd hr p.1 p.2)
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨⟨x, y⟩, hp, hchoice⟩ := (bindLaw z).mp hz
    have hp := (pair_meaning a b ha hb).mp hp
    have hc := (conditionalChoices_meaning hd hr x y z).mp hchoice
    exact ⟨hc.1, ⟨x, hp.1⟩, ⟨y, hp.2⟩⟩
  · rintro ⟨hc, ⟨x, hx⟩, ⟨y, hy⟩⟩
    by_cases h : c.truth.raw.Holds s w τ e t
    · refine ⟨x, (bindLaw x).mpr ⟨(x, y), (pair_meaning a b ha hb).mpr ⟨hx, hy⟩, ?_⟩⟩
      exact (conditionalChoices_meaning hd hr x y x).mpr ⟨hc, Or.inl ⟨h, rfl⟩⟩
    · refine ⟨y, (bindLaw y).mpr ⟨(x, y), (pair_meaning a b ha hb).mpr ⟨hx, hy⟩, ?_⟩⟩
      exact (conditionalChoices_meaning hd hr x y y).mpr ⟨hc, Or.inr ⟨h, rfl⟩⟩

theorem selections_built (aliases : List Rel) (domain : Rel) (budget : Nat) :
    Built (Backend.Alloy.Behavioral.Full.Value.selections aliases domain budget) := by
  let step := fun (values : Backend.Alloy.Behavioral.Full.Value (List Rel × Rel)) (entry : Rel) =>
    values.bind fun (chosen, seen) =>
      let member := Formula.binary .conj (.mult .one entry)
        (.binary .conj (.subset entry domain) (.unary .neg (.subset entry seen)))
      let absent := (Formula.unary .neg member, (chosen, seen))
      let present := (member, (entry :: chosen, .union seen entry))
      Backend.Alloy.Behavioral.Full.Value.mk
        (if chosen.length < budget then [present, absent] else [absent])
  have hstep (values : Backend.Alloy.Behavioral.Full.Value (List Rel × Rel)) (entry : Rel)
      (hvalues : Built values) : Built (step values entry) := by
    apply bind_built values _ hvalues
    rintro ⟨chosen, seen⟩ g y hg
    have hm : (Formula.binary .conj (.mult .one entry)
        (.binary .conj (.subset entry domain) (.unary .neg (.subset entry seen)))).Built :=
      .binary .conj (.mult _ _) (.binary .conj (.subset _ _) (.unary .neg (.subset _ _)))
    dsimp at hg
    split at hg
    · simp at hg
      rcases hg with h | h
      · rw [h.1]; exact hm
      · rw [h.1]; exact .unary .neg hm
    · simp at hg
      rw [hg.1]; exact .unary .neg hm
  have hfold (xs : List Rel) (values : Backend.Alloy.Behavioral.Full.Value (List Rel × Rel))
      (hvalues : Built values) : Built (xs.foldl step values) := by
    induction xs generalizing values with
    | nil => exact hvalues
    | cons x xs ih => exact ih _ (hstep _ x hvalues)
  exact map_built _ _ (hfold aliases _ (pure_built (([] : List Rel), Rel.empty .unary)))

theorem capture_built (aliases : List Rel) (domain : Rel) (budget : Nat) :
    Built (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) := by
  apply bind_built _ _ (selections_built aliases domain budget)
  intro selected g x h
  simp at h
  rw [h.1]
  exact .equal _ _

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Every successfully captured value is exactly the current original domain.
This is unconditional on entry coverage; coverage is needed for completeness,
not to prevent a successful capture from silently dropping a domain member. -/
theorem capture_sound (aliases : List Rel) (domain : Rel) (budget : Nat)
    (h : Meaning s w τ e t
      (Backend.Alloy.Behavioral.Full.Value.capture aliases domain budget) frozen) :
    ∀ row, row ∈ domain.eval s w τ e t ↔ row ∈ frozen.eval s w τ e t := by
  have hbody (selected : List Rel) : Built
      (Backend.Alloy.Behavioral.Full.Value.mk [(Formula.equal domain (Backend.Alloy.Behavioral.Full.union selected), Backend.Alloy.Behavioral.Full.union selected)]) := by
    intro g x hx
    simp at hx
    rw [hx.1]
    exact .equal _ _
  obtain ⟨selected, _, g, hg, htruth⟩ :=
    (bind_meaning _ _ (selections_built aliases domain budget) hbody).mp h
  simp at hg
  obtain ⟨rfl, rfl⟩ := hg
  exact htruth

/-- A representation statement about the finite guarded values, parameterized
by an interpretation of target value syntax. This is a composition interface,
not the concrete trace representation or the full preservation theorem. -/
def Represents (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (interpret : α → β) (a : Backend.Alloy.Behavioral.Full.Value α) (observed : Option β) : Prop :=
  ∀ y, (∃ x, Meaning s w τ e t a x ∧ interpret x = y) ↔ observed = some y

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem represents_defined (a : Backend.Alloy.Behavioral.Full.Value α) (ha : Built a)
    (h : Represents s w τ e t interpret a observed) :
    a.defined.Holds s w τ e t ↔ observed.isSome = true := by
  rw [defined_meaning a ha]
  constructor
  · rintro ⟨x, hx⟩
    have hh := (h (interpret x)).mp ⟨x, hx, rfl⟩
    simp [hh]
  · intro hh
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hh
    obtain ⟨x, hx, _⟩ := (h y).mpr hy
    exact ⟨x, hx⟩

theorem guard_built (p : Formula) (a : Backend.Alloy.Behavioral.Full.Value α)
    (hp : p.Built) (ha : Built a) : Built (a.guard p) := by
  intro g x hx
  obtain ⟨⟨h, y⟩, hy, eq⟩ := List.mem_map.mp hx
  cases eq
  exact .binary .conj hp (ha h _ hy)

theorem guard_meaning (p : Formula) (a : Backend.Alloy.Behavioral.Full.Value α)
    (hp : p.Built) (ha : Built a) :
    Meaning s w τ e t (a.guard p) x ↔ p.Holds s w τ e t ∧ Meaning s w τ e t a x := by
  constructor
  · rintro ⟨g, hg, holds⟩
    obtain ⟨⟨h, y⟩, hy, eq⟩ := List.mem_map.mp hg
    cases eq
    obtain ⟨hp', hh⟩ := (Encoding.holds_and hp (ha h _ hy)).mp holds
    exact ⟨hp', h, hy, hh⟩
  · rintro ⟨hp', h, hx, hh⟩
    exact ⟨.binary .conj p h, List.mem_map.mpr ⟨(h, x), hx, rfl⟩,
      (Encoding.holds_and hp (ha h x hx)).mpr ⟨hp', hh⟩⟩

end Value
end ClaferCompiler.Correctness.Behavioral.Full
