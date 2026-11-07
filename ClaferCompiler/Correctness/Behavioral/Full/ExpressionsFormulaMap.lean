module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormula
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Expressions

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Encoding

namespace Expressions
-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem mapM_ok {α β ε : Type} (f : α → Except ε β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have he : [] = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst ys
    exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | error error => rw [hx] at h; contradiction
    | ok y =>
      cases hs : xs.mapM f with
      | error error => rw [hx, hs] at h; contradiction
      | ok rest =>
        have he : y :: rest = ys := by
          rw [hx, hs] at h
          exact Except.ok.inj h
        subst ys
        exact .cons hx (ih rest hs)

end Expressions

namespace Value
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

/-- Syntax obligations refer only to the choices present in the value. -/
theorem use_built_mem (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Formula)
    (ha : Built a) (hf : ∀ g x, (g, x) ∈ a.cases → (f x).Built) : (a.use f).Built := by
  rcases a with ⟨choices⟩
  induction choices with
  | nil => exact .falsity
  | cons choice choices ih =>
    rcases choice with ⟨g, x⟩
    exact .binary .disj (.binary .conj (ha g x (by simp)) (hf g x (by simp)))
      (ih (fun h y hy => ha h y (by simp [hy])) (fun h y hy => hf h y (by simp [hy])))

theorem use_meaning_mem (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Formula)
    (ha : Built a) (hf : ∀ g x, (g, x) ∈ a.cases → (f x).Built) :
    (a.use f).Holds s w τ e t ↔ ∃ x, Meaning s w τ e t a x ∧ (f x).Holds s w τ e t := by
  rcases a with ⟨choices⟩
  induction choices with
  | nil =>
    change False ↔ ∃ x, Meaning s w τ e t ⟨[]⟩ x ∧ (f x).Holds s w τ e t
    simp [Meaning]
  | cons choice choices ih =>
    rcases choice with ⟨g, x⟩
    have hg := ha g x (by simp)
    have hfx := hf g x (by simp)
    have ht : Built (Backend.Alloy.Behavioral.Full.Value.mk choices) :=
      fun h y hy => ha h y (by simp [hy])
    have hft : ∀ h y, (h, y) ∈ choices → (f y).Built :=
      fun h y hy => hf h y (by simp [hy])
    change (Formula.binary .disj (.binary .conj g (f x))
      ((Backend.Alloy.Behavioral.Full.Value.mk choices).use f)).Holds s w τ e t ↔ _
    rw [holds_or (.binary .conj hg hfx) (use_built_mem _ _ ht hft),
      holds_and hg hfx, ih ht hft]
    simp only [Meaning, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨y, ⟨guard, hy, hguard⟩, hfy⟩)
      · exact ⟨x, ⟨g, Or.inl ⟨rfl, rfl⟩, h.1⟩, h.2⟩
      · exact ⟨y, ⟨guard, Or.inr hy, hguard⟩, hfy⟩
    · rintro ⟨y, ⟨guard, (h | h), hguard⟩, hfy⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨hguard, hfy⟩
      · exact Or.inr ⟨y, ⟨guard, h, hguard⟩, hfy⟩
end Value

namespace Expressions
open Backend.Alloy.Behavioral.Full.Expressions
abbrev Translation := Backend.Alloy.Behavioral.Partial.Translation

/-- Each successful guarded branch keeps its original guard and its compiled
body. This uses the standard list traversal and no semantic choice function. -/
theorem partialMapM_cases (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Result Translation) (result : Translation)
    (h : partialMapM a f = .ok result) :
    ∃ choices : List (Formula × Translation),
      List.Forall₂ (fun input output => input.1 = output.1 ∧ f input.2 = .ok output.2) a.cases choices ∧
      result = ⟨⟨(Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.raw),
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.positive),
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.negative)⟩,
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.defined)⟩ := by
  unfold partialMapM at h
  cases hs : a.cases.mapM (fun input => Prod.mk input.1 <$> f input.2) with
  | error error => simp [hs] at h
  | ok choices =>
    refine ⟨choices, ?_, ?_⟩
    · have paired := mapM_ok _ _ _ hs
      apply paired.imp
      intro input output he
      cases hf : f input.2 with
      | error error => simp [hf] at he
      | ok body =>
        have heq : (input.1, body) = output := by simpa [hf] using he
        subst output
        exact ⟨rfl, rfl⟩
    · simpa [hs] using h.symm

theorem partial_cases_member {inputs : List (Formula × α)} {choices : List (Formula × Translation)}
    (f : α → Result Translation)
    (paired : List.Forall₂ (fun input output => input.1 = output.1 ∧ f input.2 = .ok output.2) inputs choices)
    (g : Formula) (body : Translation) :
    (g, body) ∈ choices ↔ ∃ x, (g, x) ∈ inputs ∧ f x = .ok body := by
  induction paired with
  | nil => simp
  | @cons input output inputs choices head tail ih =>
    rcases input with ⟨guard, x⟩
    rcases output with ⟨guard', p⟩
    obtain ⟨rfl, hp⟩ := head
    simp only [List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨y, hy, he⟩)
      · exact ⟨x, Or.inl ⟨rfl, rfl⟩, hp⟩
      · exact ⟨y, Or.inr hy, he⟩
    · rintro ⟨y, (⟨rfl, rfl⟩ | hy), he⟩
      · exact Or.inl ⟨rfl, (Except.ok.inj (he.symm.trans hp))⟩
      · exact Or.inr ⟨y, hy, he⟩

theorem partialMapM_built (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Result Translation) (result : Translation)
    (ha : Value.Built a)
    (bodies : ∀ g x body, (g, x) ∈ a.cases → f x = .ok body → Partial.Built body)
    (h : partialMapM a f = .ok result) : Partial.Built result := by
  obtain ⟨choices, paired, rfl⟩ := partialMapM_cases a f result h
  have hc : Value.Built (Backend.Alloy.Behavioral.Full.Value.mk choices) := by
    intro g p hp
    obtain ⟨x, hx, _⟩ := (partial_cases_member f paired g p).mp hp
    exact ha g x hx
  have hb : ∀ g p, (g, p) ∈ choices → Partial.Built p := by
    intro g p hp
    obtain ⟨x, hx, he⟩ := (partial_cases_member f paired g p).mp hp
    exact bodies g x p hx he
  refine ⟨⟨Value.use_built_mem _ _ hc (fun g p hp => (hb g p hp).truth.raw),
    Value.use_built_mem _ _ hc (fun g p hp => (hb g p hp).truth.positive),
    Value.use_built_mem _ _ hc (fun g p hp => (hb g p hp).truth.negative)⟩,
    Value.use_built_mem _ _ hc (fun g p hp => (hb g p hp).defined)⟩

/-- The four components of a partial translation, including original domain. -/
def component (p : Translation) : Option (Option Bool) → Formula
  | none => p.defined
  | some sign => Encoding.part p.truth sign

theorem component_built (h : Partial.Built p) (part : Option (Option Bool)) :
    (component p part).Built := by
  cases part with
  | none => exact h.defined
  | some sign => exact h.truth.part sign

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem partialMapM_meaning (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Result Translation) (result : Translation)
    (ha : Value.Built a)
    (bodies : ∀ g x body, (g, x) ∈ a.cases → f x = .ok body → Partial.Built body)
    (h : partialMapM a f = .ok result) (part : Option (Option Bool)) :
    (component result part).Holds s w τ e t ↔
      ∃ x body, Value.Meaning s w τ e t a x ∧ f x = .ok body ∧
        (component body part).Holds s w τ e t := by
  obtain ⟨choices, paired, rfl⟩ := partialMapM_cases a f result h
  have hc : Value.Built (Backend.Alloy.Behavioral.Full.Value.mk choices) := by
    intro g p hp
    obtain ⟨x, hx, _⟩ := (partial_cases_member f paired g p).mp hp
    exact ha g x hx
  have hb : ∀ g p, (g, p) ∈ choices → (component p part).Built := by
    intro g p hp
    obtain ⟨x, hx, he⟩ := (partial_cases_member f paired g p).mp hp
    exact component_built (bodies g x p hx he) part
  have same : component
      ⟨⟨(Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.raw),
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.positive),
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.truth.negative)⟩,
        (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => p.defined)⟩ part =
      (Backend.Alloy.Behavioral.Full.Value.mk choices).use (fun p => component p part) := by
    cases part with
    | none => rfl
    | some sign => cases sign with
      | none => rfl
      | some sign => cases sign <;> rfl
  rw [same, Value.use_meaning_mem _ _ hc hb]
  constructor
  · rintro ⟨p, ⟨g, hg, ht⟩, hp⟩
    obtain ⟨x, hx, he⟩ := (partial_cases_member f paired g p).mp hg
    exact ⟨x, p, ⟨g, hx, ht⟩, he, hp⟩
  · rintro ⟨x, p, ⟨g, hg, ht⟩, he, hp⟩
    exact ⟨p, ⟨g, (partial_cases_member f paired g p).mpr ⟨x, hg, he⟩, ht⟩, hp⟩

theorem partialMapM_total (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Result Translation) (result : Translation)
    (h : partialMapM a f = .ok result) (hx : Value.Meaning s w τ e t a x) :
    ∃ body, f x = .ok body := by
  obtain ⟨choices, paired, shape⟩ := partialMapM_cases a f result h
  clear shape
  obtain ⟨g, hg, _⟩ := hx
  have he : ∃ output ∈ choices, (g, x).1 = output.1 ∧ f (g, x).2 = .ok output.2 := by
    generalize heq : a.cases = inputs at paired hg
    clear heq
    induction paired with
    | nil => simp at hg
    | @cons input output inputs outputs head tail ih =>
      rcases List.mem_cons.mp hg with h | h
      · subst input; exact ⟨output, by simp, head⟩
      · obtain ⟨out, hout, hrel⟩ := ih h
        exact ⟨out, by simp [hout], hrel⟩
  obtain ⟨body, _, _, hb⟩ := he
  exact ⟨body.2, hb⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem partialMapM_observation {A D : Nat → Type} {C U : Type}
    {σ : Clafer.Behavioral.Trace C U} {O : Clafer.Behavioral.PartialObservation A D U}
    {ρ : Clafer.Behavioral.Environment U n} {source : Clafer.Behavioral.Formula A D n}
    (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Result Translation) (result : Translation)
    (ha : Value.Built a)
    (bodies : ∀ g x body, (g, x) ∈ a.cases → f x = .ok body → Partial.Built body)
    (h : partialMapM a f = .ok result)
    (complete : source.Defined σ O ρ t → ∃ x, Value.Meaning s w τ e t a x)
    (correct : ∀ x body, Value.Meaning s w τ e t a x → f x = .ok body →
      FormulaObservation s w τ e t σ O ρ source body) :
    FormulaObservation s w τ e t σ O ρ source result := by
  have choice (hd : source.Defined σ O ρ t) :
      ∃ x body, Value.Meaning s w τ e t a x ∧ f x = .ok body := by
    obtain ⟨x, hx⟩ := complete hd
    obtain ⟨body, hb⟩ := partialMapM_total a f result h hx
    exact ⟨x, body, hx, hb⟩
  refine ⟨partialMapM_built a f result ha bodies h, ?_, ?_, ?_, ?_⟩
  · rw [show result.defined = component result none from rfl, partialMapM_meaning a f result ha bodies h]
    constructor
    · rintro ⟨x, body, hx, hb, hdef⟩
      exact (correct x body hx hb).defined.mp hdef
    · intro hd
      obtain ⟨x, body, hx, hb⟩ := choice hd
      exact ⟨x, body, hx, hb, (correct x body hx hb).defined.mpr hd⟩
  · intro hd
    rw [show result.truth.raw = component result (some none) from rfl, partialMapM_meaning a f result ha bodies h]
    constructor
    · rintro ⟨x, body, hx, hb, hraw⟩
      exact ((correct x body hx hb).raw hd).mp hraw
    · intro hr
      obtain ⟨x, body, hx, hb⟩ := choice hd
      exact ⟨x, body, hx, hb, ((correct x body hx hb).raw hd).mpr hr⟩
  · intro hd
    rw [show result.truth.positive = component result (some (some true)) from rfl, partialMapM_meaning a f result ha bodies h]
    constructor
    · rintro ⟨x, body, hx, hb, hpos⟩
      exact ((correct x body hx hb).positive hd).mp hpos
    · intro hp
      obtain ⟨x, body, hx, hb⟩ := choice hd
      exact ⟨x, body, hx, hb, ((correct x body hx hb).positive hd).mpr hp⟩
  · intro hd
    rw [show result.truth.negative = component result (some (some false)) from rfl, partialMapM_meaning a f result ha bodies h]
    constructor
    · rintro ⟨x, body, hx, hb, hneg⟩
      exact ((correct x body hx hb).negative hd).mp hneg
    · intro hn
      obtain ⟨x, body, hx, hb⟩ := choice hd
      exact ⟨x, body, hx, hb, ((correct x body hx hb).negative hd).mpr hn⟩

end Expressions
end ClaferCompiler.Correctness.Behavioral.Full
