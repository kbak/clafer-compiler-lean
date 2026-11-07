module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionAggregates
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural

theorem observed_formula_raw {U : Type} {A D : Nat → Type}
    (m : Clafer.Behavioral.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (O : Clafer.Behavioral.Observation A D U) (a : Clafer.Behavioral.Formula A D n)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    a.raw (Clafer.Behavioral.Structural.observed m τ) O ρ t ↔ a.raw τ O ρ t := by
  induction a generalizing t <;>
    simp_all [Clafer.Behavioral.Formula.raw, Clafer.Behavioral.Lifetime.next,
      Clafer.Behavioral.Lifetime.eventually, Clafer.Behavioral.Lifetime.always,
      Clafer.Behavioral.Lifetime.strongUntil, Clafer.Behavioral.Lifetime.weakUntil,
      Clafer.Behavioral.Lifetime.Through, Clafer.Behavioral.Trace.ParentPresent,
      Clafer.Behavioral.Trace.Starts, Clafer.Behavioral.Trace.Ends, Clafer.Behavioral.Structural.observed]

theorem observed_formula_defined {U : Type} {A D : Nat → Type}
    (m : Clafer.Behavioral.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (O : Clafer.Behavioral.PartialObservation A D U) (a : Clafer.Behavioral.Formula A D n)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    a.Defined (Clafer.Behavioral.Structural.observed m τ) O ρ t ↔ a.Defined τ O ρ t := by
  induction a generalizing t <;>
    simp_all [Clafer.Behavioral.Formula.Defined, Clafer.Behavioral.Lifetime.Through,
      Clafer.Behavioral.Trace.ParentPresent,
      Clafer.Behavioral.Trace.Starts, Clafer.Behavioral.Trace.Ends, Clafer.Behavioral.Structural.observed]

theorem condition_observed {U : Type} (m : Clafer.Behavioral.Structural.Core k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (a : SemanticsBridge.Behavioral.Expression.Meaning U n)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    SemanticsBridge.Behavioral.Expression.condition (Clafer.Behavioral.Structural.observed m τ) a ρ t =
      SemanticsBridge.Behavioral.Expression.condition τ a ρ t := by
  classical
  unfold SemanticsBridge.Behavioral.Expression.condition
  simp only [observed_formula_defined, observed_formula_raw]

theorem count_observed {U : Type} (m : Clafer.Behavioral.Structural.Core k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (q : IR.Behavioral.Grouped.Count) (arity : Nat) (disjoint : Bool)
    (d : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n)
    (a : SemanticsBridge.Behavioral.Expression.Meaning U (n + arity))
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    SemanticsBridge.Behavioral.Expression.countObservation
      (Clafer.Behavioral.Structural.observed m τ) q arity disjoint d a ρ t =
      SemanticsBridge.Behavioral.Expression.countObservation τ q arity disjoint d a ρ t := by
  classical
  unfold SemanticsBridge.Behavioral.Expression.countObservation
  simp only [observed_formula_defined, observed_formula_raw]

theorem quantifier_image {A B : Type} (f : A ↪ B) (q : Clafer.Behavioral.Quantifier)
    (S : Set A) (a : A → Prop) (b : B → Prop) (agree : ∀ x ∈ S, b (f x) ↔ a x) :
    q.eval (f '' S) b ↔ q.eval S a := by
  classical
  cases q with
  | all =>
    exact ⟨fun hb x hx => (agree x hx).mp (hb _ ⟨x, hx, rfl⟩), by
      rintro ha _ ⟨x, hx, rfl⟩
      exact (agree x hx).mpr (ha x hx)⟩
  | some =>
    exact ⟨by rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩; exact ⟨x, hx, (agree x hx).mp hb⟩,
      by rintro ⟨x, hx, ha⟩; exact ⟨f x, ⟨x, hx, rfl⟩, (agree x hx).mpr ha⟩⟩
  | no =>
    apply not_congr
    exact ⟨by rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩; exact ⟨x, hx, (agree x hx).mp hb⟩,
      by rintro ⟨x, hx, ha⟩; exact ⟨f x, ⟨x, hx, rfl⟩, (agree x hx).mpr ha⟩⟩
  | one =>
    constructor
    · rintro ⟨_, ⟨⟨x, hx, rfl⟩, hb⟩, unique⟩
      refine ⟨x, ⟨hx, (agree x hx).mp hb⟩, ?_⟩
      rintro y ⟨hy, ha⟩
      exact f.injective (unique (f y) ⟨⟨y, hy, rfl⟩, (agree y hy).mpr ha⟩)
    · rintro ⟨x, ⟨hx, ha⟩, unique⟩
      refine ⟨f x, ⟨⟨x, hx, rfl⟩, (agree x hx).mpr ha⟩, ?_⟩
      rintro _ ⟨⟨y, hy, rfl⟩, hb⟩
      exact congrArg f (unique y ⟨hy, (agree y hy).mp hb⟩)
  | lone =>
    constructor
    · intro hb x hx y hy ha ha'
      exact f.injective (hb _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        ((agree x hx).mpr ha) ((agree y hy).mpr ha'))
    · rintro ha _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hb hb'
      exact congrArg f (ha x hx y hy ((agree x hx).mp hb) ((agree y hy).mp hb'))

def assignmentEmbedding {A B : Type} (f : A ↪ B) (arity : Nat) :
    (Fin arity → A) ↪ (Fin arity → B) where
  toFun a := f ∘ a
  inj' := by intro a b eq; funext i; exact f.injective (congrFun eq i)

theorem assignments_image {A B : Type} (f : A ↪ B) (arity : Nat) (disjoint : Bool) (S : Set A) :
    assignmentEmbedding f arity '' SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S =
      SemanticsBridge.Behavioral.Grouped.assignments arity disjoint (f '' S) := by
  classical
  ext b
  constructor
  · rintro ⟨a, ⟨ha, hd⟩, rfl⟩
    exact ⟨fun i => ⟨a i, ha i, rfl⟩, fun h => f.injective.comp (hd h)⟩
  · rintro ⟨hb, hd⟩
    choose a ha eq using hb
    refine ⟨a, ⟨ha, ?_⟩, funext eq⟩
    intro h i j he
    apply hd h
    exact (eq i).symm.trans ((congrArg f he).trans (eq j))

namespace ObservesCompletion
variable {U : Type} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}
  {objects : Fin o ↪ U}

theorem parentPresent_iff (h : ObservesCompletion v p l τ R objects) (x : Completion o) (t : Nat) :
    τ.ParentPresent (h.embedding x) t ↔ (completeTrace v p l).ParentPresent x t := by
  unfold Clafer.Behavioral.Trace.ParentPresent
  rw [← h.root_eq, h.embedding.injective.eq_iff, h.parent_eq]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro (root | ⟨_, ⟨y, hy, rfl⟩, live⟩)
    · exact Or.inl root
    · exact Or.inr ⟨y, hy, (h.live_iff t y).mp live⟩
  · rintro (root | ⟨y, hy, live⟩)
    · exact Or.inl root
    · exact Or.inr ⟨h.embedding y, ⟨y, hy, rfl⟩, (h.live_iff t y).mpr live⟩

theorem starts_iff (h : ObservesCompletion v p l τ R objects) (x : Completion o) (t : Nat) :
    τ.Starts t (h.embedding x) ↔ (completeTrace v p l).Starts t x := by
  simp only [Clafer.Behavioral.Trace.Starts, h.live_iff]

theorem ends_iff (h : ObservesCompletion v p l τ R objects) (x : Completion o) (t : Nat) :
    τ.Ends t (h.embedding x) ↔ (completeTrace v p l).Ends t x := by
  simp only [Clafer.Behavioral.Trace.Ends, h.live_iff]

theorem environment_extend (h : ObservesCompletion v p l τ R objects)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) (arity : Nat) (a : Fin arity → Completion o) :
    h.environment (SemanticsBridge.Behavioral.Grouped.extend ρ arity a) =
      SemanticsBridge.Behavioral.Grouped.extend (h.environment ρ) arity (h.embedding ∘ a) := by
  unfold environment SemanticsBridge.Behavioral.Grouped.extend
  congr 1
  funext i
  split <;> simp_all

@[simp] theorem environment_this (h : ObservesCompletion v p l τ R objects)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) :
    (h.environment ρ).this = h.embedding ρ.this := rfl

structure MeaningTransport (h : ObservesCompletion v p l τ R objects)
    (a : SemanticsBridge.Behavioral.Expression.Meaning (Completion o) n)
    (b : SemanticsBridge.Behavioral.Expression.Meaning U n) : Prop where
  defined : ∀ ρ t, b.Defined τ SemanticsBridge.Behavioral.Expression.observation (h.environment ρ) t ↔
    a.Defined (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation ρ t
  raw : ∀ ρ t, b.raw τ SemanticsBridge.Behavioral.Expression.observation.canonical (h.environment ρ) t ↔
    a.raw (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation.canonical ρ t
  denote : ∀ s ρ t,
    b.denote τ SemanticsBridge.Behavioral.Expression.observation.canonical s (h.environment ρ) t ↔
    a.denote (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation.canonical s ρ t

namespace MeaningTransport
open Clafer.Behavioral
variable {h : ObservesCompletion v p l τ R objects}
  {a b c : SemanticsBridge.Behavioral.Expression.Meaning (Completion o) n} {a' b' c' : SemanticsBridge.Behavioral.Expression.Meaning U n}

theorem truth : MeaningTransport (n := n) h .truth .truth := ⟨fun _ _ => Iff.rfl,
  fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem atom {a : SemanticsBridge.Behavioral.Expression.Observed (Completion o) Prop n} {b : SemanticsBridge.Behavioral.Expression.Observed U Prop n}
    (eq : ∀ ρ t, b (h.environment ρ) t = a ρ t) : MeaningTransport h (.atom a) (.atom b) := by
  constructor <;> intros <;>
    simp only [Formula.Defined, Formula.raw, Formula.denote, SemanticsBridge.Behavioral.Expression.observation,
      PartialObservation.canonical, PartialObservation.complete, eq]

theorem not (ha : MeaningTransport h a a') : MeaningTransport h (.not a) (.not a') :=
  ⟨ha.defined, fun ρ t => not_congr (ha.raw ρ t), fun s ρ t => ha.denote (!s) ρ t⟩

theorem and (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.and a b) (.and a' b') := by
  constructor
  · intro ρ t; exact and_congr (ha.defined ρ t) (hb.defined ρ t)
  · intro ρ t; exact and_congr (ha.raw ρ t) (hb.raw ρ t)
  · intro s ρ t; cases s <;> simp only [Formula.denote, ha.denote, hb.denote]

theorem or (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.or a b) (.or a' b') := by
  constructor
  · intro ρ t; exact and_congr (ha.defined ρ t) (hb.defined ρ t)
  · intro ρ t; exact or_congr (ha.raw ρ t) (hb.raw ρ t)
  · intro s ρ t; cases s <;> simp only [Formula.denote, ha.denote, hb.denote]

theorem implies (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.implies a b) (.implies a' b') := by
  constructor
  · intro ρ t; exact and_congr (ha.defined ρ t) (hb.defined ρ t)
  · intro ρ t; exact imp_congr (ha.raw ρ t) (hb.raw ρ t)
  · intro s ρ t; cases s <;> simp only [Formula.denote, ha.denote, hb.denote]

theorem iff (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.iff a b) (.iff a' b') := by
  constructor
  · intro ρ t; exact and_congr (ha.defined ρ t) (hb.defined ρ t)
  · intro ρ t; exact iff_congr (ha.raw ρ t) (hb.raw ρ t)
  · intro s ρ t; cases s <;> simp only [Formula.denote, ha.denote, hb.denote]

theorem xor (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.xor a b) (.xor a' b') := by
  constructor
  · intro ρ t; exact and_congr (ha.defined ρ t) (hb.defined ρ t)
  · intro ρ t; exact not_congr (iff_congr (ha.raw ρ t) (hb.raw ρ t))
  · intro s ρ t; cases s <;> simp only [Formula.denote, ha.denote, hb.denote]

theorem ite (hc : MeaningTransport h c c') (ha : MeaningTransport h a a')
    (hb : MeaningTransport h b b') : MeaningTransport h (.ite c a b) (.ite c' a' b') := by
  constructor
  · intro ρ t
    exact and_congr (hc.defined ρ t) (and_congr (ha.defined ρ t) (hb.defined ρ t))
  · intro ρ t
    exact and_congr (imp_congr (hc.raw ρ t) (ha.raw ρ t))
      (imp_congr (not_congr (hc.raw ρ t)) (hb.raw ρ t))
  · intro s ρ t; cases s <;> simp only [Formula.denote, hc.denote, ha.denote, hb.denote]

theorem next (ha : MeaningTransport h a a') : MeaningTransport h (.next a) (.next a') := by
  constructor
  · intro ρ t
    exact imp_congr (h.parentPresent_iff ρ.this _) (ha.defined ρ _)
  · intro ρ t
    exact imp_congr (h.parentPresent_iff ρ.this _) (ha.raw ρ _)
  · intro s ρ t
    exact imp_congr (h.parentPresent_iff ρ.this _) (ha.denote s ρ _)

theorem eventually (ha : MeaningTransport h a a') :
    MeaningTransport h (.eventually a) (.eventually a') := by
  constructor
  · intro ρ t
    simp only [Formula.Defined, Lifetime.Through, environment_this, h.parentPresent_iff, ha.defined]
  · intro ρ t
    simp only [Formula.raw, Lifetime.eventually, Lifetime.Through, environment_this,
      h.parentPresent_iff, ha.raw]
  · intro s ρ t
    cases s <;> simp only [Formula.denote, Lifetime.eventually, Lifetime.always,
      Lifetime.Through, environment_this, h.parentPresent_iff, ha.denote]

theorem always (ha : MeaningTransport h a a') :
    MeaningTransport h (.always a) (.always a') := by
  constructor
  · intro ρ t
    simp only [Formula.Defined, Lifetime.Through, environment_this, h.parentPresent_iff, ha.defined]
  · intro ρ t
    simp only [Formula.raw, Lifetime.always, Lifetime.Through, environment_this, h.parentPresent_iff, ha.raw]
  · intro s ρ t
    cases s <;> simp only [Formula.denote, Lifetime.eventually, Lifetime.always,
      Lifetime.Through, environment_this, h.parentPresent_iff, ha.denote]

theorem strongUntil (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.strongUntil a b) (.strongUntil a' b') := by
  constructor
  · intro ρ t
    simp only [Formula.Defined, Lifetime.Through, environment_this, h.parentPresent_iff, ha.defined, hb.defined]
  · intro ρ t
    simp only [Formula.raw, Lifetime.strongUntil, environment_this, h.parentPresent_iff, ha.raw, hb.raw]
  · intro s ρ t
    cases s <;> simp only [Formula.denote, Lifetime.strongUntil, Lifetime.weakUntil,
      Lifetime.always, Lifetime.Through, environment_this, h.parentPresent_iff, ha.denote, hb.denote]

theorem weakUntil (ha : MeaningTransport h a a') (hb : MeaningTransport h b b') :
    MeaningTransport h (.weakUntil a b) (.weakUntil a' b') := by
  constructor
  · intro ρ t
    simp only [Formula.Defined, Lifetime.Through, environment_this, h.parentPresent_iff, ha.defined, hb.defined]
  · intro ρ t
    simp only [Formula.raw, Lifetime.weakUntil, Lifetime.always, Lifetime.Through,
      Lifetime.strongUntil, environment_this, h.parentPresent_iff, ha.raw, hb.raw]
  · intro s ρ t
    cases s <;> simp only [Formula.denote, Lifetime.strongUntil, Lifetime.weakUntil,
      Lifetime.always, Lifetime.Through, environment_this, h.parentPresent_iff, ha.denote, hb.denote]

theorem initially (ha : MeaningTransport h a a') : MeaningTransport h (.initially a) (.initially a') :=
  ⟨fun ρ t => imp_congr (h.starts_iff ρ.this t) (ha.defined ρ t),
    fun ρ t => imp_congr (h.starts_iff ρ.this t) (ha.raw ρ t),
    fun s ρ t => imp_congr (h.starts_iff ρ.this t) (ha.denote s ρ t)⟩

theorem «finally» (ha : MeaningTransport h a a') : MeaningTransport h (.finally a) (.finally a') :=
  ⟨fun ρ t => imp_congr (h.ends_iff ρ.this t) (ha.defined ρ t),
    fun ρ t => imp_congr (h.ends_iff ρ.this t) (ha.raw ρ t),
    fun s ρ t => imp_congr (h.ends_iff ρ.this t) (ha.denote s ρ t)⟩

theorem condition (ha : MeaningTransport h a a') (ρ : Environment (Completion o) n) (t : Nat) :
    SemanticsBridge.Behavioral.Expression.condition τ a' (h.environment ρ) t = SemanticsBridge.Behavioral.Expression.condition (completeTrace v p l) a ρ t := by
  classical
  unfold SemanticsBridge.Behavioral.Expression.condition
  simp only [ha.defined, ha.raw]

theorem push_singleton (ρ : Environment (Completion o) n) (x : Completion o) :
    (h.environment ρ).push {h.embedding x} = h.environment (ρ.push {x}) := by
  rw [h.environment_push, Set.image_singleton]

theorem domain_canonical
    {d : SemanticsBridge.Behavioral.Expression.Observed (Completion o) (Set (Completion o)) n}
    {d' : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n}
    (hd : ∀ ρ t, d' (h.environment ρ) t = (d ρ t).map (Set.image h.embedding))
    (ρ : Environment (Completion o) n) (t : Nat) :
    SemanticsBridge.Behavioral.Expression.observation.canonical.domain d' (h.environment ρ) t =
      h.embedding '' SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t := by
  change (d' (h.environment ρ) t).getD ∅ = h.embedding '' (d ρ t).getD ∅
  rw [hd]
  cases d ρ t <;> simp

theorem quant {d : SemanticsBridge.Behavioral.Expression.Observed (Completion o) (Set (Completion o)) n}
    {d' : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n}
    {a : SemanticsBridge.Behavioral.Expression.Meaning (Completion o) (n + 1)}
    {a' : SemanticsBridge.Behavioral.Expression.Meaning U (n + 1)}
    (q : Quantifier)
    (hd : ∀ ρ t, d' (h.environment ρ) t = (d ρ t).map (Set.image h.embedding))
    (ha : MeaningTransport h a a') : MeaningTransport h (.quant q d a) (.quant q d' a') := by
  constructor
  · intro ρ t
    change (∃ S, d' (h.environment ρ) t = some S ∧ _) ↔ (∃ S, d ρ t = some S ∧ _)
    rw [hd]
    cases value : d ρ t with
    | none => simp
    | some S =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left']
      exact quantifier_image h.embedding .all S _ _ (fun x _ => by
        rw [push_singleton]
        exact ha.defined _ t)
  · intro ρ t
    simp only [Formula.raw, domain_canonical hd]
    exact quantifier_image h.embedding q _ _ _ (fun x _ => by
      rw [push_singleton]
      exact ha.raw _ t)
  · intro s ρ t
    have allImage (sign : Bool) :
        (∀ x ∈ h.embedding '' SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t,
          a'.denote τ SemanticsBridge.Behavioral.Expression.observation.canonical sign
            ((h.environment ρ).push {x}) t) ↔
        ∀ x ∈ SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t,
          a.denote (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation.canonical
            sign (ρ.push {x}) t :=
      quantifier_image h.embedding .all _ _ _ (fun x _ => by
        rw [push_singleton]
        exact ha.denote sign _ t)
    have someImage (sign : Bool) :
        (∃ x ∈ h.embedding '' SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t,
          a'.denote τ SemanticsBridge.Behavioral.Expression.observation.canonical sign
            ((h.environment ρ).push {x}) t) ↔
        ∃ x ∈ SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t,
          a.denote (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation.canonical
            sign (ρ.push {x}) t :=
      quantifier_image h.embedding .some _ _ _ (fun x _ => by
        rw [push_singleton]
        exact ha.denote sign _ t)
    have rawImage (q : Quantifier) :
        q.eval (h.embedding '' SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t)
          (fun x => a'.raw τ SemanticsBridge.Behavioral.Expression.observation.canonical
            ((h.environment ρ).push {x}) t) ↔
        q.eval (SemanticsBridge.Behavioral.Expression.observation.canonical.domain d ρ t)
          (fun x => a.raw (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation.canonical
            (ρ.push {x}) t) :=
      quantifier_image h.embedding q _ _ _ (fun x _ => by
        rw [push_singleton]
        exact ha.raw _ t)
    cases q with
    | all | some | no =>
      cases s <;> simp only [Formula.denote, domain_canonical hd, allImage, someImage]
    | one | lone =>
      simp only [Formula.denote, domain_canonical hd, polarity, rawImage]

theorem letSet {d : SemanticsBridge.Behavioral.Expression.Observed (Completion o) (Set (Completion o)) n}
    {d' : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n}
    {a : SemanticsBridge.Behavioral.Expression.Meaning (Completion o) (n + 1)}
    {a' : SemanticsBridge.Behavioral.Expression.Meaning U (n + 1)}
    (hd : ∀ ρ t, d' (h.environment ρ) t = (d ρ t).map (Set.image h.embedding))
    (ha : MeaningTransport h a a') : MeaningTransport h (.letSet d a) (.letSet d' a') := by
  constructor
  · intro ρ t
    change (∃ S, d' (h.environment ρ) t = some S ∧ _) ↔ (∃ S, d ρ t = some S ∧ _)
    rw [hd]
    cases value : d ρ t with
    | none => simp
    | some S =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left', ← h.environment_push]
      exact ha.defined _ t
  · intro ρ t
    simp only [Formula.raw, domain_canonical hd, ← h.environment_push]
    exact ha.raw _ t
  · intro s ρ t
    simp only [Formula.denote, domain_canonical hd, ← h.environment_push]
    exact ha.denote s _ t

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem count {d : SemanticsBridge.Behavioral.Expression.Observed (Completion o) (Set (Completion o)) n}
    {d' : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n}
    {a : SemanticsBridge.Behavioral.Expression.Meaning (Completion o) (n + arity)}
    {a' : SemanticsBridge.Behavioral.Expression.Meaning U (n + arity)}
    (q : IR.Behavioral.Grouped.Count) (disjoint : Bool)
    (hd : ∀ ρ t, d' (h.environment ρ) t = (d ρ t).map (Set.image h.embedding))
    (ha : MeaningTransport h a a') (ρ : Environment (Completion o) n) (t : Nat) :
    SemanticsBridge.Behavioral.Expression.countObservation τ q arity disjoint d' a'
      (h.environment ρ) t =
    SemanticsBridge.Behavioral.Expression.countObservation (completeTrace v p l) q arity disjoint d a ρ t := by
  classical
  unfold SemanticsBridge.Behavioral.Expression.countObservation
  rw [hd]
  cases value : d ρ t with
  | none => rfl
  | some S =>
    simp only [Option.map_some, Option.bind_some]
    have defined :
        (∀ assignment ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint (h.embedding '' S),
          a'.Defined τ SemanticsBridge.Behavioral.Expression.observation
            (SemanticsBridge.Behavioral.Grouped.extend (h.environment ρ) arity assignment) t) ↔
        ∀ assignment ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S,
          a.Defined (completeTrace v p l) SemanticsBridge.Behavioral.Expression.observation
            (SemanticsBridge.Behavioral.Grouped.extend ρ arity assignment) t := by
      rw [← assignments_image h.embedding]
      apply quantifier_image (assignmentEmbedding h.embedding arity) .all
      intro assignment _
      change a'.Defined _ _ (SemanticsBridge.Behavioral.Grouped.extend (h.environment ρ)
        arity (h.embedding ∘ assignment)) t ↔ _
      rw [← h.environment_extend]
      exact ha.defined _ t
    rw [defined]
    split
    · apply congrArg some
      apply propext
      rw [← assignments_image h.embedding]
      apply quantifier_image (assignmentEmbedding h.embedding arity)
      intro assignment _
      change a'.raw _ _ (SemanticsBridge.Behavioral.Grouped.extend (h.environment ρ)
        arity (h.embedding ∘ assignment)) t ↔ _
      rw [← h.environment_extend]
      exact ha.raw _ t
    · rfl

end MeaningTransport

end ObservesCompletion
end ClaferCompiler.Correctness.Behavioral.Full
