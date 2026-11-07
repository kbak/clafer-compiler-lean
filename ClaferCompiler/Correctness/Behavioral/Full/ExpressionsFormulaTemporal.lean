module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormula

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.FormulaObservation
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Partial
open Encoding
variable {A D : Nat → Type} {C U : Type} {s : Schema} {w : Nat} {τ : Trace}
  {e : Environment} {t : Nat} {σ : Clafer.Behavioral.Trace C U}
  {O : Clafer.Behavioral.PartialObservation A D U} {ρ : Clafer.Behavioral.Environment U n}
  {a b : Clafer.Behavioral.Formula A D n} {x y : Translation} {p : Formula}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem next (ha : ∀ j, FormulaObservation s w τ e j σ O ρ a x)
    (hp : p.Built) (parent : ∀ j, p.Holds s w τ e j ↔ σ.ParentPresent ρ.this j) :
    FormulaObservation s w τ e t σ O ρ (.next a) (next p x) := by
  refine ⟨Partial.next_built hp (ha t).built, ?_, ?_, ?_, ?_⟩
  · rw [Partial.next_domain hp (ha t).built, parent, (ha (t + 1)).defined]
    rfl
  · intro hd
    change (Backend.Alloy.Behavioral.next p x.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.next_meaning s w τ e p x.truth.raw hp (ha t).built.truth.raw t]
    change (p.Holds s w τ e (t + 1) → _) ↔ (σ.ParentPresent ρ.this (t + 1) → _)
    rw [parent]
    exact imp_congr_right (fun h => (ha (t + 1)).raw (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.next p x.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.next_meaning s w τ e p x.truth.positive hp (ha t).built.truth.positive t]
    change (p.Holds s w τ e (t + 1) → _) ↔ (σ.ParentPresent ρ.this (t + 1) → _)
    rw [parent]
    exact imp_congr_right (fun h => (ha (t + 1)).positive (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.next p x.truth.negative).Holds s w τ e t ↔ _
    rw [Encoding.next_meaning s w τ e p x.truth.negative hp (ha t).built.truth.negative t]
    change (p.Holds s w τ e (t + 1) → _) ↔ (σ.ParentPresent ρ.this (t + 1) → _)
    rw [parent]
    exact imp_congr_right (fun h => (ha (t + 1)).negative (hd h))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem eventually (ha : ∀ j, FormulaObservation s w τ e j σ O ρ a x)
    (hp : p.Built) (parent : ∀ j, p.Holds s w τ e j ↔ σ.ParentPresent ρ.this j) :
    FormulaObservation s w τ e t σ O ρ (.eventually a) (eventually p x) := by
  have he : (fun j => p.Holds s w τ e j) = σ.ParentPresent ρ.this :=
    funext (fun j => propext (parent j))
  refine ⟨Partial.eventually_built hp (ha t).built, ?_, ?_, ?_, ?_⟩
  · rw [Partial.eventually_domain hp (ha t).built, he]
    exact forall_congr' (fun j => imp_congr_right (fun _ => imp_congr_right (fun _ => (ha j).defined)))
  · intro hd
    change (Backend.Alloy.Behavioral.eventually p x.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.eventually_meaning s w τ e p x.truth.raw hp (ha t).built.truth.raw t, he]
    exact Clafer.Behavioral.Lifetime.eventually_congr (fun j hj hthrough => (ha j).raw (hd j hj hthrough))
  · intro hd
    change (Backend.Alloy.Behavioral.eventually p x.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.eventually_meaning s w τ e p x.truth.positive hp (ha t).built.truth.positive t, he]
    exact Clafer.Behavioral.Lifetime.eventually_congr (fun j hj hthrough => (ha j).positive (hd j hj hthrough))
  · intro hd
    change (Backend.Alloy.Behavioral.always p x.truth.negative).Holds s w τ e t ↔ _
    rw [Encoding.always_meaning s w τ e p x.truth.negative hp (ha t).built.truth.negative t, he]
    exact Clafer.Behavioral.Lifetime.always_congr (fun j hj hthrough => (ha j).negative (hd j hj hthrough))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem always (ha : ∀ j, FormulaObservation s w τ e j σ O ρ a x)
    (hp : p.Built) (parent : ∀ j, p.Holds s w τ e j ↔ σ.ParentPresent ρ.this j) :
    FormulaObservation s w τ e t σ O ρ (.always a) (always p x) := by
  have he : (fun j => p.Holds s w τ e j) = σ.ParentPresent ρ.this :=
    funext (fun j => propext (parent j))
  refine ⟨Partial.always_built hp (ha t).built, ?_, ?_, ?_, ?_⟩
  · rw [Partial.always_domain hp (ha t).built, he]
    exact forall_congr' (fun j => imp_congr_right (fun _ => imp_congr_right (fun _ => (ha j).defined)))
  · intro hd
    change (Backend.Alloy.Behavioral.always p x.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.always_meaning s w τ e p x.truth.raw hp (ha t).built.truth.raw t, he]
    exact Clafer.Behavioral.Lifetime.always_congr (fun j hj hthrough => (ha j).raw (hd j hj hthrough))
  · intro hd
    change (Backend.Alloy.Behavioral.always p x.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.always_meaning s w τ e p x.truth.positive hp (ha t).built.truth.positive t, he]
    exact Clafer.Behavioral.Lifetime.always_congr (fun j hj hthrough => (ha j).positive (hd j hj hthrough))
  · intro hd
    change (Backend.Alloy.Behavioral.eventually p x.truth.negative).Holds s w τ e t ↔ _
    rw [Encoding.eventually_meaning s w τ e p x.truth.negative hp (ha t).built.truth.negative t, he]
    exact Clafer.Behavioral.Lifetime.eventually_congr (fun j hj hthrough => (ha j).negative (hd j hj hthrough))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem strongUntil (ha : ∀ j, FormulaObservation s w τ e j σ O ρ a x)
    (hb : ∀ j, FormulaObservation s w τ e j σ O ρ b y)
    (hp : p.Built) (parent : ∀ j, p.Holds s w τ e j ↔ σ.ParentPresent ρ.this j) :
    FormulaObservation s w τ e t σ O ρ (.strongUntil a b) (strongUntil p x y) := by
  have he : (fun j => p.Holds s w τ e j) = σ.ParentPresent ρ.this :=
    funext (fun j => propext (parent j))
  have hx := (ha t).built
  have hy := (hb t).built
  refine ⟨⟨⟨Encoding.until_built hp hx.truth.raw hy.truth.raw,
    Encoding.until_built hp hx.truth.positive hy.truth.positive,
    Encoding.weakUntil_built hp hy.truth.negative (.binary .conj hx.truth.negative hy.truth.negative)⟩,
    Partial.totalAlways_built hp (.binary .conj hx.defined hy.defined)⟩, ?_, ?_, ?_, ?_⟩
  · rw [Partial.strongUntil_domain hp hx hy, he]
    exact forall_congr' (fun j => imp_congr_right (fun _ => imp_congr_right (fun _ =>
      and_congr (ha j).defined (hb j).defined)))
  · intro hd
    change (Backend.Alloy.Behavioral.strongUntil p x.truth.raw y.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.until_meaning s w τ e p x.truth.raw y.truth.raw hp hx.truth.raw hy.truth.raw t, he]
    exact Clafer.Behavioral.Lifetime.until_congr
      (fun j hj ht => (ha j).raw (hd j hj ht).1)
      (fun j hj ht => (hb j).raw (hd j hj ht).2)
  · intro hd
    change (Backend.Alloy.Behavioral.strongUntil p x.truth.positive y.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.until_meaning s w τ e p x.truth.positive y.truth.positive hp hx.truth.positive hy.truth.positive t, he]
    exact Clafer.Behavioral.Lifetime.until_congr
      (fun j hj ht => (ha j).positive (hd j hj ht).1)
      (fun j hj ht => (hb j).positive (hd j hj ht).2)
  · intro hd
    change (Backend.Alloy.Behavioral.weakUntil p y.truth.negative
      (.binary .conj x.truth.negative y.truth.negative)).Holds s w τ e t ↔ _
    rw [Encoding.weakUntil_meaning s w τ e p y.truth.negative
      (.binary .conj x.truth.negative y.truth.negative) hp hy.truth.negative
      (.binary .conj hx.truth.negative hy.truth.negative) t, he]
    apply Clafer.Behavioral.Lifetime.weakUntil_congr
    · exact fun j hj ht => (hb j).negative (hd j hj ht).2
    · intro j hj ht
      exact (holds_and hx.truth.negative hy.truth.negative).trans
        (and_congr ((ha j).negative (hd j hj ht).1) ((hb j).negative (hd j hj ht).2))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem weakUntil (ha : ∀ j, FormulaObservation s w τ e j σ O ρ a x)
    (hb : ∀ j, FormulaObservation s w τ e j σ O ρ b y)
    (hp : p.Built) (parent : ∀ j, p.Holds s w τ e j ↔ σ.ParentPresent ρ.this j) :
    FormulaObservation s w τ e t σ O ρ (.weakUntil a b) (weakUntil p x y) := by
  have he : (fun j => p.Holds s w τ e j) = σ.ParentPresent ρ.this :=
    funext (fun j => propext (parent j))
  have hx := (ha t).built
  have hy := (hb t).built
  refine ⟨⟨⟨Encoding.weakUntil_built hp hx.truth.raw hy.truth.raw,
    Encoding.weakUntil_built hp hx.truth.positive hy.truth.positive,
    Encoding.until_built hp hy.truth.negative (.binary .conj hx.truth.negative hy.truth.negative)⟩,
    Partial.totalAlways_built hp (.binary .conj hx.defined hy.defined)⟩, ?_, ?_, ?_, ?_⟩
  · rw [Partial.weakUntil_domain hp hx hy, he]
    exact forall_congr' (fun j => imp_congr_right (fun _ => imp_congr_right (fun _ =>
      and_congr (ha j).defined (hb j).defined)))
  · intro hd
    change (Backend.Alloy.Behavioral.weakUntil p x.truth.raw y.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.weakUntil_meaning s w τ e p x.truth.raw y.truth.raw hp hx.truth.raw hy.truth.raw t, he]
    exact Clafer.Behavioral.Lifetime.weakUntil_congr
      (fun j hj ht => (ha j).raw (hd j hj ht).1)
      (fun j hj ht => (hb j).raw (hd j hj ht).2)
  · intro hd
    change (Backend.Alloy.Behavioral.weakUntil p x.truth.positive y.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.weakUntil_meaning s w τ e p x.truth.positive y.truth.positive hp hx.truth.positive hy.truth.positive t, he]
    exact Clafer.Behavioral.Lifetime.weakUntil_congr
      (fun j hj ht => (ha j).positive (hd j hj ht).1)
      (fun j hj ht => (hb j).positive (hd j hj ht).2)
  · intro hd
    change (Backend.Alloy.Behavioral.strongUntil p y.truth.negative
      (.binary .conj x.truth.negative y.truth.negative)).Holds s w τ e t ↔ _
    rw [Encoding.until_meaning s w τ e p y.truth.negative
      (.binary .conj x.truth.negative y.truth.negative) hp hy.truth.negative
      (.binary .conj hx.truth.negative hy.truth.negative) t, he]
    apply Clafer.Behavioral.Lifetime.until_congr
    · exact fun j hj ht => (hb j).negative (hd j hj ht).2
    · intro j hj ht
      exact (holds_and hx.truth.negative hy.truth.negative).trans
        (and_congr ((ha j).negative (hd j hj ht).1) ((hb j).negative (hd j hj ht).2))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem initially (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hp : p.Built) (present : ∀ j, p.Holds s w τ e j ↔ ρ.this ∈ σ.live j) :
    FormulaObservation s w τ e t σ O ρ (.initially a) (initially p x) := by
  have hanchor : (p.Holds s w τ e t ∧ (t = 0 ∨ ∃ j, t = j + 1 ∧ ¬ p.Holds s w τ e j)) ↔ σ.Starts t ρ.this := by
    simp only [Clafer.Behavioral.Trace.Starts, present]
  refine ⟨⟨⟨Encoding.initially_built hp ha.built.truth.raw,
    Encoding.initially_built hp ha.built.truth.positive, Encoding.initially_built hp ha.built.truth.negative⟩,
    Encoding.initially_built hp ha.built.defined⟩, ?_, ?_, ?_, ?_⟩
  · rw [Partial.initially_domain hp ha.built, hanchor, ha.defined]
    rfl
  · intro hd
    change (Backend.Alloy.Behavioral.initially p x.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.initially_meaning s w τ e p x.truth.raw hp ha.built.truth.raw t, hanchor]
    exact imp_congr_right (fun h => ha.raw (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.initially p x.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.initially_meaning s w τ e p x.truth.positive hp ha.built.truth.positive t, hanchor]
    exact imp_congr_right (fun h => ha.positive (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.initially p x.truth.negative).Holds s w τ e t ↔ _
    rw [Encoding.initially_meaning s w τ e p x.truth.negative hp ha.built.truth.negative t, hanchor]
    exact imp_congr_right (fun h => ha.negative (hd h))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem «finally» (ha : FormulaObservation s w τ e t σ O ρ a x)
    (hp : p.Built) (present : ∀ j, p.Holds s w τ e j ↔ ρ.this ∈ σ.live j) :
    FormulaObservation s w τ e t σ O ρ (.«finally» a) («finally» p x) := by
  have hanchor : (p.Holds s w τ e t ∧ ¬ p.Holds s w τ e (t + 1)) ↔ σ.Ends t ρ.this := by
    simp only [Clafer.Behavioral.Trace.Ends, present]
  refine ⟨⟨⟨Encoding.atEnd_built hp ha.built.truth.raw,
    Encoding.atEnd_built hp ha.built.truth.positive, Encoding.atEnd_built hp ha.built.truth.negative⟩,
    Encoding.atEnd_built hp ha.built.defined⟩, ?_, ?_, ?_, ?_⟩
  · rw [Partial.finally_domain hp ha.built, hanchor, ha.defined]
    rfl
  · intro hd
    change (Backend.Alloy.Behavioral.atEnd p x.truth.raw).Holds s w τ e t ↔ _
    rw [Encoding.atEnd_meaning s w τ e p x.truth.raw hp ha.built.truth.raw t, hanchor]
    exact imp_congr_right (fun h => ha.raw (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.atEnd p x.truth.positive).Holds s w τ e t ↔ _
    rw [Encoding.atEnd_meaning s w τ e p x.truth.positive hp ha.built.truth.positive t, hanchor]
    exact imp_congr_right (fun h => ha.positive (hd h))
  · intro hd
    change (Backend.Alloy.Behavioral.atEnd p x.truth.negative).Holds s w τ e t ↔ _
    rw [Encoding.atEnd_meaning s w τ e p x.truth.negative hp ha.built.truth.negative t, hanchor]
    exact imp_congr_right (fun h => ha.negative (hd h))

end ClaferCompiler.Correctness.Behavioral.Full.FormulaObservation
