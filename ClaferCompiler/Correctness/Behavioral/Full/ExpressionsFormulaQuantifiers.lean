module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaMap

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Encoding

namespace Mixed
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {f : U → Atom} {D : Set U} {r d : Rel} {a b p : Formula}

theorem all_unary (hp : p.Built) (hr : Unary f D (r.eval s w τ e t)) :
    (Formula.all r p).Holds s w τ e t ↔ ∀ x ∈ D, p.Holds s w τ (f x :: e) t := by
  rw [holds_all hp]
  constructor
  · intro h x hx; exact h _ ((hr _).mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, he⟩ := (hr _).mp hy
    have he' : y = f x := by simpa using he
    subst y
    exact h x hx

theorem exists_unary (hp : p.Built) (hr : Unary f D (r.eval s w τ e t)) :
    (Formula.exists_ r p).Holds s w τ e t ↔ ∃ x ∈ D, p.Holds s w τ (f x :: e) t := by
  rw [holds_exists hp]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, hx, he⟩ := (hr _).mp hy
    have he' : y = f x := by simpa using he
    subst y
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨_, (hr _).mpr ⟨x, hx, rfl⟩, h⟩

theorem equal_variables (hf : Function.Injective f) (x y : U) :
    (Formula.equal (.var 0) (.var 1)).Holds s w τ (f y :: f x :: e) t ↔ y = x := by
  have h : Unary f {y} ((Rel.var 0).eval s w τ (f y :: f x :: e) t) := unary_singleton y
  have h' : Unary f {x} ((Rel.var 1).eval s w τ (f y :: f x :: e) t) := unary_singleton x
  exact (unary_equal hf h h').trans (by simp)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem unique_meaning (hf : Function.Injective f) (hd : d.Term)
    (hD : Unary f D (d.eval s w τ e t)) (ha : a.Built)
    (P : U → Prop)
    (hP : ∀ x ∈ D, ∀ y ∈ D, a.Holds s w τ (f y :: f x :: e) t ↔ P y)
    (x : U) (hx : x ∈ D) :
    (Formula.all (Backend.Alloy.Behavioral.shift 1 d) (.binary .implies a (.equal (.var 0) (.var 1)))).Holds
      s w τ (f x :: e) t ↔ ∀ y ∈ D, P y → y = x := by
  have hD' : Unary f D ((Backend.Alloy.Behavioral.shift 1 d).eval s w τ (f x :: e) t) := by
    rw [show (1 : Nat) = ([f x] : Environment).length from rfl,
      show f x :: e = [f x] ++ e from rfl, shift_eval hd]
    exact hD
  rw [all_unary (.binary .implies ha (.equal _ _)) hD']
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro hy
  rw [holds_implies ha (.equal _ _), hP x hx y hy, equal_variables hf]

theorem one_meaning (hf : Function.Injective f) (hd : d.Term)
    (hD : Unary f D (d.eval s w τ e t)) (ha : a.Built) (hb : b.Built)
    (P : U → Prop)
    (hP : ∀ x ∈ D, a.Holds s w τ (f x :: e) t ↔ P x)
    (hQ : ∀ x ∈ D, ∀ y ∈ D, b.Holds s w τ (f y :: f x :: e) t ↔ P y) :
    (Formula.exists_ d (.binary .conj a (.all (Backend.Alloy.Behavioral.shift 1 d)
      (.binary .implies b (.equal (.var 0) (.var 1)))))).Holds s w τ e t ↔
      Clafer.Behavioral.Quantifier.one.eval D P := by
  rw [exists_unary (.binary .conj ha (.all _ (.binary .implies hb (.equal _ _)))) hD]
  have step : ∀ x ∈ D, (a.Holds s w τ (f x :: e) t ∧
      (Formula.all (Backend.Alloy.Behavioral.shift 1 d) (.binary .implies b (.equal (.var 0) (.var 1)))).Holds s w τ (f x :: e) t) ↔
      P x ∧ ∀ y ∈ D, P y → y = x := by
    intro x hx
    rw [hP x hx, unique_meaning hf hd hD hb P hQ x hx]
  simp only [holds_and ha (.all _ (.binary .implies hb (.equal _ _)))]
  have h := exists_congr (fun x => and_congr_right (step x))
  apply h.trans
  simp only [Clafer.Behavioral.Quantifier.eval, ExistsUnique]
  aesop

theorem lone_meaning (hf : Function.Injective f) (hd : d.Term)
    (hD : Unary f D (d.eval s w τ e t)) (ha : a.Built) (hb : b.Built)
    (P : U → Prop)
    (hP : ∀ x ∈ D, a.Holds s w τ (f x :: e) t ↔ P x)
    (hQ : ∀ x ∈ D, ∀ y ∈ D, b.Holds s w τ (f y :: f x :: e) t ↔ P y) :
    (Formula.all d (.binary .implies a (.all (Backend.Alloy.Behavioral.shift 1 d)
      (.binary .implies b (.equal (.var 0) (.var 1)))))).Holds s w τ e t ↔
      Clafer.Behavioral.Quantifier.lone.eval D P := by
  rw [all_unary (.binary .implies ha (.all _ (.binary .implies hb (.equal _ _)))) hD]
  simp only [holds_implies ha (.all _ (.binary .implies hb (.equal _ _)))]
  have step : ∀ x ∈ D, (a.Holds s w τ (f x :: e) t →
      (Formula.all (Backend.Alloy.Behavioral.shift 1 d) (.binary .implies b (.equal (.var 0) (.var 1)))).Holds s w τ (f x :: e) t) ↔
      P x → ∀ y ∈ D, P y → y = x := by
    intro x hx
    rw [hP x hx, unique_meaning hf hd hD hb P hQ x hx]
  have h := forall_congr' (fun x => imp_congr_right (step x))
  apply h.trans
  simp only [Clafer.Behavioral.Quantifier.eval]
  aesop

end Mixed
namespace FormulaObservation
variable {A D : Nat → Type} {C U : Type} {s : Schema} {w : Nat} {τ : Trace}
  {e : Environment} {t : Nat} {σ : Clafer.Behavioral.Trace C U}
  {O : Clafer.Behavioral.PartialObservation A D U} {ρ : Clafer.Behavioral.Environment U n}
  {a : Clafer.Behavioral.Formula A D (n + 1)} {d : D n} {S : Set U} {f : U → Atom}
  {domain : Rel} {one two : Backend.Alloy.Behavioral.Partial.Translation}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem quantify (q : IR.Behavioral.Quantifier) (hf : Function.Injective f)
    (term : domain.Term) (rows : Mixed.Unary f S (domain.eval s w τ e t))
    (source : O.domain d ρ t = some S) (ho : Partial.Built one) (ht : Partial.Built two)
    (first : ∀ x ∈ S, FormulaObservation s w τ (f x :: e) t σ O (ρ.push {x}) a one)
    (second : ∀ x ∈ S, ∀ y ∈ S,
      FormulaObservation s w τ (f y :: f x :: e) t σ O (ρ.push {y}) a two) :
    FormulaObservation s w τ e t σ O ρ (.quant (SemanticsBridge.Behavioral.quantifier q) d a)
      (Backend.Alloy.Behavioral.Partial.quantify q domain .truth one two) := by
  have canon : O.canonical.domain d ρ t = S := by
    simp [Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete, source]
  have original : (Clafer.Behavioral.Formula.quant (SemanticsBridge.Behavioral.quantifier q) d a).Defined σ O ρ t ↔
      ∀ x ∈ S, a.Defined σ O (ρ.push {x}) t := by
    simp [Clafer.Behavioral.Formula.Defined, source]
  have hb : Partial.Built (Backend.Alloy.Behavioral.Partial.quantify q domain .truth one two) := by
    refine ⟨?_, .binary .conj .truth (.all domain ho.defined)⟩
    cases q with
    | all => exact ⟨.all _ ho.truth.raw, .all _ ho.truth.positive, .exists_ _ ho.truth.negative⟩
    | some => exact ⟨.exists_ _ ho.truth.raw, .exists_ _ ho.truth.positive, .all _ ho.truth.negative⟩
    | no => exact ⟨.all _ (.unary .neg ho.truth.raw), .all _ ho.truth.negative, .exists_ _ ho.truth.positive⟩
    | one => exact atomic_built (.exists_ _ (.binary .conj ho.truth.raw (.all _ (.binary .implies ht.truth.raw (.equal _ _)))))
    | lone => exact atomic_built (.all _ (.binary .implies ho.truth.raw (.all _ (.binary .implies ht.truth.raw (.equal _ _)))))
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · rw [Partial.quantify_domain q domain .truth .truth one two ho, holds_truth, true_and,
      ← holds_all ho.defined, Mixed.all_unary ho.defined rows, original]
    exact forall_congr' (fun x => imp_congr_right (fun hx => (first x hx).defined))
  · intro hd
    have hd := original.mp hd
    have hr : ∀ x ∈ S, one.truth.raw.Holds s w τ (f x :: e) t ↔ a.raw σ O.canonical (ρ.push {x}) t :=
      fun x hx => (first x hx).raw (hd x hx)
    have hp : ∀ x ∈ S, one.truth.positive.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical true (ρ.push {x}) t :=
      fun x hx => (first x hx).positive (hd x hx)
    have hn : ∀ x ∈ S, one.truth.negative.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical false (ρ.push {x}) t :=
      fun x hx => (first x hx).negative (hd x hx)
    have hr₂ : ∀ x ∈ S, ∀ y ∈ S, two.truth.raw.Holds s w τ (f y :: f x :: e) t ↔ a.raw σ O.canonical (ρ.push {y}) t :=
      fun x hx y hy => (second x hx y hy).raw (hd y hy)
    cases q with
    | all =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.raw, canon]
      rw [Mixed.all_unary ho.truth.raw rows]
      exact forall_congr' (fun x => imp_congr_right (hr x))
    | some =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.raw, canon]
      rw [Mixed.exists_unary ho.truth.raw rows]
      exact exists_congr (fun x => and_congr_right (hr x))
    | no =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.raw, canon]
      rw [Mixed.all_unary (.unary .neg ho.truth.raw) rows]
      simp only [holds_neg ho.truth.raw]
      constructor
      · intro h ⟨x, hx, hxraw⟩; exact h x hx ((hr x hx).mpr hxraw)
      · intro h x hx hxraw; exact h ⟨x, hx, (hr x hx).mp hxraw⟩
    | one =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.raw, canon]
      exact Mixed.one_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂
    | lone =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.raw, canon]
      exact Mixed.lone_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂
  · intro hd
    have hd := original.mp hd
    have hr : ∀ x ∈ S, one.truth.raw.Holds s w τ (f x :: e) t ↔ a.raw σ O.canonical (ρ.push {x}) t :=
      fun x hx => (first x hx).raw (hd x hx)
    have hp : ∀ x ∈ S, one.truth.positive.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical true (ρ.push {x}) t :=
      fun x hx => (first x hx).positive (hd x hx)
    have hn : ∀ x ∈ S, one.truth.negative.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical false (ρ.push {x}) t :=
      fun x hx => (first x hx).negative (hd x hx)
    have hr₂ : ∀ x ∈ S, ∀ y ∈ S, two.truth.raw.Holds s w τ (f y :: f x :: e) t ↔ a.raw σ O.canonical (ρ.push {y}) t :=
      fun x hx y hy => (second x hx y hy).raw (hd y hy)
    cases q with
    | all =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.all_unary ho.truth.positive rows]
      exact forall_congr' (fun x => imp_congr_right (hp x))
    | some =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.exists_unary ho.truth.positive rows]
      exact exists_congr (fun x => and_congr_right (hp x))
    | no =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.all_unary ho.truth.negative rows]
      exact forall_congr' (fun x => imp_congr_right (hn x))
    | one =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      exact Mixed.one_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂
    | lone =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      exact Mixed.lone_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂
  · intro hd
    have hd := original.mp hd
    have hr : ∀ x ∈ S, one.truth.raw.Holds s w τ (f x :: e) t ↔ a.raw σ O.canonical (ρ.push {x}) t :=
      fun x hx => (first x hx).raw (hd x hx)
    have hp : ∀ x ∈ S, one.truth.positive.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical true (ρ.push {x}) t :=
      fun x hx => (first x hx).positive (hd x hx)
    have hn : ∀ x ∈ S, one.truth.negative.Holds s w τ (f x :: e) t ↔ a.denote σ O.canonical false (ρ.push {x}) t :=
      fun x hx => (first x hx).negative (hd x hx)
    have hr₂ : ∀ x ∈ S, ∀ y ∈ S, two.truth.raw.Holds s w τ (f y :: f x :: e) t ↔ a.raw σ O.canonical (ρ.push {y}) t :=
      fun x hx y hy => (second x hx y hy).raw (hd y hy)
    cases q with
    | all =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.exists_unary ho.truth.negative rows]
      exact exists_congr (fun x => and_congr_right (hn x))
    | some =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.all_unary ho.truth.negative rows]
      exact forall_congr' (fun x => imp_congr_right (hn x))
    | no =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      rw [Mixed.exists_unary ho.truth.positive rows]
      exact exists_congr (fun x => and_congr_right (hp x))
    | one =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      exact (holds_neg (.exists_ _ (.binary .conj ho.truth.raw (.all _ (.binary .implies ht.truth.raw (.equal _ _)))))).trans (not_congr (Mixed.one_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂))
    | lone =>
      simp only [Backend.Alloy.Behavioral.Partial.quantify, SemanticsBridge.Behavioral.quantifier,
        Clafer.Behavioral.Formula.denote, canon]
      exact (holds_neg (.all _ (.binary .implies ho.truth.raw (.all _ (.binary .implies ht.truth.raw (.equal _ _)))))).trans (not_congr (Mixed.lone_meaning hf term rows ho.truth.raw ht.truth.raw _ hr hr₂))

end FormulaObservation

end ClaferCompiler.Correctness.Behavioral.Full
