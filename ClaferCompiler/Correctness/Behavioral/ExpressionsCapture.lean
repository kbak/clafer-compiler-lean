module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
variable {U : Type}

namespace Encoding

def part (a : Translation) : Option Bool → Formula
  | none => a.raw
  | some true => a.positive
  | some false => a.negative

theorem Built.part (h : Built a) (p : Option Bool) : (part a p).Built := by
  cases p with
  | none => exact h.raw
  | some p => cases p with
    | false => exact h.negative
    | true => exact h.positive

theorem freezeChoice_meaning (hg : g.Built) (ha : Built a) (hb : Built b) (p : Option Bool) :
    (part (freezeChoice g a b) p).Holds s w τ e t ↔
      (g.Holds s w τ e t ∧ (part a p).Holds s w τ e t) ∨
        (¬ g.Holds s w τ e t ∧ (part b p).Holds s w τ e t) := by
  have h (x y : Formula) (hx : x.Built) (hy : y.Built) :
      (Formula.binary .disj (.binary .conj g x) (.binary .conj (.unary .neg g) y)).Holds s w τ e t ↔
        (g.Holds s w τ e t ∧ x.Holds s w τ e t) ∨ (¬ g.Holds s w τ e t ∧ y.Holds s w τ e t) := by
    rw [holds_or (.binary .conj hg hx) (.binary .conj (.unary .neg hg) hy),
      holds_and hg hx, holds_and (.unary .neg hg) hy, holds_neg hg]
  cases p with
  | none => exact h _ _ ha.raw hb.raw
  | some p => cases p with
    | false => exact h _ _ ha.negative hb.negative
    | true => exact h _ _ ha.positive hb.positive

end Encoding

theorem Frozen.unique (hf : Function.Injective f)
    (ha : Frozen v w τ f e r A) (hb : Frozen v w τ f e r B) : A = B :=
  (Relations.unary_equal hf (ha.2 0) (hb.2 0)).mp (fun _ => Iff.rfl)

theorem Frozen.union (ha : Frozen v w τ f e a A) (hb : Frozen v w τ f e b B) :
    Frozen v w τ f e (a.union b) (A ∪ B) :=
  ⟨.union ha.1 hb.1, fun t => Relations.unary_union ha.1 hb.1 (ha.2 t) (hb.2 t)⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- Guards observe membership only at the capture time. Each selected atom is
frozen over the whole trace, so the continuation observes the captured set even
when its current live extent later differs. Duplicate aliases are harmless. -/
theorem freezeFrom_meaning (v : IR.Structural.Layout k) (w : Nat) (τ : Trace)
    (f : U → Nat) (hf : Function.Injective f) (e : Environment) (t : Nat)
    (aliases : List Rel) (value captured : Rel) (D A : Set U)
    (hv : Relations.Unary f D (value.eval (schema v) w τ e t))
    (ha : Frozen v w τ f e captured A)
    (inside : A ⊆ D)
    (hs : ∀ r ∈ aliases, ∃ x, Frozen v w τ f e r {x})
    (cover : ∀ x ∈ D, x ∈ A ∨ ∃ r ∈ aliases, Frozen v w τ f e r {x})
    (body : Rel → Translation) (hb : ∀ r, Encoding.Built (body r))
    (P : Set U → Prop) (p : Option Bool)
    (correct : ∀ r S, (_ : Frozen v w τ f e r S) → (
      (Encoding.part (body r) p).Holds (schema v) w τ e t ↔ P S)) :
    (Encoding.part (freezeFrom aliases value body captured) p).Holds (schema v) w τ e t ↔ P D := by
  classical
  induction aliases generalizing captured A with
  | nil =>
    have he : A = D := Set.Subset.antisymm inside (fun x hx => by simpa using cover x hx)
    subst A
    exact correct captured D ha
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := hs x (by simp)
    have hguard : (Formula.subset x value).Holds (schema v) w τ e t ↔ y ∈ D :=
      (Relations.unary_subset hf (hy.2 t) hv).trans (by simp)
    have hs' : ∀ r ∈ xs, ∃ z, Frozen v w τ f e r {z} := fun r hr => hs r (by simp [hr])
    change (Encoding.part (freezeChoice (.subset x value)
      (freezeFrom xs value body (captured.union x)) (freezeFrom xs value body captured)) p).Holds _ _ _ _ _ ↔ _
    rw [Encoding.freezeChoice_meaning (.subset _ _) (Encoding.freezeFrom_built _ _ _ _ hb)
      (Encoding.freezeFrom_built _ _ _ _ hb) p]
    by_cases hd : y ∈ D
    · simp only [hguard.mpr hd, true_and, not_true_eq_false, false_and, or_false]
      apply ih (captured.union x) (A ∪ {y}) (ha.union hy)
      · exact Set.union_subset inside (by simpa using hd)
      · exact hs'
      · intro z hz
        rcases cover z hz with hz | ⟨r, hr, hrz⟩
        · exact Or.inl (Or.inl hz)
        · rcases List.mem_cons.mp hr with rfl | hr
          · have hzy : y = z := Set.singleton_injective (hy.unique hf hrz)
            exact Or.inl (Or.inr hzy.symm)
          · exact Or.inr ⟨r, hr, hrz⟩
    · simp only [mt hguard.mp hd, false_and, not_false_eq_true, true_and, false_or]
      apply ih captured A ha inside hs'
      intro z hz
      rcases cover z hz with hz | ⟨r, hr, hrz⟩
      · exact Or.inl hz
      · rcases List.mem_cons.mp hr with rfl | hr
        · have hzy : y = z := Set.singleton_injective (hy.unique hf hrz)
          exact (hd (hzy.symm ▸ hz)).elim
        · exact Or.inr ⟨r, hr, hrz⟩

theorem freeze_meaning (v : IR.Structural.Layout k) (w : Nat) (τ : Trace)
    (f : U → Nat) (hf : Function.Injective f) (e : Environment) (t : Nat)
    (aliases : List Rel) (value : Rel) (D : Set U)
    (hv : Relations.Unary f D (value.eval (schema v) w τ e t))
    (hs : ∀ r ∈ aliases, ∃ x, Frozen v w τ f e r {x})
    (cover : ∀ x, ∃ r ∈ aliases, Frozen v w τ f e r {x})
    (body : Rel → Translation) (hb : ∀ r, Encoding.Built (body r))
    (P : Set U → Prop) (p : Option Bool)
    (correct : ∀ r S, (_ : Frozen v w τ f e r S) → (
      (Encoding.part (body r) p).Holds (schema v) w τ e t ↔ P S)) :
    (Encoding.part (freeze aliases value body) p).Holds (schema v) w τ e t ↔ P D :=
  freezeFrom_meaning v w τ f hf e t aliases value (.empty .unary) D ∅ hv
    ⟨.empty _, fun _ => Relations.unary_empty⟩ (Set.empty_subset _) hs
    (fun x _ => Or.inr (cover x)) body hb P p correct

end ClaferCompiler.Correctness.Behavioral
