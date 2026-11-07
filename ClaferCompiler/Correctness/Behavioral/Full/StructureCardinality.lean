module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureState
public import ClaferCompiler.Correctness.StructuralCardinality
public import ClaferCompiler.Correctness.Behavioral.ExpressionsMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem interval_built (b : IR.Structural.Bounds) (r : Rel) : (interval b r).Built := by
  apply Formula.Built.binary
  · split <;> constructor
  · cases b.upper <;> constructor

/-- Reuses finite-set cardinality and the static unary cardinal construction,
with temporal atoms in place of the static target's natural-number tuples. -/
theorem unary_card {U : Type} [Fintype U] (P : U → Prop) [DecidablePred P]
    (f : U → Nat) (hf : Function.Injective f) (xs : Relation)
    (hm : Relations.Unary f {x | P x} xs) :
    xs.eraseDups.length = Fintype.card {x // P x} := by
  classical
  let emb : U ↪ List Atom := ⟨fun x => [.object (f x)], by
    intro x y h
    exact hf (by simpa using h)⟩
  have he : xs.toFinset = (Finset.univ.filter P).map emb := by
    ext row
    simp only [List.mem_toFinset, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change row ∈ xs ↔ ∃ x, P x ∧ [.object (f x)] = row
    simpa only [Set.mem_ofPred, eq_comm] using hm row
  have dedup : xs.eraseDups.toFinset = xs.toFinset := by ext; simp
  rw [← List.toFinset_card_of_nodup (Structural.eraseDups_nodup xs), dedup,
    he, Finset.card_map, Fintype.card_subtype]

theorem bounded_compare_le (w : Nat) (a b : Int) :
    (∃ x y, Backend.Alloy.boundedInt w a = some x ∧
      Backend.Alloy.boundedInt w b = some y ∧ Backend.Alloy.Comparison.le.holds x y = true) ↔
    Backend.Alloy.fitsInt w a = true ∧ Backend.Alloy.fitsInt w b = true ∧ a ≤ b := by
  unfold Backend.Alloy.boundedInt
  split <;> split <;> simp_all [Backend.Alloy.Comparison.holds]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Exact numeric and range conditions of the emitted interval. No target
truth is hidden in the range obligation used for the converse direction. -/
theorem interval_holds (w : Nat) (b : IR.Structural.Bounds) (r : Rel)
    (s : Schema) (τ : Trace) (env : Environment) (t : Nat) :
    (interval b r).Holds s w τ env t ↔
      Structural.IntervalFits w b (r.eval s w τ env t).eraseDups.length ∧
      DPGraph.Predicates.CountInRange (SemanticsBridge.Structural.bounds b)
        (r.eval s w τ env t).eraseDups.length := by
  have hl : (if b.lower == 0 then Formula.truth else
      .compare .le (.literal (Int.ofNat b.lower)) (.count r)).Built := by split <;> constructor
  have hu : (match b.upper with
      | .unbounded => Formula.truth
      | .finite n => .compare .le (.count r) (.literal (Int.ofNat n))).Built := by
    cases b.upper <;> constructor
  unfold interval
  dsimp only
  refine (Encoding.holds_and (s := s) (w := w) (τ := τ) (e := env) (t := t) hl hu).trans ?_
  have hc (a b : Int) :
      (∃ x, Backend.Alloy.boundedInt w a = some x ∧
        ∃ y, Backend.Alloy.boundedInt w b = some y ∧ Backend.Alloy.Comparison.le.holds x y = true) ↔
      Backend.Alloy.fitsInt w a = true ∧ Backend.Alloy.fitsInt w b = true ∧ a ≤ b := by
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact (bounded_compare_le w a b).mp ⟨x, y, hx, hy, h⟩
    · intro h
      obtain ⟨x, y, hx, hy, h⟩ := (bounded_compare_le w a b).mpr h
      exact ⟨x, hx, y, hy, h⟩
  cases b with
  | mk lower upper =>
    cases upper <;> by_cases hz : lower = 0 <;>
      simp [hz, Formula.Holds, Formula.fold, Formula.truth, Formula.compare,
        FormulaAlgebra.step, formulaAlgebra, Integer.eval, Integer.fold, Integer.literal,
        Integer.count, IntegerAlgebra.step, hc, Structural.IntervalFits,
        DPGraph.Predicates.CountInRange, SemanticsBridge.Structural.bounds] <;> tauto

theorem interval_source {U : Type} [Fintype U] (P : U → Prop) [DecidablePred P]
    (f : U → Nat) (hf : Function.Injective f) (r : Rel)
    (s : Schema) (w : Nat) (τ : Trace) (env : Environment) (t : Nat)
    (hm : Relations.Unary f {x | P x} (r.eval s w τ env t)) (b : IR.Structural.Bounds) :
    (interval b r).Holds s w τ env t ↔
      Structural.IntervalFits w b (Fintype.card {x // P x}) ∧
      DPGraph.Predicates.InRange (SemanticsBridge.Structural.bounds b) {x // P x} := by
  rw [interval_holds, unary_card P f hf _ hm, DPGraph.Predicates.inRange_card]

end ClaferCompiler.Correctness.Behavioral.Full
