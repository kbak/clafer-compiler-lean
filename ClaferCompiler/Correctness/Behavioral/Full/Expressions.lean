module

public import ClaferCompiler.Correctness.Behavioral.Full.Collections
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Expressions

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Encoding
attribute [local instance] Classical.propDecidable

/-- Occurrences are positions in the tuple enumeration. Distinct tuples with
the same raw truth contribute separately, as required by grouped counting. -/
def trueCount (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (ps : List Formula) : Nat := by
  classical
  exact ps.countP fun p => decide (p.Holds s w τ e t)

def CountState (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (pair : Formula × Formula) (n : Nat) : Prop :=
  pair.1.Built ∧ pair.2.Built ∧
  (pair.1.Holds s w τ e t ↔ n = 0) ∧ (pair.2.Holds s w τ e t ↔ n = 1)

def countStep (acc : Formula × Formula) (p : Formula) : Formula × Formula :=
  (.binary .conj acc.1 (.unary .neg p),
   .binary .disj (.binary .conj acc.2 (.unary .neg p)) (.binary .conj acc.1 p))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem countStep_correct (hp : p.Built) (hc : CountState s w τ e t acc n) :
    CountState s w τ e t (countStep acc p)
      (n + if p.Holds s w τ e t then 1 else 0) := by
  classical
  rcases hc with ⟨hz, ho, hzero, hone⟩
  refine ⟨.binary .conj hz (.unary .neg hp),
    .binary .disj (.binary .conj ho (.unary .neg hp)) (.binary .conj hz hp), ?_, ?_⟩
  · simp only [countStep, holds_and hz (.unary .neg hp), holds_neg hp, hzero]
    by_cases h : p.Holds s w τ e t <;> simp [h]
  · simp only [countStep, holds_or (.binary .conj ho (.unary .neg hp)) (.binary .conj hz hp),
      holds_and ho (.unary .neg hp), holds_and hz hp, holds_neg hp, hone, hzero]
    by_cases h : p.Holds s w τ e t <;> simp [h]

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem countFold_correct (ps : List Formula) (hps : ∀ p ∈ ps, p.Built)
    (hc : CountState s w τ e t acc n) :
    CountState s w τ e t (ps.foldl countStep acc) (n + trueCount s w τ e t ps) := by
  classical
  induction ps generalizing acc n with
  | nil => simpa [trueCount] using hc
  | cons p ps ih =>
    have hp := hps p (by simp)
    have rest := ih (fun q hq => hps q (by simp [hq])) (countStep_correct hp hc)
    simpa [trueCount, List.countP_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

/-- The target formula counts all complete ordered tuples. This is the finite
counting lemma consumed after tuple enumeration/observation correspondence. -/
theorem countTruth_correct (q : IR.Behavioral.Grouped.Count) (ps : List Formula)
    (hps : ∀ p ∈ ps, p.Built) :
    (Expressions.countTruth q ps).Holds s w τ e t ↔
      match q with | .one => trueCount s w τ e t ps = 1
                   | .lone => trueCount s w τ e t ps ≤ 1 := by
  have initial : CountState s w τ e t (.truth, .falsity) 0 :=
    ⟨.truth, .falsity, by simp, by simp [Formula.Holds, Formula.fold, Formula.falsity,
      FormulaAlgebra.step, formulaAlgebra]⟩
  have h := countFold_correct ps hps initial
  simp only [Nat.zero_add] at h
  rcases h with ⟨hz, ho, hzero, hone⟩
  cases q with
  | one => exact hone
  | lone =>
    change (Formula.binary .disj (ps.foldl countStep (.truth, .falsity)).1
      (ps.foldl countStep (.truth, .falsity)).2).Holds s w τ e t ↔ trueCount s w τ e t ps ≤ 1
    rw [holds_or hz ho, hzero, hone]
    omega

end ClaferCompiler.Correctness.Behavioral.Full
