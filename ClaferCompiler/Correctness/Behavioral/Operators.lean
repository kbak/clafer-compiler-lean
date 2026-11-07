module

public import ClaferCompiler.Backend.Alloy.Behavioral.Operators
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics
public import Clafer.Behavioral.Lifetime

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
namespace Encoding
open Backend.Alloy.Behavioral

-- [proof->req~compiler-behavioral-correctness~1]
/-- The concrete emitted next formula has independent target meaning equal to
the upstream lifetime operator, including cancellation. Shape is not truth. -/
theorem next_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a : Formula) (hp : p.Built) (ha : a.Built) (t : Nat) :
    (next p a).Holds s w τ e t ↔
      Clafer.Behavioral.Lifetime.next (fun j => p.Holds s w τ e j)
        (fun j => a.Holds s w τ e j) t := by
  classical
  simp only [next, Formula.Holds,
    Formula.fold_unary _ _ _ _ (.binary .disj (.unary .neg hp) ha),
    Formula.fold_binary _ _ _ _ _ (.unary .neg hp) ha,
    Formula.fold_unary _ _ _ _ hp]
  simp [formulaAlgebra, Clafer.Behavioral.Lifetime.next, imp_iff_not_or]

theorem eventually_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a : Formula) (hp : p.Built) (ha : a.Built) (t : Nat) :
    (eventually p a).Holds s w τ e t ↔
      Clafer.Behavioral.Lifetime.eventually (fun j => p.Holds s w τ e j)
        (fun j => a.Holds s w τ e j) t := by
  rw [Clafer.Behavioral.Lifetime.eventually_lower]
  simp only [eventually, Formula.Holds,
    Formula.fold_unary _ _ _ _ (.binary .disj (.unary .neg hp) ha),
    Formula.fold_binary _ _ _ _ _ (.unary .neg hp) ha,
    Formula.fold_unary _ _ _ _ hp]
  rfl

theorem always_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a : Formula) (hp : p.Built) (ha : a.Built) (t : Nat) :
    (always p a).Holds s w τ e t ↔
      Clafer.Behavioral.Lifetime.always (fun j => p.Holds s w τ e j)
        (fun j => a.Holds s w τ e j) t := by
  rw [Clafer.Behavioral.Lifetime.always_lower]
  simp only [always, Formula.weakUntil, Formula.Holds,
    Formula.fold_binary _ _ _ _ _ (.binary .until (.binary .conj hp ha) (.unary .neg hp))
      (.unary .always (.binary .conj hp ha)),
    Formula.fold_binary _ _ _ _ _ (.binary .conj hp ha) (.unary .neg hp),
    Formula.fold_unary _ _ _ _ (.binary .conj hp ha),
    Formula.fold_binary _ _ _ _ _ hp ha, Formula.fold_unary _ _ _ _ hp]
  exact or_comm

theorem until_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a b : Formula) (hp : p.Built) (ha : a.Built) (hb : b.Built) (t : Nat) :
    (strongUntil p a b).Holds s w τ e t ↔
      Clafer.Behavioral.Lifetime.strongUntil (fun j => p.Holds s w τ e j)
        (fun j => a.Holds s w τ e j) (fun j => b.Holds s w τ e j) t := by
  simp only [strongUntil, Formula.Holds,
    Formula.fold_binary _ _ _ _ _ (.binary .conj hp ha) (.binary .disj (.unary .neg hp) hb),
    Formula.fold_binary _ _ _ _ _ hp ha,
    Formula.fold_binary _ _ _ _ _ (.unary .neg hp) hb,
    Formula.fold_unary _ _ _ _ hp]
  rfl

theorem weakUntil_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p a b : Formula) (hp : p.Built) (ha : a.Built) (hb : b.Built) (t : Nat) :
    (weakUntil p a b).Holds s w τ e t ↔
      Clafer.Behavioral.Lifetime.weakUntil (fun j => p.Holds s w τ e j)
        (fun j => a.Holds s w τ e j) (fun j => b.Holds s w τ e j) t := by
  have hga : (always p a).Built :=
    .binary .disj (.binary .until (.binary .conj hp ha) (.unary .neg hp))
      (.unary .always (.binary .conj hp ha))
  have hua : (strongUntil p a b).Built :=
    .binary .until (.binary .conj hp ha) (.binary .disj (.unary .neg hp) hb)
  change ((Formula.binary .disj (always p a) (strongUntil p a b)).Holds s w τ e t) ↔ _
  change ((Formula.binary .disj (always p a) (strongUntil p a b)).fold
    (formulaAlgebra s w τ) (fun _ _ => False) e t) ↔ _
  rw [Formula.fold_binary _ _ _ _ _ hga hua]
  change (always p a).Holds s w τ e t ∨ (strongUntil p a b).Holds s w τ e t ↔ _
  rw [always_meaning s w τ e p a hp ha, until_meaning s w τ e p a b hp ha hb]
  rfl

end Encoding
end ClaferCompiler.Correctness.Behavioral
