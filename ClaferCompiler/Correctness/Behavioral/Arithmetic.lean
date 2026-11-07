module

public import ClaferCompiler.Backend.Alloy.Behavioral.Arithmetic
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics
public import ClaferCompiler.Correctness.IntegerArithmetic
public import ClaferCompiler.SemanticsBridge.BehavioralArithmetic

public section
namespace ClaferCompiler.Correctness.Behavioral.Arithmetic
open Backend.Alloy Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Arithmetic

abbrev Operator := IR.BehavioralArithmetic.Binary

/-- The static integer proof's stack discipline, specialized to the temporal
target. Shape evidence contains no arithmetic or source satisfaction premise. -/
inductive Term : Temporal.Integer → Prop where
  | literal (n : Int) : Term (.literal n)
  | count (r : Temporal.Rel) : Term (.count r)
  | scalar (lo hi : Int) (r : Temporal.Rel) : Term (.scalar lo hi r)
  | binary (op : Operator) : Term a → Term b → Term (binary op a b)

@[expose] def applyAlgebra (a : Temporal.IntegerAlgebra α) : Operator → α → α → α
  | .add => a.add | .subtract => a.subtract | .multiply => a.multiply
  | .divide => a.divide | .remainder => a.remainder

-- [proof->req~compiler-alloy-temporal-target~1]
theorem Term.stack (h : Term n) (a : Temporal.IntegerAlgebra α) :
    ∃ value, ∀ stack, n.code.foldl a.step (some stack) = some (value :: stack) := by
  induction h with
  | literal n => exact ⟨a.literal n, fun _ => rfl⟩
  | count r => exact ⟨a.count r, fun _ => rfl⟩
  | scalar lo hi r => exact ⟨a.scalar lo hi r, fun _ => rfl⟩
  | binary op _ _ ihp ihq =>
    obtain ⟨x, hx⟩ := ihp
    obtain ⟨y, hy⟩ := ihq
    refine ⟨applyAlgebra a op x y, fun stack => ?_⟩
    cases op <;> simp [Backend.Alloy.Behavioral.Arithmetic.binary, Temporal.Integer.add, Temporal.Integer.subtract,
      Temporal.Integer.multiply, Temporal.Integer.divide, Temporal.Integer.remainder,
      List.foldl_append, hx, hy, Temporal.IntegerAlgebra.step, applyAlgebra]

theorem fold_binary (op : Operator) (ha : Term a) (hb : Term b)
    (alg : Temporal.IntegerAlgebra α) (fallback : α) :
    (binary op a b).fold alg fallback =
      applyAlgebra alg op (a.fold alg fallback) (b.fold alg fallback) := by
  obtain ⟨x, hx⟩ := ha.stack alg
  obtain ⟨y, hy⟩ := hb.stack alg
  cases op <;> simp [binary, Temporal.Integer.fold, Temporal.Integer.add,
    Temporal.Integer.subtract, Temporal.Integer.multiply, Temporal.Integer.divide,
    Temporal.Integer.remainder, List.foldl_append, hx, hy, Temporal.IntegerAlgebra.step,
    applyAlgebra]

/-- Target evaluation follows the source scalar operation when its result fits.
This equation also preserves missing operands and division/remainder by zero. -/
theorem eval_binary (op : Operator) (ha : Term a) (hb : Term b)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (e : Temporal.Environment) (t : Nat) :
    (binary op a b).eval s w τ e t =
      (op.eval (a.eval s w τ e t) (b.eval s w τ e t)).bind (boundedInt w) := by
  unfold Temporal.Integer.eval
  rw [fold_binary op ha hb]
  cases op <;> simp only [applyAlgebra, IR.BehavioralArithmetic.Binary.eval,
    IR.BehavioralArithmetic.Binary.apply, Option.bind_assoc, Option.bind_some]
  all_goals try rfl
  all_goals
    congr 1
    funext x
    congr 1
    funext y
    split <;> rfl

/-- A represented singleton uses its mathematical value. The target fallback
cannot alter a defined source extraction satisfying the admitted interval. -/
theorem represented_scalar (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace)
    (e : Temporal.Environment) (t : Nat) (r : Temporal.Rel) (lo hi value : Int)
    (rows : (r.eval s w τ e t).eraseDups = [[Temporal.Atom.integer value]])
    (lower : lo ≤ value) (upper : value ≤ hi) (fits : fitsInt w value = true) :
    (Temporal.Integer.scalar lo hi r).eval s w τ e t = some value := by
  simp [Temporal.Integer.eval, Temporal.Integer.scalar, Temporal.Integer.fold,
    Temporal.IntegerAlgebra.step, Temporal.scalarValue, rows, lower, upper, boundedInt, fits]

abbrev interval (r : IntRange) : IR.Expr.Interval := ⟨r.lower, r.upper⟩

abbrev targetInterval (r : IR.Expr.Interval) : IntRange := ⟨r.lower, r.upper⟩

theorem checked_fits (r : IntRange) (w : Nat) :
    (r.checked w = some r) ↔ (interval r).fits w = true := by
  have lo : (IR.Expr.signedRange w).lower = minInt w := by
    simp [IR.Expr.signedRange, minInt]
  have hi : (IR.Expr.signedRange w).upper = maxInt w := by
    simp [IR.Expr.signedRange, maxInt]
  change r.checked w = some r ↔
    decide (1 ≤ w ∧ w ≤ 16 ∧ r.lower ≤ r.upper ∧
      (IR.Expr.signedRange w).lower ≤ r.lower ∧ r.upper ≤ (IR.Expr.signedRange w).upper) = true
  rw [decide_eq_true_eq, lo, hi]
  rw [IntRange.checked_iff]
  simp only [fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨_, order, lower, upper⟩
    exact ⟨lower.1.1.1, lower.1.1.2, order, lower.1.2, upper.2⟩
  · rintro ⟨wlo, whi, order, lower, upper⟩
    exact ⟨trivial, order, ⟨⟨⟨wlo, whi⟩, lower⟩, order.trans upper⟩,
      ⟨⟨⟨wlo, whi⟩, lower.trans order⟩, upper⟩⟩

theorem range_binary (op : Operator) (ha : Term a) (hb : Term b)
    (m : Temporal.Module) (ra rb : IntRange)
    (har : a.range m = some ra) (hbr : b.range m = some rb) :
    (binary op a b).range m =
      if op.nonzero (interval rb) then
        (targetInterval (op.range (interval ra) (interval rb))).checked m.command.bitwidth
      else none := by
  unfold Temporal.Integer.range at har hbr ⊢
  rw [fold_binary op ha hb]
  rw [har, hbr]
  cases op <;> simp [applyAlgebra, IR.BehavioralArithmetic.Binary.range,
    IR.BehavioralArithmetic.Binary.nonzero, IR.BehavioralArithmetic.magnitude,
    IR.BehavioralArithmetic.symmetric, IR.Expr.Interval.add, IR.Expr.Interval.subtract,
    targetInterval, quotientRange, nonzero, magnitude, symmetric, decide_eq_true_eq]

/-- A checked frontend scalar range suffices for concrete target evaluation,
once the two operand values are represented. No truth premise is used. -/
theorem represented_binary (op : Operator) (ha : Term a) (hb : Term b)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (e : Temporal.Environment) (t : Nat)
    (ra rb : IR.Expr.Interval) (checked : IR.BehavioralArithmetic.Checked op w ra rb)
    (x y : Int) (hx : ra.Contains x) (hy : rb.Contains y)
    (hexa : a.eval s w τ e t = some x) (hexb : b.eval s w τ e t = some y) :
    ∃ z, (SemanticsBridge.BehavioralArithmetic.binary op).apply x y = some z ∧
      (binary op a b).eval s w τ e t = some z := by
  obtain ⟨z, hz, hfit⟩ := SemanticsBridge.BehavioralArithmetic.admitted_range op checked hx hy
  refine ⟨z, hz, ?_⟩
  rw [eval_binary op ha hb, hexa, hexb,
    SemanticsBridge.BehavioralArithmetic.scalar_agrees]
  change ((SemanticsBridge.BehavioralArithmetic.binary op).apply x y).bind (boundedInt w) = some z
  rw [hz]
  apply (boundedInt_some_iff w z).mpr
  have hw := checked.inputs.1
  simp only [IR.Expr.Interval.fits, decide_eq_true_eq] at hw
  simp only [fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hw.1, hw.2.1⟩, ?_⟩, ?_⟩
  · simpa [minInt, IR.Expr.signedRange, IR.Expr.Interval.Contains] using hfit.1
  · simpa [maxInt, IR.Expr.signedRange, IR.Expr.Interval.Contains] using hfit.2

end ClaferCompiler.Correctness.Behavioral.Arithmetic
