module

public import ClaferCompiler.IR.BehavioralArithmetic
public import ClaferCompiler.SemanticsBridge.ExprObservation
public import Clafer.Behavioral.PrimitiveExpression
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.BehavioralArithmetic
open IR.BehavioralArithmetic IR.Expr
open scoped BigOperators

def binary : Binary → Clafer.Behavioral.Arithmetic.Binary
  | .add => .add | .subtract => .subtract | .multiply => .multiply
  | .divide => .divide | .remainder => .remainder

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem scalar_agrees (op : Binary) (a b : Option Int) :
    op.eval a b = (binary op).eval a b := by
  cases op <;> cases a <;> cases b <;> rfl

theorem missing_left (op : Binary) (b : Option Int) : op.eval none b = none := rfl
theorem missing_right (op : Binary) (a : Option Int) : op.eval a none = none := by cases a <;> rfl
theorem strict_branches (c : Option Bool) (a : Option α) :
    conditional c none a = none ∧ conditional c a none = none := by
  cases c <;> cases a <;> simp [conditional]

theorem magnitude_bound {r : Interval} {i : Int} (h : r.Contains i) : i.natAbs ≤ magnitude r := by
  have lo := Int.le_natAbs (a := -r.lower)
  rw [Int.natAbs_neg] at lo
  have hi := Int.le_natAbs (a := r.upper)
  have ml : (r.lower.natAbs : Int) ≤ (magnitude r : Int) := by
    exact_mod_cast Nat.le_max_left r.lower.natAbs r.upper.natAbs
  have mu : (r.upper.natAbs : Int) ≤ (magnitude r : Int) := by
    exact_mod_cast Nat.le_max_right r.lower.natAbs r.upper.natAbs
  rcases h with ⟨hl, hu⟩
  have bounds : -(magnitude r : Int) ≤ i ∧ i ≤ magnitude r := by omega
  by_cases h : 0 ≤ i
  · have := Int.natAbs_of_nonneg h; omega
  · have := Int.ofNat_natAbs_of_nonpos (by omega : i ≤ 0); omega

theorem symmetric_contains {q : Nat} {i : Int} (h : i.natAbs ≤ q) : (symmetric q).Contains i := by
  have lo := Int.le_natAbs (a := -i)
  rw [Int.natAbs_neg] at lo
  have hi := Int.le_natAbs (a := i)
  change -(q : Int) ≤ i ∧ i ≤ (q : Int)
  omega

theorem range_contains (op : Binary) {a b : Interval} {x y z : Int}
    (hx : a.Contains x) (hy : b.Contains y) (result : op.apply x y = some z) :
    (op.range a b).Contains z := by
  have ax := magnitude_bound hx
  have by' := magnitude_bound hy
  cases op with
  | add =>
    have hz : z = x + y := (Option.some.inj result).symm
    subst z
    change a.lower + b.lower ≤ x + y ∧ x + y ≤ a.upper + b.upper
    rcases hx with ⟨_, _⟩; rcases hy with ⟨_, _⟩; omega
  | subtract =>
    have hz : z = x - y := (Option.some.inj result).symm
    subst z
    change a.lower - b.upper ≤ x - y ∧ x - y ≤ a.upper - b.lower
    rcases hx with ⟨_, _⟩; rcases hy with ⟨_, _⟩; omega
  | multiply =>
    have hz : z = x * y := (Option.some.inj result).symm
    subst z
    apply symmetric_contains
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul ax by'
  | divide =>
    simp only [Binary.apply] at result
    split at result
    · cases result
    · cases Option.some.inj result
      exact symmetric_contains ((Int.natAbs_tdiv_le_natAbs x y).trans ax)
  | remainder =>
    simp only [Binary.apply] at result
    split at result
    · cases result
    · cases Option.some.inj result
      apply symmetric_contains
      rw [Int.natAbs_tmod]
      exact (Nat.mod_le _ _).trans ax

theorem divisor_nonzero (op : Binary) {r : Interval} {y : Int}
    (hy : r.Contains y) (safe : op.nonzero r = true) :
    op = .divide ∨ op = .remainder → y ≠ 0 := by
  intro hop
  rcases hop with rfl | rfl <;>
    simp only [Binary.nonzero, Bool.or_eq_true, decide_eq_true_eq] at safe <;>
    rcases hy with ⟨_, _⟩ <;> omega

/-- Every admitted operand pair has a defined source result and that result
fits the selected target width, including negative division and all intermediates
represented by this scalar operation. -/
theorem admitted_range (op : Binary) {width : Nat} {a b : Interval}
    (checked : Checked op width a b) {x y : Int} (hx : a.Contains x) (hy : b.Contains y) :
    ∃ z, (binary op).apply x y = some z ∧ (signedRange width).Contains z := by
  have nonzero := divisor_nonzero op hy checked.divisor
  have sourceDomain : binary op = .divide ∨ binary op = .remainder → y ≠ 0 := by
    cases op <;> simp_all [binary]
  obtain ⟨z, hz⟩ := (Clafer.Behavioral.Arithmetic.defined_iff (binary op) x y).mpr sourceDomain
  have equality : op.apply x y = (binary op).apply x y := by cases op <;> rfl
  have interval := range_contains op hx hy (equality.trans hz)
  have fits := checked.result
  simp only [Interval.fits, decide_eq_true_eq] at fits
  exact ⟨z, hz, le_trans fits.2.2.2.1 interval.1, le_trans interval.2 fits.2.2.2.2⟩

universe u
variable {U : Type u} (R : Clafer.Constraints.IntegerRealization U)

/-- The full mathematical carrier remains independent; the list describes only
the current finite observation. Equal values denote one integer object. -/
def observed (values : List Int) : Set U := {x | ∃ i ∈ values, R.encode i = x}

theorem observed_finite (values : List Int) : (observed R values).Finite := by
  exact (List.finite_toSet values).image R.encode

theorem observed_typed (values : List Int) : observed R values ⊆ R.domain := by
  rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩

theorem observation_defined (values : List Int) :
    ∃ i, Clafer.Behavioral.IntegerObservation.coerce R (observed R values) = some i :=
  (Clafer.Behavioral.IntegerObservation.coerce_defined_iff R _).mpr
    ⟨observed_finite R values, observed_typed R values⟩

theorem coerce_sum (values : List Int) : coerce values = ∑ i ∈ values.toFinset, i := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x ∈ xs
    · simp [h, ih, Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
    · simp [h, ih]

-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- Exact finite-set conversion, for any realization of the full integer domain.
The proof does not quotient reference heads; only the implicit target set is summed. -/
theorem coerce_agrees (values : List Int) :
    Clafer.Behavioral.IntegerObservation.coerce R (observed R values) = some (coerce values) := by
  classical
  rw [Clafer.Behavioral.IntegerObservation.coerce_finite R
    (observed_finite R values) (observed_typed R values)]
  have he : (observed_finite R values).toFinset = values.toFinset.map R.encode := by
    ext x
    simp [observed]
  rw [he, Finset.sum_map]
  simp only [R.decode_encode, coerce_sum]

theorem sum_bound (values : List Int) (bound : Nat)
    (small : ∀ x ∈ values, x.natAbs ≤ bound) : values.sum.natAbs ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hx := small x (by simp)
    have hxs := ih (fun y hy => small y (by simp [hy]))
    simpa [Nat.add_mul, Nat.add_comm] using (Int.natAbs_add_le x xs.sum).trans (Nat.add_le_add hx hxs)

theorem product_bound (values : List Int) (bound : Nat)
    (small : ∀ x ∈ values, x.natAbs ≤ bound) : values.prod.natAbs ≤ bound ^ values.length := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hx := small x (by simp)
    have hxs := ih (fun y hy => small y (by simp [hy]))
    simpa [Int.natAbs_mul, pow_succ, Nat.mul_comm] using Nat.mul_le_mul hx hxs

/-- A sum budget counts occurrences before any deduplication; this bound therefore
also covers implicit coercion and every prefix of an occurrence fold. -/
theorem coerce_bound (values : List Int) (bound : Nat)
    (small : ∀ x ∈ values, x.natAbs ≤ bound) : (coerce values).natAbs ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hxs := ih (fun y hy => small y (by simp [hy]))
    have hx := small x (by simp)
    simp only [coerce_cons]
    split
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · simpa [Nat.add_mul, Nat.add_comm] using (Int.natAbs_add_le x (coerce xs)).trans (Nat.add_le_add hx hxs)

theorem observation_range {values : List Int} {r : Interval} {budget : Nat}
    (count : values.length ≤ budget) (typed : ∀ x ∈ values, r.Contains x) :
    (setSumRange budget r).Contains (coerce values) :=
  symmetric_contains ((coerce_bound values (magnitude r)
    (fun x hx => magnitude_bound (typed x hx))).trans (Nat.mul_le_mul_right _ count))

theorem fold_sum_range {values : List Int} {r : Interval} {budget : Nat}
    (count : values.length ≤ budget) (typed : ∀ x ∈ values, r.Contains x) :
    (setSumRange budget r).Contains values.sum :=
  symmetric_contains ((sum_bound values (magnitude r)
    (fun x hx => magnitude_bound (typed x hx))).trans (Nat.mul_le_mul_right _ count))

theorem fold_product_range {values : List Int} {r : Interval} {budget : Nat}
    (count : values.length ≤ budget) (typed : ∀ x ∈ values, r.Contains x) :
    (productRange budget r).Contains values.prod := by
  apply symmetric_contains
  apply (product_bound values (max 1 (magnitude r))
    (fun x hx => (magnitude_bound (typed x hx)).trans (Nat.le_max_right _ _))).trans
  exact Nat.pow_le_pow_right (Nat.le_max_left _ _) count

theorem minimum_membership (values : List Int) (i : Int) :
    i ∈ minimum values ↔ i ∈ values ∧ ∀ j ∈ values, i ≤ j := by
  simp [minimum, List.min?_eq_some_iff]

theorem maximum_membership (values : List Int) (i : Int) :
    i ∈ maximum values ↔ i ∈ values ∧ ∀ j ∈ values, j ≤ i := by
  simp [maximum, List.max?_eq_some_iff]

theorem minimum_agrees (values : List Int) :
    Clafer.Behavioral.Aggregate.Extreme.minimum.select R (observed R values) =
      some (observed R (minimum values)) := by
  rw [Clafer.Behavioral.Aggregate.select_finite _ R (observed_finite R values) (observed_typed R values)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, least⟩
    refine ⟨i, (minimum_membership values i).mpr ⟨hi, ?_⟩, rfl⟩
    intro j hj
    simpa only [Clafer.Behavioral.Aggregate.Extreme.before, R.decode_encode] using least (R.encode j) ⟨j, hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨member, least⟩ := (minimum_membership values i).mp hi
    refine ⟨⟨i, member, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    simpa only [Clafer.Behavioral.Aggregate.Extreme.before, R.decode_encode] using least j hj

theorem maximum_agrees (values : List Int) :
    Clafer.Behavioral.Aggregate.Extreme.maximum.select R (observed R values) =
      some (observed R (maximum values)) := by
  rw [Clafer.Behavioral.Aggregate.select_finite _ R (observed_finite R values) (observed_typed R values)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, greatest⟩
    refine ⟨i, (maximum_membership values i).mpr ⟨hi, ?_⟩, rfl⟩
    intro j hj
    simpa only [Clafer.Behavioral.Aggregate.Extreme.before, R.decode_encode] using greatest (R.encode j) ⟨j, hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨member, greatest⟩ := (maximum_membership values i).mp hi
    refine ⟨⟨i, member, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    simpa only [Clafer.Behavioral.Aggregate.Extreme.before, R.decode_encode] using greatest j hj

def fold : Fold → Clafer.Behavioral.Aggregate.Fold
  | .sum => .sum | .product => .product

theorem traverse_values (values : List Int) : (values.map some).mapM id = some values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- The semantic indices are operand occurrences. Equal values remain separate;
flattening operand families retains their order and cardinality. -/
theorem fold_agrees (op : Fold) (values : List Int) :
    (fold op).eval (Set.univ : Set (Fin values.length)) (fun i => some values[i]) =
      op.eval [values.map some] := by
  rw [Clafer.Behavioral.Aggregate.fold_finite _ (Set.finite_univ) _ (by simp)]
  have listValues : List.ofFn (fun i : Fin values.length => values[i]) = values := List.ofFn_get _
  cases op <;>
    simp only [Fold.eval, List.flatten_cons, List.flatten_nil, List.append_nil, traverse_values,
      pure, fold, Set.toFinite_toFinset, Set.toFinset_univ, Option.getD_some]
  · congr 1
    rw [← Fin.sum_ofFn, listValues]
  · congr 1
    rw [← Fin.prod_ofFn, listValues]

/-- Historical extraction is reused unchanged; it never applies D3 summation. -/
theorem extract_common (values : List Int) :
    IR.BehavioralArithmetic.extract values = Expr.integers.extract
      (Expr.atomSet (values.map Atom.integer)) :=
  Expr.extract_agreement _

theorem extrema_range {values : List Int} {r : Interval}
    (typed : ∀ x ∈ values, r.Contains x) :
    (∀ x ∈ minimum values, r.Contains x) ∧ (∀ x ∈ maximum values, r.Contains x) :=
  ⟨fun x hx => typed x ((minimum_membership values x).mp hx).1,
    fun x hx => typed x ((maximum_membership values x).mp hx).1⟩

theorem negate_range {r : Interval} {x : Int} (hx : r.Contains x) :
    (negateRange r).Contains (-x) := by
  rcases hx with ⟨_, _⟩
  simp only [negateRange, Interval.Contains]; omega

theorem count_range {count budget : Nat} (h : count ≤ budget) :
    (countRange budget).Contains (count : Int) := by
  simp only [countRange, Interval.Contains]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr h⟩

end ClaferCompiler.SemanticsBridge.BehavioralArithmetic
