module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersValues

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
namespace IntegerFold
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def operator (op : IR.BehavioralArithmetic.Fold) : IR.BehavioralArithmetic.Binary :=
  if op == .sum then .add else .multiply

def initial (op : IR.BehavioralArithmetic.Fold) : Int := if op == .sum then 0 else 1

def scalar (op : IR.BehavioralArithmetic.Fold) (x y : Int) : Int :=
  if op == .sum then x + y else x * y

def term (op : IR.BehavioralArithmetic.Fold) (xs : List Integer) (a : Integer) : Integer :=
  xs.foldl (Backend.Alloy.Behavioral.Arithmetic.binary (operator op)) a

theorem binary_built (op : IR.BehavioralArithmetic.Binary)
    (ha : Full.Value.Built a) (hb : Full.Value.Built b) :
    Full.Value.Built (integerBinary op a b) :=
  Full.Value.map_built _ _ (Full.Value.pair_built a b ha hb)

theorem binary_meaning (op : IR.BehavioralArithmetic.Binary)
    (ha : Full.Value.Built a) (hb : Full.Value.Built b) :
    Full.Value.Meaning s w τ e t (integerBinary op a b) n ↔
      ∃ x y, Full.Value.Meaning s w τ e t a x ∧ Full.Value.Meaning s w τ e t b y ∧
        n = Backend.Alloy.Behavioral.Arithmetic.binary op x y := by
  rw [integerBinary, Full.Value.map_meaning]
  simp only [Prod.exists, Full.Value.pair_meaning a b ha hb]
  aesop

theorem foldl_built (op : IR.BehavioralArithmetic.Fold) (values : List (Value Integer))
    (built : ∀ x ∈ values, Full.Value.Built x) (a : Value Integer) (ha : Full.Value.Built a) :
    Full.Value.Built (values.foldl (fun acc v => integerBinary (operator op) acc v) a) := by
  induction values generalizing a with
  | nil => exact ha
  | cons v vs ih =>
    exact ih (fun x hx => built x (List.mem_cons_of_mem _ hx)) _
      (binary_built _ ha (built v List.mem_cons_self))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem foldl_meaning (op : IR.BehavioralArithmetic.Fold) (values : List (Value Integer))
    (built : ∀ x ∈ values, Full.Value.Built x) (a : Value Integer) (ha : Full.Value.Built a) :
    Full.Value.Meaning s w τ e t
      (values.foldl (fun acc v => integerBinary (operator op) acc v) a) n ↔
    ∃ start xs, Full.Value.Meaning s w τ e t a start ∧
      List.Forall₂ (Full.Value.Meaning s w τ e t) values xs ∧ n = term op xs start := by
  induction values generalizing a with
  | nil => simp [term, List.forall₂_nil_left_iff]
  | cons v vs ih =>
    rw [List.foldl_cons, ih (fun x hx => built x (List.mem_cons_of_mem _ hx)) _
      (binary_built _ ha (built v List.mem_cons_self))]
    simp only [binary_meaning _ ha (built v List.mem_cons_self)]
    constructor
    · rintro ⟨start, xs, ⟨i, z, hi, hz, rfl⟩, hxs, rfl⟩
      exact ⟨i, z :: xs, hi, .cons hz hxs, rfl⟩
    · rintro ⟨i, xs, hi, hxs, rfl⟩
      cases hxs with
      | cons hz hxs => exact ⟨_, _, ⟨i, _, hi, hz, rfl⟩, hxs, rfl⟩

theorem built (op : IR.BehavioralArithmetic.Fold) (values : List (Value Integer))
    (h : ∀ x ∈ values, Full.Value.Built x) : Full.Value.Built (integerFold op values) :=
  foldl_built op values h _ (Full.Value.pure_built _)

theorem meaning (op : IR.BehavioralArithmetic.Fold) (values : List (Value Integer))
    (h : ∀ x ∈ values, Full.Value.Built x) :
    Full.Value.Meaning s w τ e t (integerFold op values) n ↔
      ∃ xs, List.Forall₂ (Full.Value.Meaning s w τ e t) values xs ∧
        n = term op xs (.literal (initial op)) := by
  change Full.Value.Meaning s w τ e t
    (values.foldl (fun acc v => integerBinary (operator op) acc v)
      (.pure (.literal (initial op)))) n ↔ _
  rw [foldl_meaning op values h _ (Full.Value.pure_built _)]
  simp only [Full.Value.pure_meaning]
  aesop

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Every intermediate target scalar is checked against the mathematical
before value. The independent target overflow semantics is never ignored. -/
theorem term_eval (op : IR.BehavioralArithmetic.Fold)
    (represented : List.Forall₂ (fun n z => Arithmetic.Term n ∧ n.eval s w τ e t = some z) ns zs)
    (ha : Arithmetic.Term a) (he : a.eval s w τ e t = some value)
    (fit : ∀ before, before <+: zs → Backend.Alloy.fitsInt w (before.foldl (scalar op) value) = true) :
    Arithmetic.Term (term op ns a) ∧
      (term op ns a).eval s w τ e t = some (zs.foldl (scalar op) value) := by
  induction represented generalizing a value with
  | nil => exact ⟨ha, he⟩
  | @cons n z ns zs hn hz ih =>
    have nextTerm : Arithmetic.Term (Backend.Alloy.Behavioral.Arithmetic.binary (operator op) a n) :=
      .binary _ ha hn.1
    have nextEval : (Backend.Alloy.Behavioral.Arithmetic.binary (operator op) a n).eval s w τ e t =
        some (scalar op value z) := by
      rw [Arithmetic.eval_binary _ ha hn.1, he, hn.2]
      have fitNext := fit [z] (by simp)
      cases op <;>
        simpa [operator, scalar, IR.BehavioralArithmetic.Binary.eval, IR.BehavioralArithmetic.Binary.apply]
          using (Backend.Alloy.boundedInt_some_iff w _).mpr fitNext
    apply ih nextTerm nextEval
    intro before hp
    exact fit (z :: before) (by simpa using hp)

theorem pure_built (op : IR.BehavioralArithmetic.Fold) (terms : List Integer) :
    Full.Value.Built (integerFold op (terms.map Value.pure)) := by
  apply built
  intro value hv
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
  exact Full.Value.pure_built n

theorem pure_meaning (op : IR.BehavioralArithmetic.Fold) (terms : List Integer) :
    Full.Value.Meaning s w τ e t (integerFold op (terms.map Value.pure)) n ↔
      n = term op terms (.literal (initial op)) := by
  rw [meaning op _ (by
    intro value hv
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
    exact Full.Value.pure_built n)]
  have pair (xs : List Integer) :
      List.Forall₂ (Full.Value.Meaning s w τ e t) (terms.map Value.pure) xs ↔ terms = xs := by
    simp only [List.forall₂_map_left_iff, Full.Value.pure_meaning, eq_comm]
    rw [List.forall₂_eq_eq_eq]
  simp only [pair]
  aesop

end IntegerFold

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem interval_fits_value (range : IR.Expr.Interval) (checked : range.fits w = true)
    (value : range.Contains z) : Backend.Alloy.fitsInt w z = true := by
  simp only [IR.Expr.Interval.fits, decide_eq_true_eq] at checked
  simp only [Backend.Alloy.fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨checked.1, checked.2.1⟩, ?_⟩, ?_⟩
  · exact checked.2.2.2.1.trans value.1
  · exact value.2.trans checked.2.2.2.2

namespace IntegerFold

theorem prefixes_fit (op : IR.BehavioralArithmetic.Fold)
    (range : IR.Expr.Interval)
    (checked : (IR.Behavioral.Expression.Ranges.foldRange op budget range).fits w = true)
    (size : zs.length ≤ budget) (members : ∀ z ∈ zs, range.Contains z)
    (before : List Int) (hb : before <+: zs) :
    Backend.Alloy.fitsInt w (before.foldl (scalar op) (initial op)) = true := by
  apply interval_fits_value _ checked
  have size' := hb.length_le.trans size
  have members' : ∀ z ∈ before, range.Contains z := fun z hz => members z (hb.subset hz)
  cases op with
  | sum =>
    change (IR.BehavioralArithmetic.setSumRange budget range).Contains
      (before.foldl (· + ·) 0)
    rw [← List.sum_eq_foldl]
    exact
      SemanticsBridge.BehavioralArithmetic.fold_sum_range size' members'
  | product =>
    change (IR.BehavioralArithmetic.productRange budget range).Contains
      (before.foldl (· * ·) 1)
    rw [← List.prod_eq_foldl]
    exact
      SemanticsBridge.BehavioralArithmetic.fold_product_range size' members'

end IntegerFold
end ClaferCompiler.Correctness.Behavioral.Full
