module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersFolds
public import ClaferCompiler.Correctness.Behavioral.ExpressionsDefined

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
open Backend.Alloy.Temporal
open Backend.Alloy (IntRange)

/-- Full behavioral expressions count finite choices with literals. Their
arithmetic therefore needs no relation-cardinality hypothesis. -/
inductive IntegerPure : Integer → Prop where
  | literal (z : Int) : IntegerPure (.literal z)
  | scalar (lo hi : Int) (r : Rel) : IntegerPure (.scalar lo hi r)
  | binary (op : IR.BehavioralArithmetic.Binary) : IntegerPure a → IntegerPure b →
      IntegerPure (Backend.Alloy.Behavioral.Arithmetic.binary op a b)

theorem IntegerPure.term (h : IntegerPure n) : Arithmetic.Term n := by
  induction h with
  | literal z => exact .literal z
  | scalar lo hi r => exact .scalar lo hi r
  | binary op _ _ ihl ihr => exact .binary op ihl ihr

def FormulaPure (p : Formula) : Prop :=
  ∀ op a b, FormulaOp.compare op a b ∈ p.code → IntegerPure a ∧ IntegerPure b

@[simp] theorem pure_truth : FormulaPure .truth := by intro op a b h; simp [Formula.truth] at h
@[simp] theorem pure_falsity : FormulaPure .falsity := by intro op a b h; simp [Formula.falsity] at h
@[simp] theorem pure_equal (a b : Rel) : FormulaPure (.equal a b) := by intro op x y h; simp [Formula.equal] at h
@[simp] theorem pure_subset (a b : Rel) : FormulaPure (.subset a b) := by intro op x y h; simp [Formula.subset] at h
@[simp] theorem pure_mult (m : Backend.Alloy.Multiplicity) (r : Rel) : FormulaPure (.mult m r) := by intro op x y h; simp [Formula.mult] at h
@[simp] theorem pure_compare (op : Backend.Alloy.Comparison) (a b : Integer) :
    FormulaPure (.compare op a b) ↔ IntegerPure a ∧ IntegerPure b := by
  simp only [FormulaPure, Formula.compare, List.mem_singleton, FormulaOp.compare.injEq]
  aesop
@[simp] theorem pure_unary (op : Unary) (p : Formula) :
    FormulaPure (.unary op p) ↔ FormulaPure p := by simp [FormulaPure, Formula.unary]
@[simp] theorem pure_binary (op : Binary) (p q : Formula) :
    FormulaPure (.binary op p q) ↔ FormulaPure p ∧ FormulaPure q := by
  constructor
  · intro h
    exact ⟨fun o a b hm => h o a b (by simp [Formula.binary, hm]),
      fun o a b hm => h o a b (by simp [Formula.binary, hm])⟩
  · rintro ⟨hp, hq⟩ o a b hm
    have member : FormulaOp.compare o a b ∈ p.code ∨ FormulaOp.compare o a b ∈ q.code := by
      simpa [Formula.binary] using hm
    exact member.elim (hp o a b) (hq o a b)
@[simp] theorem pure_all (r : Rel) (p : Formula) :
    FormulaPure (.all r p) ↔ FormulaPure p := by simp [FormulaPure, Formula.all]
@[simp] theorem pure_exists (r : Rel) (p : Formula) :
    FormulaPure (.exists_ r p) ↔ FormulaPure p := by simp [FormulaPure, Formula.exists_]

theorem checked_self {a b : IntRange} (h : a.checked w = some b) :
    a = b ∧ b.checked w = some b := by
  obtain ⟨rfl, _⟩ := (Backend.Alloy.IntRange.checked_iff _ _ _).mp h
  exact ⟨rfl, h⟩

theorem range_binary (op : IR.BehavioralArithmetic.Binary) (ha : Arithmetic.Term a) (hb : Arithmetic.Term b) :
    (Backend.Alloy.Behavioral.Arithmetic.binary op a b).range m = (do
      let ra ← a.range m
      let rb ← b.range m
      if op.nonzero (Arithmetic.interval rb) then
        (Arithmetic.targetInterval (op.range (Arithmetic.interval ra) (Arithmetic.interval rb))).checked m.command.bitwidth
      else none) := by
  unfold Integer.range
  rw [Arithmetic.fold_binary op ha hb]
  cases op <;> simp [Arithmetic.applyAlgebra, IR.BehavioralArithmetic.Binary.nonzero,
    IR.BehavioralArithmetic.Binary.range, IR.BehavioralArithmetic.symmetric,
    IR.BehavioralArithmetic.magnitude, Arithmetic.targetInterval,
    IR.Expr.Interval.add, IR.Expr.Interval.subtract, quotientRange, nonzero, symmetric, magnitude]

theorem scalarValue_range (order : lo ≤ hi) (rows : Relation) :
    (IR.Expr.Interval.mk lo hi).Contains (scalarValue lo hi rows) := by
  change lo ≤ scalarValue lo hi rows ∧ scalarValue lo hi rows ≤ hi
  unfold scalarValue
  split <;> try exact ⟨le_refl _, order⟩
  split
  · rename_i h
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
  · exact ⟨le_refl _, order⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Successful target admission gives total arithmetic on every trace and
lexical environment, including alternatives whose guard is false. -/
theorem IntegerPure.range_total (h : IntegerPure n) (safe : n.range m = some r) :
    r.checked m.command.bitwidth = some r ∧
      ∀ (τ : Trace) (e : Environment) (t : Nat), ∃ z,
        n.eval m.schema m.command.bitwidth τ e t = some z ∧ (Arithmetic.interval r).Contains z := by
  induction h generalizing r with
  | literal z =>
    change (IntRange.mk z z).checked m.command.bitwidth = some r at safe
    obtain ⟨rfl, checked⟩ := checked_self safe
    refine ⟨checked, fun τ e t => ⟨z, ?_, le_refl _, le_refl _⟩⟩
    exact (Backend.Alloy.boundedInt_some_iff _ _).mpr
      (interval_fits_value _ ((Arithmetic.checked_fits _ _).mp checked) ⟨le_refl _, le_refl _⟩)
  | scalar lo hi relation =>
    change (if relation.safe m then (IntRange.mk lo hi).checked m.command.bitwidth else none) = some r at safe
    split at safe
    · obtain ⟨rfl, checked⟩ := checked_self safe
      have order := (Backend.Alloy.IntRange.checked_iff _ _ _).mp checked |>.2.1
      refine ⟨checked, fun τ e t => ⟨scalarValue lo hi (relation.eval m.schema m.command.bitwidth τ e t), ?_, scalarValue_range order _⟩⟩
      exact (Backend.Alloy.boundedInt_some_iff _ _).mpr
        (interval_fits_value _ ((Arithmetic.checked_fits _ _).mp checked) (scalarValue_range order _))
    · contradiction
  | @binary a b op ha hb ia ib =>
    rw [range_binary op ha.term hb.term] at safe
    cases left : a.range m with
    | none => simp [left] at safe
    | some ra =>
      cases right : b.range m with
      | none => simp [left, right] at safe
      | some rb =>
        simp only [left, right, bind, Option.bind] at safe
        split at safe
        · rename_i nonzero
          obtain ⟨rfl, checked⟩ := checked_self safe
          obtain ⟨leftChecked, leftValues⟩ := ia left
          obtain ⟨rightChecked, rightValues⟩ := ib right
          have certified : IR.BehavioralArithmetic.Checked op m.command.bitwidth
              (Arithmetic.interval ra) (Arithmetic.interval rb) :=
            ⟨⟨(Arithmetic.checked_fits _ _).mp leftChecked, (Arithmetic.checked_fits _ _).mp rightChecked⟩,
              nonzero, (Arithmetic.checked_fits _ _).mp checked⟩
          refine ⟨checked, ?_⟩
          intro τ e t
          obtain ⟨x, hx, bx⟩ := leftValues τ e t
          obtain ⟨y, hy, by'⟩ := rightValues τ e t
          obtain ⟨z, scalar, eval⟩ := Arithmetic.represented_binary op ha.term hb.term
            m.schema m.command.bitwidth τ e t _ _ certified x y bx by' hx hy
          have scalarIR : op.apply x y = some z := by
            have bridge := SemanticsBridge.BehavioralArithmetic.scalar_agrees op (some x) (some y)
            exact bridge.trans scalar
          exact ⟨z, eval, SemanticsBridge.BehavioralArithmetic.range_contains op bx by' scalarIR⟩
        · contradiction

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem formula_defined (built : p.Built) (pure : FormulaPure p) (safe : p.safe m = true)
    (τ : Trace) (e : Environment) (t : Nat) :
    p.Defined m.schema m.command.bitwidth τ e t := by
  induction built generalizing e t with
  | truth => trivial
  | falsity => trivial
  | equal => trivial
  | subset => trivial
  | mult => trivial
  | compare op a b =>
    have pure := (pure_compare _ _ _).mp pure
    change ((a.range m).isSome && (b.range m).isSome) = true at safe
    have both : (a.range m).isSome = true ∧ (b.range m).isSome = true := by simpa only [Bool.and_eq_true] using safe
    obtain ⟨left, right⟩ := both
    obtain ⟨ra, har⟩ := Option.isSome_iff_exists.mp left
    obtain ⟨rb, hbr⟩ := Option.isSome_iff_exists.mp right
    obtain ⟨x, hx, _⟩ := (pure.1.range_total har).2 τ e t
    obtain ⟨y, hy, _⟩ := (pure.2.range_total hbr).2 τ e t
    change (a.eval _ _ _ _ _).isSome = true ∧ (b.eval _ _ _ _ _).isSome = true
    simp [hx, hy]
  | @unary op p hp ih =>
    have safe' : p.safe m = true := by
      unfold Formula.safe at safe ⊢
      simpa only [Formula.fold_unary _ _ _ _ hp] using safe
    have ih' : ∀ e t, p.fold (definedAlgebra m.schema m.command.bitwidth τ) (fun _ _ => False) e t :=
      ih ((pure_unary _ _).mp pure) safe'
    unfold Formula.Defined
    rw [Formula.fold_unary _ _ _ _ hp]
    cases op <;> dsimp only [definedAlgebra]
    all_goals first | exact ih' _ _ | exact fun _ _ => ih' _ _
  | @binary op p q hp hq ihp ihq =>
    have safe' : p.safe m = true ∧ q.safe m = true := by
      unfold Formula.safe at safe ⊢
      simpa only [Formula.fold_binary _ _ _ _ _ hp hq, Bool.and_eq_true] using safe
    have pure' := (pure_binary _ _ _).mp pure
    have ihp' : ∀ e t, p.fold (definedAlgebra m.schema m.command.bitwidth τ) (fun _ _ => False) e t :=
      ihp pure'.1 safe'.1
    have ihq' : ∀ e t, q.fold (definedAlgebra m.schema m.command.bitwidth τ) (fun _ _ => False) e t :=
      ihq pure'.2 safe'.2
    unfold Formula.Defined
    rw [Formula.fold_binary _ _ _ _ _ hp hq]
    cases op <;> dsimp only [definedAlgebra]
    all_goals first | exact ⟨ihp' _ _, ihq' _ _⟩ | exact fun _ _ => ⟨ihp' _ _, ihq' _ _⟩
  | @all r p hp ih =>
    have safe' : p.safe m = true := by
      unfold Formula.safe at safe ⊢
      rw [Formula.fold_all _ _ _ hp] at safe
      have both : r.safe m = true ∧ p.safe m = true := by simpa only [Formula.safe, Bool.and_eq_true] using safe
      exact both.2
    have ih' : ∀ e t, p.fold (definedAlgebra m.schema m.command.bitwidth τ) (fun _ _ => False) e t :=
      ih ((pure_all _ _).mp pure) safe'
    unfold Formula.Defined
    rw [Formula.fold_all _ _ _ hp]
    exact fun _ _ => ih' _ _
  | @exists_ r p hp ih =>
    have safe' : p.safe m = true := by
      unfold Formula.safe at safe ⊢
      rw [Formula.fold_exists _ _ _ hp] at safe
      have both : r.safe m = true ∧ p.safe m = true := by simpa only [Formula.safe, Bool.and_eq_true] using safe
      exact both.2
    have ih' : ∀ e t, p.fold (definedAlgebra m.schema m.command.bitwidth τ) (fun _ _ => False) e t :=
      ih ((pure_exists _ _).mp pure) safe'
    unfold Formula.Defined
    rw [Formula.fold_exists _ _ _ hp]
    exact fun _ _ => ih' _ _

end ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
