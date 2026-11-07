module

public import ClaferCompiler.Correctness.Behavioral.SnapshotRelations

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral

inductive SnapshotInteger : Alloy.Integer → Prop where
  | literal (n) : SnapshotInteger (.literal n)
  | count : SnapshotRel r → SnapshotInteger (.count r)

/-- The actual structural formula grammar. The domain condition concerns tuple
arity only; it is supplied by snapshot table well-formedness. -/
inductive SnapshotFormula (i : Instance) : Alloy.Formula → Prop where
  | truth : SnapshotFormula i .truth
  | equal : SnapshotRel a → SnapshotRel b → SnapshotFormula i (.equal a b)
  | subset : SnapshotRel a → SnapshotRel b → SnapshotFormula i (.subset a b)
  | mult (m) : SnapshotRel r → SnapshotFormula i (.mult m r)
  | compare (op) : SnapshotInteger a → SnapshotInteger b → SnapshotFormula i (.compare op a b)
  | conj : SnapshotFormula i a → SnapshotFormula i b → SnapshotFormula i (.conj a b)
  | key : SnapshotRel a → SnapshotRel b → SnapshotRel c → SnapshotRel d →
      SnapshotFormula i (.implies (.equal a b) (.equal c d))
  | all : SnapshotRel r → (∀ env row, row ∈ r.eval i env → ∃ x, row = [x]) →
      SnapshotFormula i p → SnapshotFormula i (.all r p)

theorem SnapshotFormula.term (h : SnapshotFormula i p) : p.Term := by
  induction h with
  | truth => exact .truth
  | equal => exact .equal _ _
  | subset => exact .subset _ _
  | mult => exact .mult _ _
  | compare => exact .compare _ _ _
  | conj _ _ ia ib => exact .conj ia ib
  | key => exact .implies (.equal _ _) (.equal _ _)
  | all _ _ _ ih => exact .all _ ih

theorem snapshotFormula_built (v : IR.Structural.Layout k) (h : SnapshotFormula i p) :
    (snapshotFormula v p).Built := by
  induction h with
  | truth => exact .truth
  | equal => exact .equal _ _
  | subset => exact .subset _ _
  | mult => exact .mult _ _
  | compare => exact .compare _ _ _
  | conj ha hb ia ib =>
    unfold snapshotFormula
    rw [Formula.fold_conj_term ha.term hb.term]
    exact .binary .conj ia ib
  | key =>
    unfold snapshotFormula
    rw [Formula.fold_implies_term (.equal _ _) (.equal _ _)]
    exact .binary .implies (.equal _ _) (.equal _ _)
  | all _ _ hp ih =>
    unfold snapshotFormula
    rw [Formula.fold_all_term hp.term]
    exact .all _ ih

theorem snapshotFormula_conj (v : IR.Structural.Layout k)
    (ha : SnapshotFormula i a) (hb : SnapshotFormula i b) :
    snapshotFormula v (.conj a b) =
      Temporal.Formula.binary .conj (snapshotFormula v a) (snapshotFormula v b) :=
  Formula.fold_conj_term ha.term hb.term _ _

theorem snapshotFormula_all (v : IR.Structural.Layout k) (r : Rel)
    (hp : SnapshotFormula i p) :
    snapshotFormula v (.all r p) =
      Temporal.Formula.all (snapshotRel v r) (snapshotFormula v p) :=
  Formula.fold_all_term hp.term _ _ r

theorem objectRows_subset (a b : Alloy.Relation) :
    (∀ row, row ∈ objectRows a → row ∈ objectRows b) ↔ relationSubset a b = true := by
  simp only [relationSubset, List.all_eq_true, List.contains_iff_mem, objectRows]
  constructor
  · intro h row hr
    have hm := h (row.map Temporal.Atom.object) (List.mem_map.mpr ⟨row, hr, rfl⟩)
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    exact objectRow_injective he ▸ hr
  · intro h row hr
    obtain ⟨r, ha, he⟩ : ∃ r ∈ a, r.map Temporal.Atom.object = row := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨r, h r ha, he⟩

theorem objectRows_equal (a b : Alloy.Relation) :
    (∀ row, row ∈ objectRows a ↔ row ∈ objectRows b) ↔
      (relationSubset a b && relationSubset b a) = true := by
  rw [Bool.and_eq_true, ← objectRows_subset, ← objectRows_subset]
  exact ⟨fun h => ⟨fun row => (h row).mp, fun row => (h row).mpr⟩,
    fun ⟨h, g⟩ row => ⟨h row, g row⟩⟩

theorem objectRows_all (rows : Alloy.Relation)
    (unary : ∀ row ∈ rows, ∃ x, row = [x]) (p : Temporal.Atom → Prop) :
    (∀ x, [x] ∈ objectRows rows → p x) ↔
      ∀ row ∈ rows, p (.object (row.headD 0)) := by
  constructor
  · intro h row hr
    obtain ⟨x, rfl⟩ := unary row hr
    exact h (.object x) (List.mem_map.mpr ⟨[x], hr, rfl⟩)
  · intro h x hx
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hx
    obtain ⟨y, rfl⟩ := unary row hr
    have he : Temporal.Atom.object y = x := by simpa using he
    simpa only [List.headD_cons, he] using h [y] hr

theorem snapshotInteger_eval (v : IR.Structural.Layout k) (h : SnapshotInteger a)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (t : Nat) (i : Instance)
    (signatures : ∀ n env, (snapshotRel v (.sig n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.sig n).eval i env))
    (fields : ∀ n env, (snapshotRel v (.field n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.field n).eval i env)) (env : List Nat) :
    (snapshotInteger v a).eval s w τ (env.map .object) t = a.eval w i env := by
  cases h with
  | literal n => rfl
  | count h =>
    change boundedInt w (Int.ofNat ((snapshotRel v _).eval s w τ (env.map .object) t).eraseDups.length) =
      boundedInt w (Int.ofNat (Rel.eval i env _).eraseDups.length)
    rw [snapshotRel_eval v h s w τ t i signatures fields env, objectRows_dedup]
    simp

-- [proof->req~compiler-behavioral-correctness~1]
/-- Every emitted M1 clause retains both strict definedness and truth when
substituted into a temporal snapshot. Integer overflow is never erased. -/
theorem snapshotFormula_eval (v : IR.Structural.Layout k) (h : SnapshotFormula i p)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (t : Nat)
    (signatures : ∀ n env, (snapshotRel v (.sig n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.sig n).eval i env))
    (fields : ∀ n env, (snapshotRel v (.field n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.field n).eval i env)) (env : List Nat) :
    ((snapshotFormula v p).Defined s w τ (env.map .object) t ∧
      (snapshotFormula v p).Holds s w τ (env.map .object) t) ↔ p.eval w i env = some true := by
  induction h generalizing env with
  | truth => simp [snapshotFormula, Formula.fold, Formula.truth, FormulaAlgebra.step,
      Temporal.Formula.Defined, Temporal.Formula.Holds, Temporal.Formula.fold,
      Temporal.Formula.truth, Temporal.FormulaAlgebra.step, Temporal.definedAlgebra,
      Temporal.formulaAlgebra, Formula.eval]
  | equal ha hb =>
    change (True ∧ (∀ row, row ∈ (snapshotRel v _).eval s w τ (env.map .object) t ↔
      row ∈ (snapshotRel v _).eval s w τ (env.map .object) t)) ↔
      some (relationSubset (Rel.eval i env _) (Rel.eval i env _) &&
        relationSubset (Rel.eval i env _) (Rel.eval i env _)) = some true
    rw [snapshotRel_eval v ha s w τ t i signatures fields,
      snapshotRel_eval v hb s w τ t i signatures fields]
    simpa using objectRows_equal (Rel.eval i env _) (Rel.eval i env _)
  | subset ha hb =>
    change (True ∧ (∀ row, row ∈ (snapshotRel v _).eval s w τ (env.map .object) t →
      row ∈ (snapshotRel v _).eval s w τ (env.map .object) t)) ↔
      some (relationSubset (Rel.eval i env _) (Rel.eval i env _)) = some true
    rw [snapshotRel_eval v ha s w τ t i signatures fields,
      snapshotRel_eval v hb s w τ t i signatures fields]
    simpa using objectRows_subset (Rel.eval i env _) (Rel.eval i env _)
  | mult m hr =>
    change (True ∧ m.holds ((snapshotRel v _).eval s w τ (env.map .object) t).eraseDups.length = true) ↔
      some (m.holds (Rel.eval i env _).eraseDups.length) = some true
    rw [snapshotRel_eval v hr s w τ t i signatures fields, objectRows_dedup]
    simp
  | compare op ha hb =>
    change ((Temporal.Integer.eval s w τ (env.map .object) t (snapshotInteger v _)).isSome = true ∧
      (Temporal.Integer.eval s w τ (env.map .object) t (snapshotInteger v _)).isSome = true) ∧
      (∃ x y, Temporal.Integer.eval s w τ (env.map .object) t (snapshotInteger v _) = some x ∧
        Temporal.Integer.eval s w τ (env.map .object) t (snapshotInteger v _) = some y ∧
        op.holds x y = true) ↔
      (do
        let x ← Alloy.Integer.eval w i env _
        let y ← Alloy.Integer.eval w i env _
        pure (op.holds x y)) = some true
    rw [snapshotInteger_eval v ha s w τ t i signatures fields,
      snapshotInteger_eval v hb s w τ t i signatures fields]
    cases Alloy.Integer.eval w i env _ <;> cases Alloy.Integer.eval w i env _ <;> simp
  | conj ha hb ia ib =>
    rw [snapshotFormula_conj v ha hb, Formula.eval_conj_true ha.term hb.term]
    simp only [Temporal.Formula.Defined, Temporal.Formula.Holds,
      Temporal.Formula.fold_binary _ _ _ _ _ (snapshotFormula_built v ha) (snapshotFormula_built v hb)]
    change (_ ∧ _) ∧ (_ ∧ _) ↔ _
    exact (and_and_and_comm).trans (and_congr (ia env) (ib env))
  | key ha hb hc hd =>
    have eqH (a b : Rel) (ha : SnapshotRel a) (hb : SnapshotRel b) :
        (Temporal.formulaAlgebra s w τ).equal (snapshotRel v a) (snapshotRel v b) (env.map .object) t ↔
          (relationSubset (a.eval i env) (b.eval i env) &&
            relationSubset (b.eval i env) (a.eval i env)) = true := by
      change (∀ row, row ∈ (snapshotRel v a).eval s w τ (env.map .object) t ↔
        row ∈ (snapshotRel v b).eval s w τ (env.map .object) t) ↔ _
      rw [snapshotRel_eval v ha s w τ t i signatures fields,
        snapshotRel_eval v hb s w τ t i signatures fields]
      exact objectRows_equal _ _
    simp only [snapshotFormula, Formula.fold_implies_term (.equal _ _) (.equal _ _),
      Temporal.Formula.Defined, Temporal.Formula.Holds,
      Formula.eval]
    change (True ∧ True) ∧ (_ → _) ↔ some (!_ || _) = some true
    rw [eqH _ _ ha hb, eqH _ _ hc hd]
    simp only [true_and, Option.some.injEq, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    tauto
  | all hr unary hp ih =>
    rw [snapshotFormula_all v _ hp, Formula.eval_all_true hp.term]
    simp only [Temporal.Formula.Defined, Temporal.Formula.Holds,
      Temporal.Formula.fold_all _ _ _ (snapshotFormula_built v hp)]
    change ((∀ x, [x] ∈ (snapshotRel v _).eval s w τ (env.map .object) t → _) ∧
      (∀ x, [x] ∈ (snapshotRel v _).eval s w τ (env.map .object) t → _)) ↔ _
    rw [snapshotRel_eval v hr s w τ t i signatures fields]
    rw [objectRows_all _ (unary env), objectRows_all _ (unary env)]
    constructor
    · rintro ⟨hd, hh⟩ row hrow
      exact (ih (row.headD 0 :: env)).mp ⟨hd row hrow, hh row hrow⟩
    · intro h
      exact ⟨fun row hrow => ((ih (row.headD 0 :: env)).mpr (h row hrow)).1,
        fun row hrow => ((ih (row.headD 0 :: env)).mpr (h row hrow)).2⟩

end ClaferCompiler.Correctness.Behavioral
