module

public import ClaferCompiler.Correctness.PipelineCorrectness

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open ExpressionMeaning ExpressionRelations ExpressionConstruction Expressions

/-- Total functional scalar rows with in-range, injective values satisfy the
actual generated range/identity formulae. The premises are finite data only. -/
theorem scalarFacts_complete (i : Instance) (w owner : Nat) (range : Interval)
    (hrange : range.fits w = true)
    (typed : ∀ row ∈ i.values[owner]?.getD [], range.Contains row.2)
    (keys : ((i.values[owner]?.getD []).map Prod.fst).Nodup)
    (total : ∀ a ∈ i.signatures[owner]?.getD [], ∃ z, (a,z) ∈ i.values[owner]?.getD [])
    (unique : ∀ row ∈ i.values[owner]?.getD [], ∀ other ∈ i.values[owner]?.getD [],
      row.2 = other.2 → row.1 = other.1) :
    ∀ fact ∈ scalarFacts owner w range, fact.eval w i [] = some true := by
  obtain ⟨hlo,hhi⟩ := interval_target_endpoints range w hrange
  have fits (a : Nat) (z : Int) (hz : (a,z) ∈ i.values[owner]?.getD []) : fitsInt w z = true := by
    have h := typed (a,z) hz
    have hrange := hrange
    simp only [Interval.fits,decide_eq_true_eq] at hrange
    simp only [Interval.Contains] at h
    exact (boundedInt_some_iff w z).mp (source_range_target_int ⟨hrange.1,hrange.2.1⟩
      ⟨hrange.2.2.2.1.trans h.1,h.2.trans hrange.2.2.2.2⟩)
  intro fact hf
  simp only [scalarFacts,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl
  · rw [Formula.eval_all_true (.conj (.compare _ _ _) (.compare _ _ _))]
    intro tuple ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    obtain ⟨z,hz⟩ := total a ha
    rw [Formula.eval_conj_true (.compare _ _ _) (.compare _ _ _)]
    have hr := scalar_eval_row i w owner keys hz (fits a z hz) [a] (.var 0) rfl
    change (do let x ← boundedInt w range.lower
               let y ← (scalarAt owner w 0).eval w i [a]
               pure (Comparison.le.holds x y)) = some true ∧
      (do let x ← (scalarAt owner w 0).eval w i [a]
          let y ← boundedInt w range.upper
          pure (Comparison.le.holds x y)) = some true
    rw [hlo,hhi,show (scalarAt owner w 0).eval w i [a] = some z from hr]
    simpa [Comparison.holds,Interval.Contains] using typed (a,z) hz
  · rw [Formula.eval_all_true (.all _ (.implies (.compare _ _ _) (.equal _ _)))]
    intro tuple ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    obtain ⟨z,hz⟩ := total a ha
    rw [Formula.eval_all_true (.implies (.compare _ _ _) (.equal _ _))]
    intro tuple ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨z',hz'⟩ := total b hb
    rw [eval_implies (.compare _ _ _) (.equal _ _)]
    have hra := scalar_eval_row i w owner keys hz (fits a z hz) [b,a] (.var 1) rfl
    have hrb := scalar_eval_row i w owner keys hz' (fits b z' hz') [b,a] (.var 0) rfl
    change (do
      let x ← (do
        let x ← (scalarAt owner w 1).eval w i [b,a]
        let y ← (scalarAt owner w 0).eval w i [b,a]
        pure (Comparison.eq.holds x y))
      let y ← some (relationSubset [[a]] [[b]] && relationSubset [[b]] [[a]])
      pure (!x || y)) = some true
    rw [show (scalarAt owner w 1).eval w i [b,a] = some z from hra,
      show (scalarAt owner w 0).eval w i [b,a] = some z' from hrb]
    by_cases he : z = z'
    · have hab : a = b := unique (a,z) hz (b,z') hz' he
      simp [Comparison.holds,relationSubset,he,hab]
    · simp [Comparison.holds,he]

/-- Converse membership through the library traversal. -/
theorem flatMapM_origin {α β ε : Type} (f : α → Except ε (List β))
    (xs : List α) {ys : List β} (h : xs.flatMapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, ∃ zs, f x = .ok zs ∧ y ∈ zs := by
  induction xs generalizing ys with
  | nil => simp only [List.flatMapM_nil,pure,Except.pure,Except.ok.injEq] at h; subst ys; simp at hy
  | cons a as ih =>
    rw [List.flatMapM_cons] at h
    cases ha : f a with
    | error e => simp [ha,bind,Except.bind] at h
    | ok zs =>
      cases ht : as.flatMapM f with
      | error e => simp [ha,ht,bind,Except.bind] at h
      | ok tail =>
        simp only [ha,ht,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
        subst ys
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨a,List.mem_cons_self,zs,ha,hy⟩
        · obtain ⟨x,hx,zs,hf,hy⟩ := ih ht hy
          exact ⟨x,List.mem_cons_of_mem _ hx,zs,hf,hy⟩

theorem numericFacts_origin (v : IR.Inherited.Validated n) (b : Structural.Bounds)
    (ranges : Vector Interval n) (facts : List Formula) (h : numericFacts v b ranges = .ok facts)
    (fact : Formula) (hf : fact ∈ facts) :
    ∃ d : Fin n, (v.core.structural.get d).origin = .integer ∧ ranges[d].fits b.bitwidth = true ∧
      fact ∈ scalarFacts (Structural.signatureId v.layout d) b.bitwidth ranges[d] := by
  obtain ⟨d,_,fs,he,hmem⟩ := flatMapM_origin _ _ h hf
  by_cases hd : (v.core.structural.get d).origin = .integer
  · simp only [hd,beq_self_eq_true,bne,Bool.not_true,Bool.false_eq_true,↓reduceIte] at he
    split at he
    · simp [throw,bind,Except.bind,pure,Except.pure] at he
    · rename_i hfit
      have he' : fs = scalarFacts (Structural.signatureId v.layout d) b.bitwidth ranges[d] := by
        simpa [pure,Except.pure] using he.symm
      exact ⟨d,hd,by simpa using hfit,he' ▸ hmem⟩
  · simp [hd,pure,Except.pure] at he
    subst fs
    simp at hmem

end ClaferCompiler.Correctness.Pipeline
