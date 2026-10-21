module

public import ClaferCompiler.Correctness.ExpressionAttachments
public import Mathlib.Data.List.Nodup

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction Expressions

theorem scalar_field_rows (i : Instance) (w : Nat) (schema : Schema)
    (owner : Nat) (decl : Signature) (hd : schema.signatures[owner]? = some decl)
    (hscalar : decl.scalar = true) (hs : i.scalarFields w schema = true) :
    (∀ row ∈ i.values[owner]?.getD [], row.1 ∈ i.signatures[owner]?.getD [] ∧ fitsInt w row.2 = true) ∧
    ((i.values[owner]?.getD []).map Prod.fst).Nodup ∧
    ∀ a ∈ i.signatures[owner]?.getD [], ∃ z, (a, z) ∈ i.values[owner]?.getD [] := by
  have h := List.all_eq_true.mp hs (decl, owner) (List.mk_mem_zipIdx_iff_getElem?.mpr hd)
  simp only [hscalar, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro a ha
  obtain ⟨row, hr, he⟩ := h.2 a ha
  exact ⟨row.2, he ▸ hr⟩

theorem scalar_eval_row (i : Instance) (w : Nat) (owner : Nat)
    (hrows : ((i.values[owner]?.getD []).map Prod.fst).Nodup)
    {a : Nat} {z : Int} (hz : (a, z) ∈ i.values[owner]?.getD []) (hfit : fitsInt w z = true)
    (env : List Nat) (r : Rel) (hr : r.eval i env = [[a]]) :
    (Integer.scalar owner (minInt w) (maxInt w) r).eval w i env = some z := by
  have hvals : (((i.values[owner]?.getD []).filter (fun row => row.1 == a)).map Prod.snd).eraseDups = [z] := by
    apply dedup_singleton
    intro value
    simp only [List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨row, ⟨hrow, he⟩, rfl⟩
      have heq : row = (a, z) := List.inj_on_of_nodup_map hrows hrow hz he
      exact congrArg Prod.snd heq
    · intro he
      subst value
      exact ⟨(a, z), ⟨hz, rfl⟩, rfl⟩
  have hlohi : minInt w ≤ z ∧ z ≤ maxInt w := by
    simp only [fitsInt, Bool.and_eq_true, decide_eq_true_eq] at hfit
    exact ⟨hfit.1.2, hfit.2⟩
  change boundedInt w (i.scalarValue env owner (minInt w) (maxInt w) r) = some z
  simp only [Instance.scalarValue, hr, List.eraseDups_cons, List.filter_nil, List.eraseDups_nil, hvals]
  simp only [hlohi.1, hlohi.2, decide_true, Bool.and_self, ↓reduceIte]
  exact (boundedInt_some_iff w z).mpr hfit

theorem interval_target_endpoints (range : Interval) (w : Nat) (h : range.fits w = true) :
    boundedInt w range.lower = some range.lower ∧ boundedInt w range.upper = some range.upper := by
  simp only [Interval.fits, decide_eq_true_eq] at h
  constructor
  · exact source_range_target_int ⟨h.1, h.2.1⟩ ⟨h.2.2.2.1, h.2.2.1.trans h.2.2.2.2⟩
  · exact source_range_target_int ⟨h.1, h.2.1⟩ ⟨h.2.2.2.1.trans h.2.2.1, h.2.2.2.2⟩

/-- Generated scalar facts enforce the declared mathematical interval and unique
integer identity. Field admission supplies total, typed, functional rows; neither
source truth nor the constructor preservation theorem is a premise here. -/
theorem scalarFacts_enforce (i : Instance) (w : Nat) (schema : Schema)
    (owner : Nat) (decl : Signature) (hd : schema.signatures[owner]? = some decl)
    (hscalar : decl.scalar = true) (hs : i.scalarFields w schema = true)
    (range : Interval) (hrange : range.fits w = true)
    (hfacts : ∀ fact ∈ scalarFacts owner w range, fact.eval w i [] = some true) :
    (∀ row ∈ i.values[owner]?.getD [], range.Contains row.2) ∧
      ∀ row ∈ i.values[owner]?.getD [], ∀ other ∈ i.values[owner]?.getD [],
        row.2 = other.2 → row.1 = other.1 := by
  obtain ⟨htyped, hkeys, _⟩ := scalar_field_rows i w schema owner decl hd hscalar hs
  obtain ⟨hlo, hhi⟩ := interval_target_endpoints range w hrange
  have hbound := hfacts _ (by unfold scalarFacts; exact List.mem_cons_self)
  have hinj := hfacts _ (by unfold scalarFacts; exact List.mem_cons_of_mem _ List.mem_cons_self)
  rw [Formula.eval_all_true (.conj (.compare _ _ _) (.compare _ _ _))] at hbound
  rw [Formula.eval_all_true (.all _ (.implies (.compare _ _ _) (.equal _ _)))] at hinj
  constructor
  · rintro ⟨a, z⟩ hz
    have hat := htyped (a, z) hz
    have hp := hbound [a] (by simpa using hat.1)
    rw [Formula.eval_conj_true (.compare _ _ _) (.compare _ _ _)] at hp
    have hr := scalar_eval_row i w owner hkeys hz hat.2 [a] (.var 0) rfl
    change (do let x ← boundedInt w range.lower
               let y ← (scalarAt owner w 0).eval w i [a]
               pure (Comparison.le.holds x y)) = some true ∧
      (do let x ← (scalarAt owner w 0).eval w i [a]
          let y ← boundedInt w range.upper
          pure (Comparison.le.holds x y)) = some true at hp
    rw [hlo, hhi, show (scalarAt owner w 0).eval w i [a] = some z from hr] at hp
    simpa [Comparison.holds, Interval.Contains] using hp
  · rintro ⟨a, z⟩ ha ⟨b, z'⟩ hb he
    have hat := htyped (a, z) ha
    have hbt := htyped (b, z') hb
    have hp := hinj [a] (by simpa using hat.1)
    rw [Formula.eval_all_true (.implies (.compare _ _ _) (.equal _ _))] at hp
    have hpp := hp [b] (by simpa using hbt.1)
    rw [eval_implies (.compare _ _ _) (.equal _ _)] at hpp
    have hra := scalar_eval_row i w owner hkeys ha hat.2 [b, a] (.var 1) rfl
    have hrb := scalar_eval_row i w owner hkeys hb hbt.2 [b, a] (.var 0) rfl
    change (do
      let x ← (do let x ← (scalarAt owner w 1).eval w i [b, a]
                  let y ← (scalarAt owner w 0).eval w i [b, a]
                  pure (Comparison.eq.holds x y))
      let y ← some (relationSubset [[a]] [[b]] && relationSubset [[b]] [[a]])
      pure (!x || y)) = some true at hpp
    rw [show (scalarAt owner w 1).eval w i [b, a] = some z from hra,
      show (scalarAt owner w 0).eval w i [b, a] = some z' from hrb] at hpp
    change z = z' at he
    have hab : a = b ∧ b = a := by simpa [Comparison.holds, relationSubset, he] using hpp
    exact hab.1

/-- Membership through the standard concatenating traversal, retaining the
successful result for the selected input. -/
theorem flatMapM_member {α β ε : Type} (f : α → Except ε (List β))
    (xs : List α) {ys : List β} (h : xs.flatMapM f = .ok ys) {x : α} (hx : x ∈ xs) :
    ∃ zs, f x = .ok zs ∧ ∀ z ∈ zs, z ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a as ih =>
    rw [List.flatMapM_cons] at h
    cases ha : f a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok zs =>
      cases ht : as.flatMapM f with
      | error e => simp [ha, ht, bind, Except.bind] at h
      | ok tail =>
        simp only [ha, ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst ys
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨zs, ha, fun z hz => List.mem_append_left _ hz⟩
        · obtain ⟨zs', hf, hm⟩ := ih ht hx
          exact ⟨zs', hf, fun z hz => List.mem_append_right _ (hm z hz)⟩

theorem numericFacts_member (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (facts : List Formula)
    (h : numericFacts v bounds intervals = .ok facts) (d : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) :
    intervals[d].fits bounds.bitwidth = true ∧
      ∀ f ∈ scalarFacts (Structural.signatureId v.layout d) bounds.bitwidth intervals[d], f ∈ facts := by
  obtain ⟨fs, hf, hm⟩ := flatMapM_member _ _ h (List.mem_finRange d)
  simp only [hd, beq_self_eq_true, bne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · simp [throw, bind, Except.bind, pure, Except.pure] at hf
  · rename_i hfit
    have he : fs = scalarFacts (Structural.signatureId v.layout d) bounds.bitwidth intervals[d] := by
      simpa [pure, Except.pure] using hf.symm
    exact ⟨by simpa using hfit, he ▸ hm⟩

/-- Accepted module satisfaction discharges the generated range and identity
facts. The only schema premises identify the declared scalar field. -/
theorem compiled_scalar_enforcement (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v bounds intervals bodies = .ok out) (i : Instance)
    (hs : Satisfies out.module.raw i) (d : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) (decl : Signature)
    (hdecl : out.module.raw.schema.signatures[Structural.signatureId v.layout d]? = some decl)
    (hscalar : decl.scalar = true) :
    (∀ row ∈ i.values[Structural.signatureId v.layout d]?.getD [], intervals[d].Contains row.2) ∧
      ∀ row ∈ i.values[Structural.signatureId v.layout d]?.getD [],
        ∀ other ∈ i.values[Structural.signatureId v.layout d]?.getD [],
          row.2 = other.2 → row.1 = other.1 := by
  obtain ⟨base, hb, _, hn, hfacts, hcommand⟩ := compile_output v bounds intervals bodies out h
  obtain ⟨scopes, _, hbase, _, _⟩ := Correctness.Inherited.compile_output v bounds base hb
  have hwidth : out.module.raw.command.bitwidth = bounds.bitwidth := by rw [hcommand, hbase]; rfl
  obtain ⟨hfit, hmem⟩ := numericFacts_member v bounds intervals out.numericFacts hn d hd
  have heval := hs.2.2.2.2.2
  have hfields : i.scalarFields bounds.bitwidth out.module.raw.schema = true := by
    unfold Module.eval at heval
    cases hf : out.module.raw.facts.mapM (fun f => f.eval out.module.raw.command.bitwidth i []) with
    | none => simp [hf] at heval
    | some fs =>
      cases hc : out.module.raw.command.body.eval out.module.raw.command.bitwidth i [] with
      | none => simp [hf, hc] at heval
      | some value =>
        simp [hf, hc] at heval
        simpa [hwidth] using heval.2
  apply scalarFacts_enforce i bounds.bitwidth out.module.raw.schema _ decl hdecl hscalar hfields intervals[d] hfit
  intro fact hfact
  rw [← hwidth]
  apply Module.fact_true out.module.raw i hs.2.2.2.2.2
  rw [hfacts]
  exact List.mem_append_left _ (List.mem_append_right _ (hmem fact hfact))

end ClaferCompiler.Correctness.ExpressionMeaning
