module

public import ClaferCompiler.Correctness.Behavioral.Completion

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

/-- A constant target valuation has no changing relation tables. This is a
property of concrete observations, independent of formula satisfaction. -/
def ConstantValuation (τ : Temporal.Trace) : Prop := ∀ t, τ.state t = τ.state 0

theorem relation_constant {r : Temporal.Rel} (h : r.Term) (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace)
    (constant : ConstantValuation τ) (e : Temporal.Environment) (t u : Nat) :
    r.eval s w τ e t = r.eval s w τ e u := by
  induction h generalizing t u with
  | empty | var | ints | integer => rfl
  | values n =>
    change (τ.state t |>.values[n]?.getD []).map (fun (x, n) =>
      [Temporal.Atom.object x, Temporal.Atom.integer n]) =
      (τ.state u |>.values[n]?.getD []).map (fun (x, n) =>
        [Temporal.Atom.object x, Temporal.Atom.integer n])
    rw [constant t, constant u]
  | sig n =>
    change (τ.state t |>.signatures[n]?.getD []).map (fun x => [Temporal.Atom.object x]) =
      (τ.state u |>.signatures[n]?.getD []).map (fun x => [Temporal.Atom.object x])
    rw [constant t, constant u]
  | field n =>
    change (τ.state t |>.fields[n]?.getD []).map (List.map Temporal.Atom.object) =
      (τ.state u |>.fields[n]?.getD []).map (List.map Temporal.Atom.object)
    rw [constant t, constant u]
  | univ =>
    change ((τ.state t).universe s w).map (fun x => [x]) =
      ((τ.state u).universe s w).map (fun x => [x])
    rw [constant t, constant u]
  | iden =>
    change ((τ.state t).universe s w).map (fun x => [x, x]) =
      ((τ.state u).universe s w).map (fun x => [x, x])
    rw [constant t, constant u]
  | union ha hb ia ib => simp only [Temporal.Rel.eval_union ha hb, ia t u, ib t u]
  | inter ha hb ia ib => simp only [Temporal.Rel.eval_inter ha hb, ia t u, ib t u]
  | diff ha hb ia ib => simp only [Temporal.Rel.eval_diff ha hb, ia t u, ib t u]
  | product ha hb ia ib => simp only [Temporal.Rel.eval_product ha hb, ia t u, ib t u]
  | join ha hb ia ib => simp only [Temporal.Rel.eval_join ha hb, ia t u, ib t u]
  | transpose ha ia => simp only [Temporal.Rel.eval_transpose ha, ia t u]
  | prime ha ia => simpa only [Temporal.Rel.eval_prime ha] using ia (t + 1) (u + 1)

-- [proof->req~compiler-behavioral-correctness~1]
theorem snapshotState_constant (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (constant : ConstantValuation τ) (t : Nat) :
    snapshotState v w τ t = snapshotState v w τ 0 := by
  unfold snapshotState
  congr 1
  · apply List.map_congr_left
    intro n _
    rw [relation_constant (snapshotRel_term v (.sig n)) (schema v) w τ constant [] t 0]
  · apply List.map_congr_left
    intro n _
    rw [relation_constant (snapshotRel_term v (.field n)) (schema v) w τ constant [] t 0]

/-- Exactly the M1 clauses occurring in the emitted behavioral state facts,
with their actual implicit-always wrapper and strict target definedness. -/
def CommonStructuralFacts (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace) : Prop :=
  ∀ q ∈ Backend.Alloy.Structural.facts v,
    (Temporal.Formula.unary .always (snapshotFormula v q.2)).Defined (schema v) w τ [] 0 ∧
    (Temporal.Formula.unary .always (snapshotFormula v q.2)).Holds (schema v) w τ [] 0

-- [proof->req~compiler-behavioral-correctness~1]
/-- Each clause quantified by the reduction is present in the actual emitted
behavioral target, with exactly this temporal wrapper. -/
theorem common_fact_generated (v : IR.Behavioral.Admitted k) (b : Bounds)
    (scopes : List Scope) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (q : Backend.Alloy.Structural.Obligation × Formula)
    (hq : q ∈ Backend.Alloy.Structural.facts v.structural.toLayout) :
    Temporal.Formula.unary .always (snapshotFormula v.structural.toLayout q.2) ∈
      (target v b scopes fuel enough).facts := by
  apply Encoding.state_generated
  exact List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

-- [proof->req~compiler-behavioral-correctness~1]
/-- The common clauses of a constant temporal valuation are exactly evaluation
of the existing structural target on its concrete live projection. Overflow
remains failure on both sides. -/
theorem constant_common_fragment (v : IR.Structural.Layout k) (w : Nat)
    (scopes : List Scope) (τ : Temporal.Trace) (constant : ConstantValuation τ)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true) :
    CommonStructuralFacts v w τ ↔
      (Backend.Alloy.Structural.target v scopes w).eval (snapshotState v w τ 0) = some true := by
  have frame t : (τ.state t).wellFormed (schema v).declarations = true := constant t ▸ wf
  have snapWF t := snapshotState_wellFormed v w τ (frame t)
  have transported (q : Backend.Alloy.Structural.Obligation × Formula)
      (hq : q ∈ Backend.Alloy.Structural.facts v) (t : Nat) :
      (snapshotFormula v q.2).Defined (schema v) w τ [] t ∧
        (snapshotFormula v q.2).Holds (schema v) w τ [] t ↔
      q.2.eval w (snapshotState v w τ 0) [] = some true := by
    rw [← snapshotState_constant v w τ constant t]
    exact snapshotFormula_eval v (snapshot_facts v _ (snapWF t) q hq) _ w τ t
      (snapshotState_signatures v w τ (frame t)) (snapshotState_fields v w τ (frame t)) []
  constructor
  · intro h
    have hf := (mapM_all_true ((Backend.Alloy.Structural.facts v).map Prod.snd)
      (fun f => f.eval w (snapshotState v w τ 0) [])).mpr (by
        intro f hf
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
        have holds := h q hq
        have built := snapshotFormula_built v (snapshot_facts v _ (snapWF 0) q hq)
        simp only [Temporal.Formula.Defined, Temporal.Formula.Holds,
          Temporal.Formula.fold_unary _ _ _ _ built] at holds
        exact (transported q hq 0).mp ⟨holds.1 0 (Nat.le_refl _), holds.2 0 (Nat.le_refl _)⟩)
    have scalar := Structural.no_scalar_fields v w (snapshotState v w τ 0)
    change (do let fs ← ((Backend.Alloy.Structural.facts v).map Prod.snd).mapM
                 (fun f => f.eval w (snapshotState v w τ 0) [])
               let body ← some true
               pure (fs.all id && body == true &&
                 (snapshotState v w τ 0).scalarFields w (Backend.Alloy.Structural.schema v))) = some true
    simpa [scalar] using hf
  · intro h q hq
    have value := Module.fact_true (Backend.Alloy.Structural.target v scopes w)
      (snapshotState v w τ 0) h q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
    have built := snapshotFormula_built v (snapshot_facts v _ (snapWF 0) q hq)
    simp only [Temporal.Formula.Defined, Temporal.Formula.Holds,
      Temporal.Formula.fold_unary _ _ _ _ built]
    exact ⟨fun t _ => ((transported q hq t).mpr value).1,
      fun t _ => ((transported q hq t).mpr value).2⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- The reduction also uses the existing full structural satisfaction relation.
Its declaration and scope checks are stated separately from the common facts. -/
theorem constant_common_satisfies (v : IR.Structural.Layout k) (w : Nat)
    (scopes : List Scope) (τ : Temporal.Trace) (constant : ConstantValuation τ)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (typed : (Backend.Alloy.Structural.target v scopes w).wellTyped = true)
    (bounded : (Backend.Alloy.Structural.target v scopes w).safeBounds = true)
    (declarations : (snapshotState v w τ 0).declarations (Backend.Alloy.Structural.schema v) = true)
    (scopeFits : (snapshotState v w τ 0).inScope scopes = true) :
    CommonStructuralFacts v w τ ↔
      Satisfies (Backend.Alloy.Structural.target v scopes w) (snapshotState v w τ 0) := by
  constructor
  · intro h
    exact ⟨typed, bounded, snapshotState_wellFormed v w τ wf, declarations, scopeFits,
      (constant_common_fragment v w scopes τ constant wf).mp h⟩
  · intro h
    exact (constant_common_fragment v w scopes τ constant wf).mpr h.2.2.2.2.2

namespace TraceRep
variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
    {target : Temporal.Lasso}

-- [proof->req~compiler-behavioral-correctness~1]
/-- When all identities are live, projection retains every object and every
inherited static pool, so the common-fragment reduction has no liveness filter. -/
theorem snapshot_liveness_trivial (rep : TraceRep v source target) (w t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (allLive : ∀ x : Fin o, x ∈ (trace source).live t) :
    (∀ label, label ∈ (snapshotState v w target.unfold t).signatures[0]?.getD [] ↔
      label ∈ (target.unfold.state t).signatures[0]?.getD []) ∧
    (∀ d label, label ∈ (snapshotState v w target.unfold t).signatures[
        Backend.Alloy.Structural.signatureId v d]?.getD [] ↔
      label ∈ (target.unfold.state t).signatures[Backend.Alloy.Structural.signatureId v d]?.getD []) := by
  constructor
  · intro label
    rw [rep.snapshot_objects w t wf, rep.allObjects]
    simp [allLive, TraceRep.label]
  · intro d label
    rw [rep.snapshot_heads w t wf, rep.pools]
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, (ancestor_agrees _ _ _).mpr hx.2, he⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, ⟨allLive x, (ancestor_agrees _ _ _).mp hx⟩, he⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral
