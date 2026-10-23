module

public import ClaferCompiler.Correctness.InheritedGeneration

@[expose] public section
/-! [proof->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Correctness.Inherited
open Backend.Alloy Backend.Alloy.Inherited IR.Inherited
attribute [local instance] Classical.propDecidable

/-- Adding facts changes no signature, role, command or scope allocation. -/
theorem base_checked (v : Validated n) (scopes : List Scope) (w : Nat)
    (ht : (target v scopes w).wellTyped = true)
    (hb : (target v scopes w).safeBounds = true) :
    (Backend.Alloy.Structural.target v.layout scopes w).wellTyped = true ∧
      (Backend.Alloy.Structural.target v.layout scopes w).safeBounds = true := by
  constructor
  · simp only [target, Module.wellTyped, List.all_append, Bool.and_eq_true] at ht ⊢
    tauto
  · simp only [target, Module.safeBounds, List.all_append, Bool.and_eq_true] at hb ⊢
    tauto

theorem run_eval (schema : Schema) (fs : List Formula) (scopes : List Scope)
    (w : Nat) (i : Instance) (scalar : i.scalarFields w schema = true) :
    ({ schema, facts := fs, command := { scopes, bitwidth := w } } : Module).eval i = some true ↔
      ∀ f ∈ fs, f.eval w i [] = some true := by
  change (do let values ← fs.mapM (fun f => f.eval w i []); pure (values.all id && true && i.scalarFields w schema)) = some true ↔ _
  simpa [scalar] using (mapM_all_true fs (fun f => f.eval w i []))

theorem base_satisfies (v : Validated n) (scopes : List Scope) (w : Nat) (i : Instance)
    (h : Satisfies (target v scopes w) i) :
    Satisfies (Backend.Alloy.Structural.target v.layout scopes w) i := by
  obtain ⟨ht, hb⟩ := base_checked v scopes w h.1 h.2.1
  refine ⟨ht, hb, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  apply (run_eval _ _ _ _ _ (Structural.no_scalar_fields v.layout w i)).mpr
  intro f hf
  exact Module.fact_true _ _ h.2.2.2.2.2 f (List.mem_append_left _ hf)

/-- Existing representation equations identify the inherited union fiber exactly. -/
theorem represented_children {U : Type} (v : Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Structural.Represents v.layout s i) (d : Fin n) (p : U) (tuple : Tuple) :
    tuple ∈ (childHeads v d).eval i [(r.objects p).val] ↔
      ∃ x, Clafer.Compile.Groups.ChildObjects (SemanticsBridge.Inherited.interpret v.core).family s d p x ∧
        tuple = [(r.objects x).val] := by
  unfold childHeads
  rw [Structural.mem_union_eval _ (by
    intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    exact .join (.var _) (.field _))]
  constructor
  · rintro ⟨q, hq, ht⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    obtain ⟨a, ha, hp⟩ := (mem_children v d c).mp hc
    obtain ⟨x, hx, ht⟩ := (Structural.represented_contains_fiber v.layout s i r c a
      (by simpa [Validated.layout] using hp) p _ 0 rfl tuple).mp ht
    exact ⟨x, ⟨a, ha, c, hp, hx⟩, ht⟩
  · rintro ⟨x, ⟨a, ha, c, hp, hx⟩, rfl⟩
    change (v.core.structural.get c).parent = some a at hp
    refine ⟨_, List.mem_map.mpr ⟨c, (mem_children v d c).mpr ⟨a, ha, hp⟩, rfl⟩, ?_⟩
    exact (Structural.represented_contains_fiber v.layout s i r c a
      (by simpa [Validated.layout] using hp) p _ 0 rfl _).mpr ⟨x, hx, rfl⟩

/-- Numeric finite-fiber representability, independent of either satisfaction relation. -/
def CountFits {U : Type} [Fintype U] (v : Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (w : Nat) : Prop := by
  classical
  exact Structural.SourceCountFits v.layout s w ∧
    ∀ d, v.core.explicitAbstract[d] = false → ∀ p ∈ s.head d,
      Structural.IntervalFits w (v.core.structural.get d).groupBounds
        (Fintype.card {x // Clafer.Compile.Groups.ChildObjects
          (SemanticsBridge.Inherited.interpret v.core).family s d p x})

theorem group_eval_iff {U : Type} [Fintype U] (v : Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Structural.Represents v.layout s i) (w : Nat) (d : Fin n) :
    (Formula.all (Backend.Alloy.Structural.head v.layout d)
      (Backend.Alloy.Structural.interval (v.core.structural.get d).groupBounds (childHeads v d))).eval w i [] = some true ↔
      ∀ p ∈ s.head d,
        Structural.IntervalFits w (v.core.structural.get d).groupBounds
          (Fintype.card {x // Clafer.Compile.Groups.ChildObjects
            (SemanticsBridge.Inherited.interpret v.core).family s d p x}) ∧
        DPGraph.Predicates.InRange (SemanticsBridge.Structural.bounds (v.core.structural.get d).groupBounds)
          {x // Clafer.Compile.Groups.ChildObjects
            (SemanticsBridge.Inherited.interpret v.core).family s d p x} := by
  classical
  rw [Structural.all_represented_iff _ _ _ _ (Structural.interval_term _ _) w i []
    (Structural.represented_head_membership v.layout s i r d [])]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  rw [Structural.interval_eval_iff, Structural.unary_card _ _
    (Subtype.val_injective.comp r.objects.injective) _ (represented_children v s i r d p)]
  rw [DPGraph.Predicates.inRange_card]

theorem groups_iff {U : Type} [Fintype U] (v : Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Structural.Represents v.layout s i) (w : Nat) :
    (∀ f ∈ groups v, f.eval w i [] = some true) ↔
      ∀ d, v.core.explicitAbstract[d] = false → ∀ p ∈ s.head d,
        Structural.IntervalFits w (v.core.structural.get d).groupBounds
          (Fintype.card {x // Clafer.Compile.Groups.ChildObjects
            (SemanticsBridge.Inherited.interpret v.core).family s d p x}) ∧
        DPGraph.Predicates.InRange (SemanticsBridge.Structural.bounds (v.core.structural.get d).groupBounds)
          {x // Clafer.Compile.Groups.ChildObjects
            (SemanticsBridge.Inherited.interpret v.core).family s d p x} := by
  classical
  simp only [groups, Backend.Alloy.Structural.allocation_head_apply,
    List.forall_mem_map, List.mem_filter, List.mem_finRange,
    Bool.not_eq_true', true_and, group_eval_iff v s i r w]

end ClaferCompiler.Correctness.Inherited
