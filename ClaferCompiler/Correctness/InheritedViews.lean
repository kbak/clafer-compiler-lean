module

public import ClaferCompiler.Backend.Alloy.InheritedViews
public import ClaferCompiler.Correctness.InheritedCorrectness

@[expose] public section
/-! [proof->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Correctness.Inherited
open Backend.Alloy Backend.Alloy.Inherited
open Clafer.Semantics.Realization

/-- Decoded context ownership is exactly the original ownership restricted by
parent membership. No inheritance-membership assumption substitutes for an edge. -/
theorem view_contains (o : Backend.Alloy.Structural.Observation n) (hr : o.root ∈ o.objects)
    (f q : Fin n) (p x : Structural.Objects o) :
    (p.val, x.val) ∈ viewContains o f q ↔ Contains (Structural.realize o hr) f q p x := by
  simp [viewContains, Contains, Structural.realize, and_comm]

/-- A live-data condition supplies the original owner object, not a new label. -/
theorem view_heads (o : Backend.Alloy.Structural.Observation n) (hr : o.root ∈ o.objects)
    (live : ∀ f p x, (p, x) ∈ o.containment f → p ∈ o.objects)
    (f q : Fin n) (x : Structural.Objects o) :
    x.val ∈ viewHeads o f q ↔ x ∈ View (Structural.realize o hr) f q := by
  simp only [viewHeads, List.mem_filter, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hx, ⟨⟨p, y⟩, hp, he⟩⟩
    change y = x.val at he
    subst y
    have h := List.mem_filter.mp hp
    exact ⟨hx, ⟨p, live f p x.val h.1⟩, h.1, by simpa [Structural.realize] using h.2⟩
  · rintro ⟨hx, p, hp, hq⟩
    exact ⟨hx, (p.val, x.val), by simp [viewContains, show (p.val, x.val) ∈ o.containment f from hp, show p.val ∈ o.heads q from hq], rfl⟩

theorem view_deref (o : Backend.Alloy.Structural.Observation n) (hr : o.root ∈ o.objects)
    (live : ∀ f p x, (p, x) ∈ o.containment f → p ∈ o.objects)
    (f q : Fin n) (x t : Structural.Objects o) :
    (x.val, t.val) ∈ viewDeref o f q ↔ Deref (Structural.realize o hr) f q x t := by
  simp [viewDeref, view_heads o hr live, Deref, Structural.realize, and_comm]

/-- Target liveness discharges the sole data premise of the context lemmas
for observations produced by the decoder. -/
theorem observation_owner_live (v : IR.Inherited.Validated n) (i : Instance)
    (hl : Correctness.Structural.Live i) (root : Nat) (f : Fin n) (p x : Nat)
    (h : (p, x) ∈ (Backend.Alloy.Structural.observation v.layout i root).containment f) :
    p ∈ (Backend.Alloy.Structural.observation v.layout i root).objects := by
  unfold Backend.Alloy.Structural.observation at h ⊢
  cases hp : (v.layout.core.get f).parent with
  | none => simp [hp, Backend.Alloy.Structural.readPairs] at h
  | some c =>
    have ht : [p, x] ∈ i.fields[Backend.Alloy.Structural.fieldId v.layout.core f .containment]?.getD [] := by
      simpa only [hp, Option.bind_some, Correctness.Structural.mem_readPairs] using h
    exact (Correctness.Structural.field_atom_live i hl _ p x ht).1

/-- The composed contextual span retains the actual original link pair.
This is upstream's injective forgetting map, including repeated bag targets. -/
theorem context_links_injective (v : IR.Inherited.Validated n)
    (o : Backend.Alloy.Structural.Observation n) (hr : o.root ∈ o.objects) (f q : Fin n) :
    Function.Injective (targetLink (SemanticsBridge.Inherited.interpret v.core)
      (Structural.realize o hr) f q) := target_links_injective _ _ f q

end ClaferCompiler.Correctness.Inherited
