module

public import ClaferCompiler.Correctness.PipelineFullBinding

@[expose] public section
/-! Canonical span reductions retain the original structural relations.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr Frontend.Constraints SemanticsBridge.Expr
open Clafer.Semantics CategoryTheory DPGraph DPGraph.Predicates

theorem ambient_of_relation {U : Type} (A B : Set U) (r : U → U → Prop)
    (typed : ∀ x y, r x y → x ∈ A ∧ y ∈ B) (x y : U) :
    (x,y) ∈ ambientRelation (Span.ofRelation (fun (a : A) (b : B) => r a.val b.val)) ↔ r x y := by
  constructor
  · rintro ⟨⟨⟨a,b⟩,hab⟩,ha,hb⟩
    change a.val = x at ha
    change b.val = y at hb
    exact ha ▸ hb ▸ hab
  · intro h
    exact ⟨⟨(⟨x,(typed x y h).1⟩,⟨y,(typed x y h).2⟩),h⟩,rfl,rfl⟩

noncomputable def sourceRelation {U : Type} {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (state : Configuration (Fin n) U) (e : Fin m) (x y : U) : Prop :=
  match s.maps[e].kind with
  | .head => state.contains s.maps[e].target x y
  | .parent => state.contains s.maps[e].source y x
  | .dereference => state.deref s.maps[e].source x y
  | .inclusion => x ∈ state.head s.maps[e].source ∧ x = y
  | .target => ∃ z, state.contains (mapOwner resolved e) x z ∧ state.deref (mapOwner resolved e) z y

theorem fullSpan_relation {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (state : Configuration (Fin n) Atom)
    (typed : state.Typed (SemanticsBridge.Structural.interpret c))
    (inherits : state.Inherits (SemanticsBridge.Structural.interpret c))
    (e : Fin m) (x y : Atom) :
    (x,y) ∈ ambientRelation (fullSpan resolved state e) ↔ sourceRelation resolved state e x y := by
  have hr := (mapOwner_resolved resolved e).2
  have containTyped (d q : Fin n) (hq : (c.get d).parent = some q) :
      ∀ x y, state.contains d x y → x ∈ state.head q ∧ y ∈ state.head d := by
    intro a b h
    obtain ⟨hb,p,hp,ha⟩ := typed.1 d a b h
    have he : p = q := Option.some.inj (hp.symm.trans hq)
    exact ⟨he ▸ ha,hb⟩
  have derefTyped (d q : Fin n) (hq : (c.get d).reference.target = some q) :
      ∀ x y, state.deref d x y → x ∈ state.head d ∧ y ∈ state.head q := by
    intro a b h
    obtain ⟨ha,p,hp,hb⟩ := typed.2 d a b h
    have hp : (c.get d).reference.target = some p := by
      simpa [SemanticsBridge.Structural.interpret] using hp
    have he : p = q := Option.some.inj (hp.symm.trans hq)
    exact ⟨ha,he ▸ hb⟩
  cases hk : s.maps[e].kind <;> simp only [hk] at hr
  · simp only [fullSpan,sourceRelation,hk]
    apply ambient_of_relation
    apply containTyped
    exact hr.2 ▸ hr.1
  · simp only [fullSpan,sourceRelation,hk]
    refine ambient_of_relation _ _ (fun a b => state.contains s.maps[e].source b a) ?_ x y
    intro a b h
    have hh := containTyped _ _ (hr.1 ▸ hr.2) b a h
    exact hh.symm
  · simp only [fullSpan,sourceRelation,hk]
    exact ambient_of_relation _ _ _ (derefTyped _ _ (hr.1 ▸ hr.2)) x y
  · simp only [fullSpan,sourceRelation,hk]
    rw [← join_span]
    change (∃ z, (x,z) ∈ ambientRelation _ ∧ (z,y) ∈ ambientRelation _) ↔ _
    apply exists_congr
    intro z
    exact and_congr (ambient_of_relation _ _ _ (containTyped _ _ hr.1) x z)
      (ambient_of_relation _ _ _ (derefTyped _ _ hr.2) z y)
  · simp only [fullSpan,sourceRelation,hk]
    constructor
    · rintro ⟨⟨⟨a,b⟩,hab⟩,ha,hb⟩
      change a.val = x at ha
      change b.val = y at hb
      exact ⟨ha ▸ a.property,ha.symm.trans (hab.trans hb)⟩
    · rintro ⟨hx,rfl⟩
      have hsub := inherits s.maps[e].source s.maps[e].target (hr.1 ▸ hr.2) x hx
      exact ⟨⟨(⟨x,hx⟩,⟨x,hsub⟩),rfl⟩,rfl,rfl⟩

end ClaferCompiler.Correctness.Pipeline
