module

public import ClaferCompiler.Correctness.PipelineObservedRelations
public import ClaferCompiler.Correctness.PipelineCompletion
public import ClaferCompiler.Correctness.PipelineQueries

@[expose] public section
/-! Full primitive parent navigation is preserved on recorded inputs; the
unbounded primitive head map is excluded by proved source syntax shape.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr Frontend.Constraints SemanticsBridge.Expr
open Clafer.Semantics DPGraph.Predicates

theorem completed_relation {U : Type} (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (state : Configuration (Fin n) U)
    (primitive : Fin n) (hp : (v.core.structural.get primitive).origin = .integer)
    (shape : PrimitiveShape (SemanticsBridge.Inherited.interpret v.core) primitive)
    (hs : Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core) state)
    (g : U ↪ Atom) (P : Set Atom) (agree : ∀ x, g x ∈ P ↔ x ∈ state.head primitive)
    (e : Fin m) (safe : HeadSafe v.core.structural s e) (x : U) (y : Atom) :
    sourceRelation resolved (completePrimitive state primitive g P) e (g x) y ↔
      ∃ z, sourceRelation resolved state e x z ∧ g z = y := by
  classical
  have hr := (mapOwner_resolved resolved e).2
  cases hk : s.maps[e].kind <;> simp only [hk] at hr
  · have hd : s.maps[e].target ≠ primitive := by
      intro he
      have ho := safe hk
      rw [he,hp] at ho
      cases ho
    simp only [sourceRelation,hk,completePrimitive,ite_eq_right hd]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      have ha : a = x := g.injective ha
      subst a
      exact ⟨b,hab,hb⟩
    · rintro ⟨b,hb,hby⟩; exact ⟨x,b,hb,rfl,hby⟩
  · by_cases hd : s.maps[e].source = primitive
    · simp only [sourceRelation,hk,completePrimitive,hd,ite_true]
      rw [agree x]
      constructor
      · rintro ⟨hy,hx⟩
        exact ⟨state.root,(primitive_contains _ _ _ shape hs _ _).mpr ⟨rfl,hx⟩,hy.symm⟩
      · rintro ⟨z,hz,hzy⟩
        have h := (primitive_contains _ _ _ shape hs _ _).mp hz
        exact ⟨hzy.symm.trans (congrArg g h.1),h.2⟩
    · simp only [sourceRelation,hk,completePrimitive,ite_eq_right hd]
      constructor
      · rintro ⟨a,b,hab,ha,hb⟩
        have hb : b = x := g.injective hb
        subst b
        exact ⟨a,hab,ha⟩
      · rintro ⟨a,ha,hay⟩; exact ⟨a,x,ha,hay,rfl⟩
  · simp only [sourceRelation,hk,completePrimitive]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      have ha : a = x := g.injective ha
      subst a
      exact ⟨b,hab,hb⟩
    · rintro ⟨a,ha,hay⟩; exact ⟨x,a,ha,rfl,hay⟩
  · have hd : mapOwner resolved e ≠ primitive := by
      intro he
      have href : (v.core.structural.get primitive).reference = .basic :=
        (SemanticsBridge.Structural.reference_basic _).mp shape.reference
      rw [he,href] at hr
      cases hr.2
    simp only [sourceRelation,hk,completePrimitive,ite_eq_right hd]
    constructor
    · rintro ⟨a,⟨b,c,hbc,hbx,hca⟩,d,f,hdf,hda,hfy⟩
      have hb : b = x := g.injective hbx
      have hdc : d = c := g.injective (hda.trans hca.symm)
      subst b; subst d
      exact ⟨f,⟨c,hbc,hdf⟩,hfy⟩
    · rintro ⟨z,⟨a,hxa,haz⟩,hzy⟩
      exact ⟨g a,⟨x,a,hxa,rfl,rfl⟩,a,z,haz,rfl,hzy⟩
  · simp only [sourceRelation,hk]
    rw [completed_head state primitive g P agree]
    constructor
    · rintro ⟨hx,hy⟩; exact ⟨x,⟨hx,rfl⟩,hy⟩
    · rintro ⟨z,⟨hx,rfl⟩,hy⟩; exact ⟨hx,hy⟩

end ClaferCompiler.Correctness.Pipeline
