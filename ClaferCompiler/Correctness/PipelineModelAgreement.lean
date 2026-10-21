module

public import ClaferCompiler.Correctness.PipelineNavigation
public import ClaferCompiler.Correctness.PipelineQueryAgreement

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr Frontend.Constraints SemanticsBridge.Expr Backend.Alloy Backend.Alloy.Expressions
open Clafer.Semantics DPGraph.Predicates

theorem completed_primitive_domains (v : IR.Inherited.Validated n)
    (primitive : Fin n) (hp : (v.core.structural.get primitive).origin = .integer)
    (o : Structural.Observation n) (root : o.root ∈ o.objects)
    (g : Structural.Objects o ↪ Atom) (R : FormalCD.IntegerRealization Atom) :
    ∀ d, (v.core.structural.get d).origin = .integer →
      (completePrimitive (Structural.realize o root) primitive g R.domain).head d = R.domain := by
  intro d hd
  have he : d = primitive := v.selectedChecked.2.2.2.2.2.2.2.2.1 d primitive hd hp
  subst d
  simp [completePrimitive]

/-- Agreement is constructed from original observation tables, structural
completion and fixed observed integer payloads. No expression truth is assumed. -/
theorem completed_model_agreement (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (primitive : Fin n)
    (hp : (v.core.structural.get primitive).origin = .integer)
    (shape : PrimitiveShape (SemanticsBridge.Inherited.interpret v.core) primitive)
    (o : Structural.Observation n) (root : o.root ∈ o.objects) (live : ObservationLive o)
    (hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core)
      (Structural.realize o root))
    (rows : List (Nat × Int)) (g : Structural.Objects o ↪ Atom)
    (labels : ∀ x, g x = decodeAtom rows x.val) (R : FormalCD.IntegerRealization Atom)
    (agree : ∀ x, g x ∈ R.domain ↔ x ∈ (Structural.realize o root).head primitive)
    (fixed : ∀ z ∈ rows.map Prod.snd, R.encode z = .integer z)
    (ordinary : ∀ x, x ∉ (Structural.realize o root).head primitive → ∃ a, g x = .object a)
    (values : ∀ x, x ∈ (Structural.realize o root).head primitive →
      ∃ z ∈ rows.map Prod.snd, g x = .integer z)
    (full : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core)
      (completePrimitive (Structural.realize o root) primitive g R.domain))
    (valid : ObservationValid s (observe v s o rows)) :
    QueryAgreement v.core.structural s (observe v s o rows) valid
      (fullBinding v s resolved _ full R (completed_primitive_domains v primitive hp o root g R)) := by
  let state := completePrimitive (Structural.realize o root) primitive g R.domain
  have objects := observed_objects_source v s o root live rows g labels
  have relations := observed_relation_source v s resolved o root live rows g labels
  constructor
  · intro d hd
    have hdp : d ≠ primitive := by
      intro he
      subst d
      have hi := resolved.2.1 primitive
      simp only [hp,decide_true] at hi
      exact Bool.noConfusion (hd.symm.trans hi)
    change state.head d = fullExtent s (observe v s o rows) d
    simp only [fullExtent,hd,Bool.false_eq_true,↓reduceIte]
    rw [objects d]
    simp only [state,completePrimitive,ite_eq_right hdp]
  · intro d S hS
    apply extraction_on R S
    intro a ha z
    have h := hS ha
    rw [objects d] at h
    obtain ⟨x,_,rfl⟩ := h
    by_cases hx : x ∈ (Structural.realize o root).head primitive
    · obtain ⟨k,hk,hxk⟩ := values x hx
      have hR : g x = R.encode k := hxk.trans (fixed k hk).symm
      constructor
      · intro hz
        have he : k = z := R.encode.injective (hR.symm.trans hz)
        subst z
        exact hxk
      · intro hz
        have he : k = z := Atom.integer.inj (hxk.symm.trans hz)
        subst z
        exact hR
    · obtain ⟨b,hb⟩ := ordinary x hx
      constructor
      · intro hz
        have hr : g x ∈ R.domain := hz ▸ ⟨z,rfl⟩
        exact (hx ((agree x).mp hr)).elim
      · intro hz
        rw [hb] at hz
        cases hz
  · intro e safe S hS
    ext y
    constructor
    · rintro ⟨a,ha,hay⟩
      have h := hS ha
      rw [objects s.maps[e].source] at h
      obtain ⟨x,_,rfl⟩ := h
      change (g x,y) ∈ ambientRelation (fullSpan resolved state e) at hay
      have hfull := (fullSpan_relation resolved state full.1 full.2.2.1.1 e (g x) y).mp hay
      obtain ⟨z,hz,hzy⟩ := (completed_relation v s resolved _ primitive hp shape hs g R.domain agree e safe x y).mp hfull
      exact ⟨g x,ha,(relations e (g x) y).mpr ⟨x,z,hz,rfl,hzy⟩⟩
    · rintro ⟨a,ha,hay⟩
      obtain ⟨x,z,hxz,hxa,hzy⟩ := (relations e a y).mp hay
      refine ⟨a,ha,?_⟩
      change (a,y) ∈ ambientRelation (fullSpan resolved state e)
      rw [← hxa]
      apply (fullSpan_relation resolved state full.1 full.2.2.1.1 e (g x) y).mpr
      exact (completed_relation v s resolved _ primitive hp shape hs g R.domain agree e safe x y).mpr
        ⟨z,hxz,hzy⟩

end ClaferCompiler.Correctness.Pipeline
