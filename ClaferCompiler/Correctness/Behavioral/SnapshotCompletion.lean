module

public import ClaferCompiler.Correctness.Behavioral.Soundness
public import ClaferCompiler.Correctness.Behavioral.CompletionFacts
public import ClaferCompiler.Correctness.StructuralCompletionFacts

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral
open Encoding

namespace TraceRep
variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Temporal.Lasso}

-- [proof->req~compiler-behavioral-correctness~1]
theorem snapshotDeclarations_complete (rep : TraceRep v source target) (w t : Nat)
    (valid : (trace source).Valid (SemanticsBridge.Structural.interpret v.core)) :
    ∀ f ∈ snapshotDeclarations v, f.Holds (schema v) w target.unfold [] t := by
  intro f hf
  obtain ⟨d, _, hf⟩ := List.mem_flatMap.mp hf
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | rfl
  · apply (Relations.unary_subset rep.label_injective
      (rep.head_meaning w [] t d) (rep.head_meaning w [] t p)).mpr
    exact (valid.states t).inherits d p (by simpa [SemanticsBridge.Structural.interpret] using hp)
  · intro row hr
    obtain ⟨x, y, hxy, rfl⟩ := (rep.step_meaning w [] t (.child d) row).mp hr
    have typed := (valid.states t).typed.1 d x y hxy
    obtain ⟨c, hc, hx⟩ := typed.2
    have hp : (v.core.get d).parent = some p := by simpa using hp
    have eq : c = p := Option.some.inj (hc.symm.trans hp)
    subst c
    exact (Relations.binary_product (head_term v p) (head_term v d)
      (rep.head_meaning w [] t p) (rep.head_meaning w [] t d) _).mpr
        ⟨x, y, ⟨hx, typed.1⟩, rfl⟩
  · cases hr : (v.core.get d).reference.target with
    | none =>
      intro row
      constructor
      · intro h
        obtain ⟨x, y, hxy, _⟩ := (rep.deref_meaning w [] t d row).mp h
        obtain ⟨_, c, hc, _⟩ := (valid.states t).typed.2 d x y hxy
        have hc : (v.core.get d).reference.target = some c := by
          simpa [SemanticsBridge.Structural.interpret] using hc
        simp [hr] at hc
      · exact False.elim ∘ List.not_mem_nil
    | some c =>
      change (_ ∧ _)
      constructor
      · intro row h
        obtain ⟨x, y, hxy, rfl⟩ := (rep.deref_meaning w [] t d row).mp h
        obtain ⟨hx, e, he, hy⟩ := (valid.states t).typed.2 d x y hxy
        have he : (v.core.get d).reference.target = some e := by
          simpa [SemanticsBridge.Structural.interpret] using he
        have eq : e = c := Option.some.inj (he.symm.trans hr)
        subst e
        exact (Relations.binary_product (head_term v d) (head_term v c)
          (rep.head_meaning w [] t d) (rep.head_meaning w [] t c) _).mpr
            ⟨x, y, ⟨hx, hy⟩, rfl⟩
      · change (Temporal.Formula.all (head v d)
          (.mult .one (.join (.var 0) (deref d)))).Holds (schema v) w target.unfold [] t
        rw [all_unary (.mult _ _) (rep.head_meaning w [] t d)]
        intro x hx
        obtain ⟨y, hy, unique⟩ := (valid.states t).references d c
          (by simpa [SemanticsBridge.Structural.interpret] using hr) x hx
        have image := Relations.unary_image rep.label_injective (.var 0) (.field _)
          (Relations.unary_singleton (f := rep.label) x)
          (rep.deref_meaning w [.object (rep.label x)] t d)
        have singleton : {z | ∃ a ∈ ({x} : Set (Fin o)), (trace source).deref t d a z} = {y} := by
          ext z
          constructor
          · rintro ⟨a, rfl, hz⟩
            exact unique z hz
          · rintro rfl
            exact ⟨x, rfl, hy⟩
        rw [singleton] at image
        exact Relations.unary_one_of_singleton image

theorem liveSnapshot_countFits (v : IR.Structural.Layout k)
    (source : IR.Behavioral.Lasso k o steps) (w t : Nat)
    (rootLive : (trace source).identities.root ∈ (trace source).live t)
    (fits : Structural.SourceCountFits v
      ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t) w) :
    Structural.SourceCountFits v (liveSnapshot
      (SemanticsBridge.Structural.interpret v.core) (trace source) t rootLive) w := by
  classical
  constructor
  · intro d c hc p hp
    rw [Fintype.card_congr (liveFiberEquiv _ _ _ rootLive d p)]
    exact fits.1 d c hc p.val hp
  · intro d hd p hp
    rw [Fintype.card_congr (liveChildEquiv _ _ _ rootLive d p)]
    exact fits.2 d hd p.val hp

-- [proof->req~compiler-behavioral-correctness~1]
/-- All actual state facts follow from source validity. Integer assumptions
bound source fiber observations, separately from either satisfaction relation. -/
theorem stateFacts_complete (rep : TraceRep v source target) (w t : Nat)
    (sw : (Alloy.Structural.schema v).wellFormed = true)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (hd : (target.unfold.state t).declarations (schema v).declarations = true)
    (valid : (trace source).Valid (SemanticsBridge.Structural.interpret v.core))
    (fits : Structural.SourceCountFits v
      ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t) w) :
    ∀ f ∈ stateFacts v, f.Defined (schema v) w target.unfold [] t ∧
      f.Holds (schema v) w target.unfold [] t := by
  classical
  have decls := rep.snapshotDeclarations_complete w t valid
  have sd := snapshotState_declarations v w target.unfold wf hd decls
  have snapshotWF := snapshotState_wellFormed v w target.unfold wf
  have repr := rep.snapshotRepData w t wf
    (Structural.declarations_live _ _ sw snapshotWF sd (Structural.schema_parentless v))
    (fun d x y h => by
      obtain ⟨_, c, hc, _⟩ := (valid.states t).typed.2 d x y h
      have hc : (v.core.get d).reference.target = some c := by
        simpa [SemanticsBridge.Structural.interpret] using hc
      simp [hc]) (valid.root_live t)
  have truth := (trace source).snapshot_structural valid t
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · refine ⟨trivial, ?_⟩
        apply (Relations.unary_subset rep.label_injective
          (rep.root_meaning w [] t) (rep.live_meaning w [] t)).mpr
        rintro x rfl
        exact valid.root_live t
      · have eq := List.mem_singleton.mp hf
        subst f
        refine ⟨trivial, ?_⟩
        apply (Relations.unary_subset rep.label_injective
          (Relations.unary_image rep.label_injective (live_term v) (.field 0)
            (rep.live_meaning w [] t) (rep.parent_meaning w [] t))
          (rep.live_meaning w [] t)).mpr
        rintro p ⟨x, hx, hp⟩
        exact valid.parent_live t x p hx hp
    · refine ⟨?_, decls f hf⟩
      obtain ⟨d, _, hf⟩ := List.mem_flatMap.mp hf
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hf
      rcases hf with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | rfl
      · trivial
      · trivial
      · cases (v.core.get d).reference.target with
        | none => trivial
        | some c => exact ⟨trivial, fun _ _ => trivial⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    apply (snapshotFormula_eval v (snapshot_facts v _ snapshotWF q hq) _ w target.unfold t
      (snapshotState_signatures v w target.unfold wf)
      (snapshotState_fields v w target.unfold wf) []).mpr
    exact Structural.source_facts v _ _ repr truth w
      (liveSnapshot_countFits v source w t (valid.root_live t) fits) q hq

end TraceRep
end ClaferCompiler.Correctness.Behavioral
