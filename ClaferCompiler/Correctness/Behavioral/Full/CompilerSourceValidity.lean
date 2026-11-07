module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionTransport
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionStructure

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.ObservesCompletion
open Clafer.Behavioral Clafer.Semantics DPGraph.Predicates
open IR.BehavioralStructural Backend.Alloy.Behavioral.Full
universe u
variable {U : Type u} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U} {objects : Fin o ↪ U}


theorem covered (h : ObservesCompletion v p l τ R objects) {y : U} (hy : y ∈ τ.live t) :
    ∃ x, h.embedding x = y := by
  have member : y ∈ h.embedding '' (completeTrace v p l).live t := by rw [h.live_image]; exact hy
  obtain ⟨x, _, eq⟩ := member
  exact ⟨x, eq⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem identities (h : ObservesCompletion v p l τ R objects)
    (valid : Structural.IdentitiesValid (SemanticsBridge.BehavioralStructural.interpret v.core) τ) : Structural.IdentitiesValid (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.type_eq, h.root_eq]; exact valid.root_type
  · intro x hx
    apply h.embedding.injective
    rw [h.root_eq]
    exact valid.root_only _ ((h.type_eq x).trans hx)
  · intro x
    rw [← h.type_eq]
    exact valid.concrete _
  · have source := valid.root_parent
    rw [← h.root_eq, h.parent_eq] at source
    exact Option.map_eq_none_iff.mp source
  · intro x different
    have different' : h.embedding x ≠ τ.identities.root := by
      rw [← h.root_eq]
      exact fun eq => different (h.embedding.injective eq)
    obtain ⟨y, hy⟩ := valid.parent_exists _ different'
    rw [h.parent_eq] at hy
    obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.mp hy
    exact ⟨z, hz⟩
  · intro x y link
    obtain ⟨c, hc, ancestor⟩ := valid.parent_typed _ _ ((h.parent_iff x y).mpr link)
    exact ⟨c, by simpa only [h.type_eq] using hc, by simpa only [h.type_eq] using ancestor⟩

theorem parent_live (h : ObservesCompletion v p l τ R objects) (valid : Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ) :
    ∀ t x y, x ∈ (completeTrace v p l).live t → (completeTrace v p l).identities.parent x = some y → y ∈ (completeTrace v p l).live t := by
  intro t x y live parent
  exact (h.live_iff t y).mp (valid.parent_live t _ _ ((h.live_iff t x).mpr live)
    ((h.parent_iff x y).mpr parent))

/-- Standard subtype equivalence plus the existing upstream `inRange_iff`
transports finite or infinite fibres; no new cardinality semantics are used. -/
def subtypeEquiv (h : ObservesCompletion v p l τ R objects)
    (P : Completion o → Prop) (Q : U → Prop)
    (agree : ∀ x, Q (h.embedding x) ↔ P x)
    (inside : ∀ y, Q y → y ∈ τ.live t) : {x // P x} ≃ {y // Q y} :=
  Equiv.ofBijective (fun x => ⟨h.embedding x.val, (agree x.val).mpr x.property⟩) (by
    constructor
    · intro x y eq
      exact Subtype.ext (h.embedding.injective (congrArg Subtype.val eq))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := h.covered (inside y hy)
      exact ⟨⟨x, (agree x).mp hy⟩, rfl⟩)

def containmentEquiv (h : ObservesCompletion v p l τ R objects) (t : Nat) (d : Fin k) (x : Completion o) :
    {y // ((completeTrace v p l).raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y} ≃
      {y // (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d (h.embedding x) y} :=
  h.subtypeEquiv (t := t) _ _ (h.contains_iff t d x) (fun _ hy => hy.1.2.1)

theorem children_iff (h : ObservesCompletion v p l τ R objects) (t : Nat) (d : Fin k) (x y : Completion o) :
    Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d (h.embedding x) (h.embedding y) ↔
      Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family ((completeTrace v p l).raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y := by
  simp only [Groups.ChildObjects, h.contains_iff]

def childrenEquiv (h : ObservesCompletion v p l τ R objects) (t : Nat) (d : Fin k) (x : Completion o) :
    {y // Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family ((completeTrace v p l).raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y} ≃
      {y // Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d (h.embedding x) y} :=
  h.subtypeEquiv (t := t) _ _ (h.children_iff t d x) (by
    rintro y ⟨a, _, c, _, link⟩
    exact link.1.2.1)

theorem reaches (h : ObservesCompletion v p l τ R objects) {x : Completion o}
    (source : (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches (h.embedding x)) :
    ((completeTrace v p l).raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x := by
  have lift {y : U} (path : (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches y) :
      ∃ z, h.embedding z = y ∧ ((completeTrace v p l).raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches z := by
    induction path with
    | refl => exact ⟨(completeTrace v p l).identities.root, h.root_eq, .refl⟩
    | @tail y z before step ih =>
      obtain ⟨d, link⟩ := step
      obtain ⟨a, rfl, path⟩ := ih
      obtain ⟨b, rfl⟩ := h.covered link.1.2.1
      exact ⟨b, rfl, path.tail ⟨d, (h.contains_iff t d a b).mp link⟩⟩
  obtain ⟨y, eq, path⟩ := lift source
  exact h.embedding.injective eq ▸ path

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Exact observation tables and one global identity embedding preserve all
source structural clauses on the canonical infinite primitive completion. -/
theorem valid (h : ObservesCompletion v p l τ R objects) (source : Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ) :
    Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) := by
  let ids := h.identities source.identities
  have wf := SemanticsBridge.BehavioralStructural.validated_wellFormed v
  refine ⟨ids, ?_, h.parent_live source, ?_⟩
  · intro t
    apply (h.live_iff t _).mp
    rw [h.root_eq]
    exact source.root_live t
  · intro t
    refine {
      typed := ⟨raw_containment_typed (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) wf ids t, ?_⟩
      root_head := ?_
      root_separate := raw_root_separate (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) wf ids t
      inherits := raw_inherits (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) t
      abstracts := raw_abstracts (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) wf ids t
      parents := raw_parents (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) wf ids (h.parent_live source) t
      references := ?_
      coherent := ?_
      keys := ?_
      multiplicities := ?_
      groups := ?_
      disjoint := raw_disjoint (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) t
      reachable := ?_ }
    · intro d x y link
      obtain ⟨head, c, target, result⟩ := (source.states t).typed.2 d _ _ ((h.deref_iff t d x y).mpr link)
      exact ⟨(h.head_iff t d x).mp head, c, target, (h.head_iff t c y).mp result⟩
    · intro x
      rw [← h.head_iff, (source.states t).root_head, ← h.root_eq]
      exact h.embedding.injective.eq_iff
    · intro d c target x hx
      obtain ⟨y, link, unique⟩ := (source.states t).references d c target _ ((h.head_iff t d x).mpr hx)
      obtain ⟨_, c', _, hy⟩ := (source.states t).typed.2 d _ y link
      obtain ⟨z, rfl⟩ := h.covered hy.1
      refine ⟨z, (h.deref_iff t d x z).mp link, ?_⟩
      intro other ho
      exact h.embedding.injective (unique _ ((h.deref_iff t d x other).mpr ho))
    · intro d e x y z left right
      exact h.embedding.injective ((source.states t).coherent d e _ _ _
        ((h.deref_iff t d x y).mpr left) ((h.deref_iff t e x z).mpr right))
    · intro d owner ownerOf kind parent target x z left lref right rref
      apply h.embedding.injective
      exact (source.states t).keys d owner ownerOf kind _ _ _ _
        ((h.contains_iff t d parent x).mpr left) ((h.observed_deref_iff t d x target).mpr lref)
        ((h.contains_iff t d parent z).mpr right) ((h.observed_deref_iff t d z target).mpr rref)
    · intro d c parent x hx
      exact (inRange_iff _ (h.containmentEquiv t d x)).mpr
        ((source.states t).multiplicities d c parent _ ((h.head_iff t c x).mpr hx))
    · intro d concrete x
      exact (inRange_iff _ (h.childrenEquiv t d x.val)).mpr
        ((source.states t).groups d concrete ⟨h.embedding x.val, (h.head_iff t d x.val).mpr x.property⟩)
    · intro x hx
      exact h.reaches ((source.states t).reachable _ ((h.live_iff t x).mpr hx))

end ClaferCompiler.Correctness.Behavioral.Full.ObservesCompletion
