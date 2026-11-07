module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionObservation
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionRestriction

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural
open scoped BigOperators

universe u
namespace ObservesCompletion
variable {U : Type u} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}
  {objects : Fin o ↪ U}

@[simp] theorem embedding_domain (h : ObservesCompletion v p l τ R objects) (x : Completion o) :
    h.embedding x ∈ R.domain ↔ x ∈ completeIntegers.domain := by
  cases x with
  | inl x => simp [h.disjoint]
  | inr z => exact ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨z, rfl⟩⟩

theorem embedding_decode (h : ObservesCompletion v p l τ R objects)
    (x : Completion o) (integer : x ∈ completeIntegers.domain) :
    R.decode (h.embedding x) = completeIntegers.decode x := by
  obtain ⟨z, rfl⟩ := integer
  exact R.decode_encode z

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The full observation embedding preserves partial conversion, including
infinite and mixed collections. No boundedness or truth premise is needed. -/
theorem coerce_image (h : ObservesCompletion v p l τ R objects) (S : Set (Completion o)) :
    Clafer.Behavioral.IntegerObservation.coerce R (h.embedding '' S) =
      Clafer.Behavioral.IntegerObservation.coerce completeIntegers S := by
  classical
  by_cases hf : S.Finite
  · have imageFinite := hf.image h.embedding
    by_cases ht : S ⊆ completeIntegers.domain
    · have imageTyped : h.embedding '' S ⊆ R.domain := by
        rintro _ ⟨x, hx, rfl⟩
        exact (h.embedding_domain x).mpr (ht hx)
      rw [Clafer.Behavioral.IntegerObservation.coerce_finite _ imageFinite imageTyped,
        Clafer.Behavioral.IntegerObservation.coerce_finite _ hf ht]
      congr 1
      rw [Set.Finite.toFinset_image h.embedding hf imageFinite, Finset.sum_image]
      · exact Finset.sum_congr rfl (fun x hx =>
          h.embedding_decode x (ht (hf.mem_toFinset.mp hx)))
      · intro x _ y _ eq
        exact h.embedding.injective eq
    · obtain ⟨x, hx, bad⟩ := Set.not_subset.mp ht
      rw [Clafer.Behavioral.IntegerObservation.coerce_wrong_domain _
          (Set.mem_image_of_mem _ hx) (by simpa using bad),
        Clafer.Behavioral.IntegerObservation.coerce_wrong_domain _ hx bad]
  · have imageInfinite : (h.embedding '' S).Infinite :=
      Set.Infinite.image h.embedding.injective.injOn hf
    rw [Clafer.Behavioral.IntegerObservation.coerce_infinite _ imageInfinite,
      Clafer.Behavioral.IntegerObservation.coerce_infinite _ hf]

theorem extract_image (h : ObservesCompletion v p l τ R objects) (S : Set (Completion o)) :
    R.extract (h.embedding '' S) = completeIntegers.extract S := by
  apply Option.ext
  intro z
  rw [FormalCD.IntegerRealization.extract_eq_some_iff,
    FormalCD.IntegerRealization.extract_eq_some_iff]
  change h.embedding '' S = {R.encode z} ↔ S = {completeIntegers.encode z}
  have singleton : h.embedding '' {completeIntegers.encode z} = {R.encode z} := by simp
  rw [← singleton]
  exact Set.image_injective.mpr h.embedding.injective |>.eq_iff

theorem observed_deref_iff (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (d : Fin k) (x y : Completion o) :
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ).deref
      t d (h.embedding x) (h.embedding y) ↔
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p l)).deref t d x y := by
  simp only [Clafer.Behavioral.Structural.observed, Clafer.Behavioral.InheritedReference.deref,
    h.head_iff]
  apply exists_congr
  intro owner
  exact and_congr_right (fun _ => and_congr_right (fun _ => h.deref_iff t owner x y))

theorem step_iff (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (s : Clafer.Behavioral.Step (Fin k)) (x y : Completion o) :
    s.relation (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
      t (h.embedding x) (h.embedding y) ↔
    s.relation (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p l)) t x y := by
  cases s with
  | parent => exact and_congr (h.parent_iff x y) (h.live_iff t y)
  | child d => exact h.contains_iff t d x y
  | deref d =>
    exact and_congr (h.live_iff t x)
      (and_congr (h.live_iff t y) (h.observed_deref_iff t d x y))

theorem step_image (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (s : Clafer.Behavioral.Step (Fin k)) (S : Set (Completion o)) :
    h.embedding '' s.image (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p l)) t S =
    s.image (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        t (h.embedding '' S) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, link⟩, rfl⟩
    exact ⟨h.embedding x, ⟨x, hx, rfl⟩, (h.step_iff t s x z).mpr link⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, link⟩
    have live : y ∈ τ.live t := by
      cases s with
      | parent => exact link.2
      | child d => exact link.1.2.1
      | deref d => exact link.2.1
    have covered : y ∈ h.embedding '' (completeTrace v p l).live t := by
      rw [h.live_image]
      exact live
    obtain ⟨z, _, rfl⟩ := covered
    exact ⟨z, ⟨x, hx, (h.step_iff t s x z).mp link⟩, rfl⟩

def environment (h : ObservesCompletion v p l τ R objects)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) : Clafer.Behavioral.Environment U n :=
  ⟨h.embedding ρ.this, fun i => h.embedding '' ρ.lookup i⟩

theorem environment_push (h : ObservesCompletion v p l τ R objects)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) (S : Set (Completion o)) :
    h.environment (ρ.push S) = (h.environment ρ).push (h.embedding '' S) := by
  unfold environment Clafer.Behavioral.Environment.push
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Captured sets and direct navigation use the same embedding at every time,
including navigation from a context which is currently absent. -/
theorem setExpr_image (h : ObservesCompletion v p l τ R objects)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat)
    (e : Clafer.Behavioral.SetExpr (Fin k) n) :
    h.embedding '' Clafer.Behavioral.Structural.eval
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) e ρ t =
    Clafer.Behavioral.Structural.eval (SemanticsBridge.BehavioralStructural.interpret v.core)
      τ e (h.environment ρ) t := by
  unfold Clafer.Behavioral.Structural.eval
  induction e with
  | empty => exact Set.image_empty _
  | this =>
    ext y
    constructor
    · rintro ⟨x, ⟨rfl, live⟩, rfl⟩
      exact ⟨rfl, (h.live_iff t _).mpr live⟩
    · rintro ⟨rfl, live⟩
      exact ⟨ρ.this, ⟨rfl, (h.live_iff t _).mp live⟩, rfl⟩
  | root =>
    change h.embedding '' {(completeTrace v p l).identities.root} = {τ.identities.root}
    rw [Set.image_singleton, h.root_eq]
  | var i => rfl
  | extent d => exact h.head_image t d
  | union a b ha hb => simp only [Clafer.Behavioral.SetExpr.eval, Set.image_union, ha, hb]
  | inter a b ha hb =>
    simp only [Clafer.Behavioral.SetExpr.eval, Set.image_inter h.embedding.injective, ha, hb]
  | diff a b ha hb =>
    simp only [Clafer.Behavioral.SetExpr.eval, Set.image_sdiff h.embedding.injective, ha, hb]
  | step s a ha =>
    change h.embedding '' s.image _ _ _ _ = _
    rw [h.step_image, ha]
    rfl
  | thisStep s =>
    change h.embedding '' s.image _ _ _ _ = _
    rw [h.step_image, Set.image_singleton]
    rfl

end ObservesCompletion
end ClaferCompiler.Correctness.Behavioral.Full
