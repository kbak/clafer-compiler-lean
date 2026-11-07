module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionTransport
public import Clafer.Behavioral.PrimitiveExpression

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural
open scoped BigOperators

universe u v

theorem finiteCard_image {A : Type u} {B : Type v} (f : A ↪ B) (S : Set A) :
    (Clafer.Constraints.finiteCard (f '' S)).map ULift.down =
      (Clafer.Constraints.finiteCard S).map ULift.down := by
  classical
  by_cases finite : S.Finite
  · simp only [Clafer.Constraints.finiteCard_finite _ finite,
      Clafer.Constraints.finiteCard_finite _ (finite.image f), Option.map_some]
    congr 1
    exact congrArg Int.ofNat (Set.ncard_image_of_injective _ f.injective)
  · rw [Clafer.Constraints.finiteCard_infinite _ finite,
      Clafer.Constraints.finiteCard_infinite _ (Set.Infinite.image f.injective.injOn finite)]
    rfl

def occurrenceEmbedding {A : Type u} {B : Type v} (f : A ↪ B) (sets : List (Set A)) :
    Fin sets.length × A ↪ Fin (sets.map (Set.image f)).length × B where
  toFun ix := (⟨ix.1.val, by simp⟩, f ix.2)
  inj' := by
    intro x y eq
    exact Prod.ext (Fin.ext (congrArg (fun z => z.1.val) eq))
      (f.injective (congrArg Prod.snd eq))

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem occurrences_image {A : Type u} {B : Type v} (f : A ↪ B) (sets : List (Set A)) :
    occurrenceEmbedding f sets '' Clafer.Behavioral.PrimitiveExpression.occurrences sets =
      Clafer.Behavioral.PrimitiveExpression.occurrences (sets.map (Set.image f)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x.2 ∈ (sets.map (Set.image f))[x.1.val]
    rw [List.getElem_map]
    exact ⟨x.2, hx, rfl⟩
  · intro hy
    change y.2 ∈ (sets.map (Set.image f))[y.1.val] at hy
    rw [List.getElem_map] at hy
    obtain ⟨x, hx, eq⟩ := hy
    refine ⟨(⟨y.1.val, by simpa using y.1.isLt⟩, x), hx, ?_⟩
    exact Prod.ext (Fin.ext rfl) eq

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Reindexing preserves occurrence folds, including undefined bodies and
infinite occurrence sets. Upstream aggregate evaluation is unchanged; the
finite case uses Mathlib's injective image sum and product laws. -/
theorem fold_image {A : Type u} {B : Type v} (f : A ↪ B)
    (op : Clafer.Behavioral.Aggregate.Fold) (S : Set A)
    (a : A → Option Int) (b : B → Option Int)
    (agree : ∀ x ∈ S, b (f x) = a x) :
    op.eval (f '' S) b = op.eval S a := by
  classical
  by_cases finite : S.Finite
  · have imageFinite := finite.image f
    by_cases defined : ∀ x ∈ S, (a x).isSome
    · have imageDefined : ∀ y ∈ f '' S, (b y).isSome := by
        rintro _ ⟨x, hx, rfl⟩
        rw [agree x hx]
        exact defined x hx
      rw [Clafer.Behavioral.Aggregate.fold_finite op imageFinite b imageDefined,
        Clafer.Behavioral.Aggregate.fold_finite op finite a defined]
      congr 1
      rw [Set.Finite.toFinset_image f finite imageFinite]
      cases op with
      | sum =>
        rw [Finset.sum_image]
        · exact Finset.sum_congr rfl (fun x hx => congrArg (fun q => q.getD 0)
            (agree x (finite.mem_toFinset.mp hx)))
        · intro x _ y _ eq
          exact f.injective eq
      | product =>
        rw [Finset.prod_image]
        · exact Finset.prod_congr rfl (fun x hx => congrArg (fun q => q.getD 0)
            (agree x (finite.mem_toFinset.mp hx)))
        · intro x _ y _ eq
          exact f.injective eq
    · push Not at defined
      obtain ⟨x, hx, bad⟩ := defined
      have missing : a x = none := by
        cases eq : a x with
        | none => rfl
        | some z => simp [eq] at bad
      rw [Clafer.Behavioral.Aggregate.fold_missing op a hx missing,
        Clafer.Behavioral.Aggregate.fold_missing op b (Set.mem_image_of_mem f hx)
          ((agree x hx).trans missing)]
  · rw [Clafer.Behavioral.Aggregate.fold_infinite op finite a,
      Clafer.Behavioral.Aggregate.fold_infinite op
        (Set.Infinite.image f.injective.injOn finite) b]

namespace ObservesCompletion
variable {U : Type u} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}
  {objects : Fin o ↪ U}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem select_image (h : ObservesCompletion v p l τ R objects)
    (op : Clafer.Behavioral.Aggregate.Extreme) (S : Set (Completion o)) :
    op.select R (h.embedding '' S) =
      (op.select completeIntegers S).map (Set.image h.embedding) := by
  classical
  have finite : (h.embedding '' S).Finite ↔ S.Finite :=
    Set.finite_image_iff h.embedding.injective.injOn
  have typed : h.embedding '' S ⊆ R.domain ↔ S ⊆ completeIntegers.domain := by
    constructor
    · intro ht x hx
      exact (h.embedding_domain x).mp (ht (Set.mem_image_of_mem _ hx))
    · rintro ht _ ⟨x, hx, rfl⟩
      exact (h.embedding_domain x).mpr (ht hx)
  unfold Clafer.Behavioral.Aggregate.Extreme.select
  rw [finite, typed]
  split
  · rename_i valid
    simp only [Option.map_some, Option.some.injEq]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, best⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro z hz
      have bound := best (h.embedding z) (Set.mem_image_of_mem _ hz)
      rw [h.embedding_decode x (valid.2 hx), h.embedding_decode z (valid.2 hz)] at bound
      exact bound
    · rintro ⟨x, ⟨hx, best⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [h.embedding_decode x (valid.2 hx), h.embedding_decode z (valid.2 hz)]
      exact best z hz
  · rfl

end ObservesCompletion
end ClaferCompiler.Correctness.Behavioral.Full
