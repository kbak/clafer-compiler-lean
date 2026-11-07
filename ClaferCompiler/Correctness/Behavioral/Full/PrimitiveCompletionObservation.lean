module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural

universe u

-- [impl->req~compiler-trace-assurance~1]
/-- A single global nonprimitive embedding, exact finite tables and the full
integer realization. These equations mention no source/target formula truth or
validity. Unused identities outside the observation can remain absent. -/
structure ObservesCompletion (v : Validated k) (p : Fin k) (l : ObservedLasso k o steps)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (objects : Fin o ↪ U) : Prop where
  disjoint : ∀ x, objects x ∉ R.domain
  root : objects l.objects.identities.root = τ.identities.root
  objectType : ∀ x, τ.identities.directType (objects x) = l.objects.identities.directType[x]
  integerType : ∀ z, τ.identities.directType (R.encode z) = p
  objectParent : ∀ x, τ.identities.parent (objects x) = (l.objects.identities.parent[x]).map objects
  integerParent : ∀ z, τ.identities.parent (R.encode z) = some (objects l.objects.identities.root)
  objectLive : ∀ t x, objects x ∈ τ.live t ↔ (l.objects.at t).live[x] = true
  integerLive : ∀ t z, R.encode z ∈ τ.live t
  objectReferences : ∀ t d x y, τ.deref t d (objects x) (objects y) ↔
    (d, x, y) ∈ (l.objects.at t).references
  scalarReferences : ∀ t d x z, τ.deref t d (objects x) (R.encode z) ↔
    (v.core.structural.get d).reference.target = some p ∧
      (l.objects.at t).live[x] = true ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        l.objects.identities.directType[x] d ∧ (l.valuesAt t)[x] = z
  integerReferences : ∀ t d z y, ¬ τ.deref t d (R.encode z) y
  liveCovered : ∀ t y, y ∈ τ.live t → (∃ x, objects x = y) ∨ ∃ z, R.encode z = y

namespace ObservesCompletion
variable {U : Type u} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}
  {objects : Fin o ↪ U}

def embedding (h : ObservesCompletion v p l τ R objects) : Completion o ↪ U where
  toFun := Sum.elim objects R.encode
  inj' := by
    intro x y eq
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (objects.injective eq)
      | inr z => exact (h.disjoint x ⟨z, eq.symm⟩).elim
    | inr z =>
      cases y with
      | inl y => exact (h.disjoint y ⟨z, eq⟩).elim
      | inr w => exact congrArg Sum.inr (R.encode.injective eq)

@[simp] theorem embedding_object (h : ObservesCompletion v p l τ R objects) (x : Fin o) :
    h.embedding (Sum.inl x) = objects x := rfl

@[simp] theorem embedding_integer (h : ObservesCompletion v p l τ R objects) (z : Int) :
    h.embedding (Sum.inr z) = R.encode z := rfl

theorem root_eq (h : ObservesCompletion v p l τ R objects) :
    h.embedding (completeTrace v p l).identities.root = τ.identities.root := h.root

theorem type_eq (h : ObservesCompletion v p l τ R objects) (x : Completion o) :
    τ.identities.directType (h.embedding x) = (completeTrace v p l).identities.directType x := by
  cases x with
  | inl x => exact h.objectType x
  | inr z => exact h.integerType z

theorem parent_eq (h : ObservesCompletion v p l τ R objects) (x : Completion o) :
    τ.identities.parent (h.embedding x) = ((completeTrace v p l).identities.parent x).map h.embedding := by
  cases x with
  | inl x =>
    rw [embedding_object, h.objectParent]
    simp [completeTrace, completeIdentities, Option.map_map, Function.comp_def]
  | inr z => exact h.integerParent z

theorem parent_iff (h : ObservesCompletion v p l τ R objects) (x y : Completion o) :
    τ.identities.parent (h.embedding x) = some (h.embedding y) ↔
      (completeTrace v p l).identities.parent x = some y := by
  rw [h.parent_eq]
  simp [Option.map_eq_some_iff, h.embedding.injective.eq_iff]

theorem live_iff (h : ObservesCompletion v p l τ R objects) (t : Nat) (x : Completion o) :
    h.embedding x ∈ τ.live t ↔ x ∈ (completeTrace v p l).live t := by
  cases x with
  | inl x => exact h.objectLive t x
  | inr z => exact ⟨fun _ => trivial, fun _ => h.integerLive t z⟩

theorem deref_iff (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (d : Fin k) (x y : Completion o) :
    τ.deref t d (h.embedding x) (h.embedding y) ↔ (completeTrace v p l).deref t d x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.objectReferences t d x y
    | inr z => exact h.scalarReferences t d x z
  | inr z => exact ⟨fun link => (h.integerReferences t d z _ link).elim, fun link =>
      (completeDeref_integer_source v p l t d z y link).elim⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem head_iff (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (d : Fin k) (x : Completion o) :
    h.embedding x ∈ (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ↔
      x ∈ ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d := by
  simp only [Clafer.Behavioral.Trace.raw, Set.mem_ofPred_eq, h.live_iff, h.type_eq]

theorem contains_iff (h : ObservesCompletion v p l τ R objects)
    (t : Nat) (d : Fin k) (x y : Completion o) :
    (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains
      d (h.embedding x) (h.embedding y) ↔
      ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y := by
  simp only [Clafer.Behavioral.Trace.raw, Clafer.Behavioral.Trace.ParentAt,
    h.live_iff, h.parent_iff, h.type_eq]

theorem live_image (h : ObservesCompletion v p l τ R objects) (t : Nat) :
    h.embedding '' (completeTrace v p l).live t = τ.live t := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h.live_iff t x).mpr hx
  · intro hy
    rcases h.liveCovered t y hy with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨Sum.inl x, (h.objectLive t x).mp hy, rfl⟩
    · exact ⟨Sum.inr z, trivial, rfl⟩

theorem head_image (h : ObservesCompletion v p l τ R objects) (t : Nat) (d : Fin k) :
    h.embedding '' ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d =
      (τ.raw (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h.head_iff t d x).mpr hx
  · intro hy
    have covered : y ∈ h.embedding '' (completeTrace v p l).live t := by
      rw [h.live_image]
      exact hy.1
    obtain ⟨x, _, rfl⟩ := covered
    exact ⟨x, (h.head_iff t d x).mp hy, rfl⟩

end ObservesCompletion

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem observesCompletion_self (v : Validated k) (p : Fin k) (l : ObservedLasso k o steps) :
    ObservesCompletion v p l (completeTrace v p l) completeIntegers
      ⟨Sum.inl, Sum.inl_injective⟩ where
  disjoint := by intro x; simp
  root := rfl
  objectType := fun _ => rfl
  integerType := fun _ => rfl
  objectParent := fun _ => rfl
  integerParent := fun _ => rfl
  objectLive := fun _ _ => Iff.rfl
  integerLive := fun _ _ => trivial
  objectReferences := fun _ _ _ _ => Iff.rfl
  scalarReferences := fun _ _ _ _ => Iff.rfl
  integerReferences := completeDeref_integer_source v p l
  liveCovered := by
    intro t y _
    cases y with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr z => exact Or.inr ⟨z, rfl⟩

end ClaferCompiler.Correctness.Behavioral.Full
