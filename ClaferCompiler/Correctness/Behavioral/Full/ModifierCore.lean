module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCorrectness
public import Clafer.Behavioral.ModifierLowering

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.ModifierCore
open IR.Behavioral Backend.Alloy.Behavioral.Full
open IR.Behavioral.ModifierLowering (owners obligations lower)

-- [proof->req~compiler-rich-core-explicit~1]
/-- The executable bundle agrees with the accepted upstream checked-core
reduction. Structural validity and the total inherited-set adapter are explicit. -/
theorem upstream_agrees (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List Surface.Modifiers.Modifier) k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ) :
    (∀ item ∈ obligations v table,
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        R item.2).PartialAttached
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        SemanticsBridge.Behavioral.Expression.observation
        ((SemanticsBridge.Behavioral.Surface.Modifiers.placement item.1).contexts
          (SemanticsBridge.BehavioralStructural.interpret v.core) τ)) ↔
    Clafer.Behavioral.Modifiers.LoweredHolds (SemanticsBridge.BehavioralStructural.interpret v.core)
      τ (SemanticsBridge.Behavioral.Modifiers.declared table)
      (Clafer.Behavioral.Modifiers.coreObservation (SemanticsBridge.BehavioralStructural.interpret v.core) τ) :=
  (modifierExpansions_source v table R τ valid).trans
    (Clafer.Behavioral.Modifiers.loweredHolds_iff _ τ valid _).symm

variable (v : IR.BehavioralStructural.Validated k) (p : Fin k)
  (source : ObservedLasso k o steps)

-- [proof->req~compiler-rich-core-explicit~1]
/-- Materializing attachment owners neither loses parent obligations nor
requires quantification over the infinite mathematical integer carrier. -/
theorem item_agrees
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (d : Fin k) (m : Surface.Modifiers.Modifier)
    (item : Surface.Modifiers.Placement k × Expression.Formula k 0)
    (member : item ∈ modifierExpansions d m) :
    (∀ owner ∈ owners v item.1, ∀ t x,
      x ∈ ((completeTrace v p source).raw (Sets.model v) t).head owner →
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) completeIntegers item.2).Satisfies
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation true (.closed x) t) ↔
    SourceModifierItem v p source item := by
  rcases item with ⟨where_, body⟩
  cases where_ with
  | all =>
    constructor
    · intro h t x _ live
      cases x with
      | inl x =>
        apply h source.objects.identities.directType[x]
        · simpa [owners, integerDeclaration] using ordinary x
        · exact ⟨live, Relation.ReflTransGen.refl⟩
      | inr z =>
        cases m <;> simp only [modifierExpansions, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq, reduceCtorEq, false_and, or_false] at member
        · rcases member with ⟨_, rfl⟩
          exact ModifierPrimitive.stable_integer v p source d (.heads d) z t
        · rcases member with ⟨_, rfl⟩
          exact ModifierPrimitive.stable_integer v p source d (.targets d) z t
    · intro h owner _ t x hx
      exact h t x (by trivial) hx.1
  | heads owner =>
    simp only [owners, List.mem_singleton, forall_eq]
    constructor
    · intro h t x hx _; exact h t x hx
    · intro h t x hx; exact h t x hx hx.1
  | parents owner =>
    simp only [owners, Option.mem_toList]
    constructor
    · intro h t x hx _
      obtain ⟨q, parent, head⟩ := hx
      exact h q parent t x head
    · intro h q parent t x head
      exact h t x ⟨q, parent, head⟩ head.1

-- [proof->req~compiler-rich-core-explicit~1]
theorem constraints_agree
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source))
    (table : Vector (List Surface.Modifiers.Modifier) k) :
    (∀ c ∈ IR.Behavioral.ModifierLowering.constraints v table,
      (sourceConstraint v c).Holds (completeTrace v p source)
        (sourceObservation v completeIntegers (completeTrace v p source))) ↔
    Clafer.Behavioral.Modifiers.Holds (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source) (SemanticsBridge.Behavioral.Modifiers.declared table) := by
  have result : (∀ c ∈ IR.Behavioral.ModifierLowering.constraints v table,
      (sourceConstraint v c).Holds (completeTrace v p source)
        (sourceObservation v completeIntegers (completeTrace v p source))) ↔
      (∀ item ∈ obligations v table, SourceModifierItem v p source item) := by
    simp only [IR.Behavioral.ModifierLowering.constraints, List.forall_mem_flatMap,
      List.forall_mem_map, sourceConstraint_meaning v completeIntegers _ valid]
    apply forall_congr'
    intro item
    apply imp_congr_right
    intro member
    obtain ⟨d, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨m, _, hm⟩ := List.mem_flatMap.mp member
    exact item_agrees v p source ordinary d m item hm
  exact result.trans (modifierExpansions_source v table completeIntegers (completeTrace v p source) valid)

-- [proof->req~compiler-rich-core-explicit~1]
theorem empty_holds (τ : Clafer.Behavioral.Trace (Fin k) U) :
    Clafer.Behavioral.Modifiers.Holds (SemanticsBridge.BehavioralStructural.interpret v.core) τ
      (SemanticsBridge.Behavioral.Modifiers.declared (Vector.replicate k [])) := by
  intro d
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    obtain ⟨a, _, ha⟩ := h <;>
    simp [SemanticsBridge.Behavioral.Modifiers.declared] at ha

-- [proof->req~compiler-rich-core-explicit~1]
/-- Erasure preserves the complete model and the selected assertion/scenario.
The finite carrier's ordinary types are the existing representation premise. -/
theorem result_agrees (r : Request k)
    (ordinary : ∀ x : Fin o,
      integerDeclaration r.model.structural source.objects.identities.directType[x] = false) :
    SourceResult (lower r) completeIntegers (completeTrace r.model.structural p source) ↔
      SourceResult r completeIntegers (completeTrace r.model.structural p source) := by
  rw [sourceResult_iff, sourceResult_iff, sourceModel_satisfies, sourceModel_satisfies]
  have cmd : SourceCommand (lower r) completeIntegers (completeTrace r.model.structural p source) =
      SourceCommand r completeIntegers (completeTrace r.model.structural p source) := by
    cases h : r.command <;> simp [SourceCommand, lower, h]
  rw [cmd]
  apply and_congr _ Iff.rfl
  change (_ ∧ _ ∧ ∀ a ∈ r.model.constraints ++ _, _) ↔ _
  simp only [List.forall_mem_append]
  constructor
  · rintro ⟨valid, _, constraints, generated⟩
    exact ⟨valid, (constraints_agree r.model.structural p source ordinary valid r.model.modifiers).mp generated,
      constraints⟩
  · rintro ⟨valid, modifiers, constraints⟩
    exact ⟨valid, empty_holds r.model.structural _, constraints,
      (constraints_agree r.model.structural p source ordinary valid r.model.modifiers).mpr modifiers⟩


-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Actual target soundness after core erasure recovers the original model,
including finality, rather than only the newly generated constraints. -/
theorem compiled_lower_sound (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile (lower r) b fuel = .ok c)
    (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Backend.Alloy.Temporal.Lasso)
    (sat : Backend.Alloy.Temporal.Satisfies c.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode r.model.structural target = .ok decoded ∧
      SourceResult r completeIntegers (completeTrace r.model.structural p decoded.2.2) := by
  obtain ⟨out⟩ := compile_output (lower r) b fuel c success
  obtain ⟨decoded, read, holds⟩ := compiled_sound (lower r) b fuel c success p primitive target sat
  let rep := decode_rep r.model.structural target decoded read
  have ordinary := fun x => (rep.ordinary_concrete b.bitwidth (out.identity target sat) x).2
  exact ⟨decoded, read, (result_agrees p decoded.2.2 r ordinary).mp holds⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Erasure preserves bounded completeness with the unchanged fitting premises. -/
theorem compiled_lower_complete (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile (lower r) b fuel = .ok c)
    (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (fit : Fits r.model.structural p source b)
    (holds : SourceResult r completeIntegers (completeTrace r.model.structural p source)) :
    Backend.Alloy.Temporal.Lasso.Satisfies c.module.raw (encode source) :=
  compiled_complete (lower r) b fuel c success p primitive source fit
    ((result_agrees p source r fit.structural.ordinary).mpr holds)

end ClaferCompiler.Correctness.Behavioral.Full.ModifierCore
