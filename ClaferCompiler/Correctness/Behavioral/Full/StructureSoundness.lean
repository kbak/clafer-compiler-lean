module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationCompletion
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionValidity

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The actual decoder succeeds from target declarations and generated facts,
and its result completes to a valid upstream rich structural trace. Neither a
representation witness nor any source validity is an input premise. -/
theorem target_structural_sound (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (shape : PrimitiveShape v) (w : Nat) (positive : 0 < w) (small : w ≤ 16)
    (capacity : Nat) (target : Lasso)
    (declarations : target.unfold.Declarations (schema v))
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (reach : ∀ t, (reachabilityFact v capacity).Holds (schema v) w target.unfold [] t)
    (fields : ∀ t, (target.unfold.state t).scalarFields w (schema v).declarations = true) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode v target = .ok decoded ∧
      Clafer.Behavioral.Structural.Valid
        (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p decoded.2.2) := by
  obtain ⟨decoded, read⟩ := target_decode_exists v w target declarations identity states fields
  exact ⟨decoded, read, (decode_rep v target decoded read).complete_valid p primitive shape
    w positive small capacity identity states reach fields⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The soundness carrier has exactly the mathematical integer extent. Bounded
solver Int atoms only constrain scalar observations; they do not replace it. -/
theorem decoded_primitive_extent (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (shape : PrimitiveShape v) (w : Nat) (target : Lasso)
    (decoded : Σ o steps, ObservedLasso k o steps) (read : decode v target = .ok decoded)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0) (t : Nat) :
    ((completeTrace v p decoded.2.2).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head p =
        completeIntegers.domain := by
  apply completeHead_primitive v p primitive shape decoded.2.2
  intro x eq
  have ordinary := ((decode_rep v target decoded read).ordinary_concrete w identity x).2
  rw [eq, (integerDeclaration_eq v p primitive p).mpr rfl] at ordinary
  contradiction

end ClaferCompiler.Correctness.Behavioral.Full
