module

public import ClaferCompiler.SemanticsBridge.StructuralNormalization
public import tests.StructuralNormalizationNative

public section
namespace ClaferCompiler.Tests.StructuralNormalization
open IR.Structural IR.Structural.Normalization

-- [utest->req~compiler-resolved-normalization~1]
theorem input_admitted : coreChecks input cert ∧ supportChecks input cert := by decide

theorem output_exact : normalize input = expected := by
  unfold normalize input expected
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem changes_input : normalize input ≠ input := by rw [output_exact]; decide

theorem output_fixed : normalize expected = expected := fixed expected (by unfold NormalForm; decide)

theorem invalid_interval_rejected : checked invalidInterval cert =
    .error ⟨.malformed, "ir.invalid-core-or-ranks", "", none⟩ := by
  apply checked_error
  have h : ¬ coreChecks invalidInterval cert := by
    intro h
    have hb := (h.2.2.2.2.2.1 0).1
    simp [invalidInterval, Core.get, Bounds.Valid] at hb
  simp [validate, h]

theorem missing_unused_rejected : checked input missingUnused =
    .error ⟨.unsupported, "ir.unsupported-or-invalid-certificate", "", none⟩ := by
  apply checked_error
  have hc : coreChecks input missingUnused := by decide
  have hs : ¬ supportChecks input missingUnused := by decide
  simp [validate, hc, hs]

end ClaferCompiler.Tests.StructuralNormalization
