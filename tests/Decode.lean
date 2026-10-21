module

public import tests.StructuralRepresentation
public import ClaferCompiler.Backend.Alloy.Decode

@[expose] public section
namespace ClaferCompiler.Tests.Decode
open Backend.Alloy.Structural
open Tests.StructuralAlloy (bagValidated)
open Tests.StructuralRepresentation

/-! Kernel witnesses: export preserves distinct heads and a violating candidate.
[utest->req~compiler-instance-decode~1] -/
theorem bag_export :
    decodeCandidate bagValidated (encode bagValidated.toLayout bagObservation) =
      .ok (candidate bagValidated bagObservation) := by
  simp only [decodeCandidate, bag_roundtrip, Except.map]

theorem negative_export :
    decodeCandidate bagValidated (encode bagValidated.toLayout missingOwner) =
      .ok (candidate bagValidated missingOwner) := by
  simp only [decodeCandidate, violating_roundtrip, Except.map]

theorem two_exported_occurrences :
    (candidate bagValidated bagObservation).references = [(300, (2, 1)), (300, (3, 1))] := by
  decide

end ClaferCompiler.Tests.Decode
