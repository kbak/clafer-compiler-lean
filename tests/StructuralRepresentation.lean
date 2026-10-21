module

public import tests.StructuralAlloy
public import ClaferCompiler.Correctness.StructuralDecoding

@[expose] public section
namespace ClaferCompiler.Tests.StructuralRepresentation
open Backend.Alloy Backend.Alloy.Structural Correctness.Structural
open Tests.StructuralAlloy (bagValidated bag_order bagInstance)

/-! Nontrivial kernel witnesses, including two bag occurrences at one target.
[utest->req~compiler-structural-representation~1] -/

def bagObservation : Observation 3 where
  objects := [0, 1, 2, 3]
  root := 0
  heads d := [[0], [1], [2, 3]][d.val]?.getD []
  containment d := [[], [(0, 1)], [(0, 2), (0, 3)]][d.val]?.getD []
  dereference d := [[], [], [(2, 1), (3, 1)]][d.val]?.getD []

theorem bag_table : TableWellFormed bagValidated bagObservation := by unfold TableWellFormed; decide

theorem bag_roundtrip : decode bagValidated (encode bagValidated bagObservation) = .ok bagObservation :=
  decode_encode bagValidated bagObservation bag_table rfl (by decide)

theorem bag_encode_identity : encode bagValidated bagObservation = bagInstance := by
  simp only [encode, bag_order]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem bag_target_satisfies :
    Satisfies (target bagValidated (List.replicate 4 ⟨4, false⟩) 5) bagInstance := by
  unfold Satisfies target schema facts declarationFacts fieldDeclaration ownership setKey head signatureId
  simp only [bag_order]
  decide

theorem bag_live : Live bagInstance := satisfying_live _ _ _ _ bag_target_satisfies

theorem bag_decoded_representation :
    ∃ hr : bagObservation.root ∈ bagObservation.objects,
      Nonempty (Represents bagValidated (realize bagObservation hr) bagInstance) := by
  apply decoded_represents bagValidated bagInstance bagObservation
  · rw [← bag_encode_identity]
    exact bag_roundtrip
  · exact bag_live

/-- Two heads have distinct identities, despite equal owner and target. -/
theorem bag_occurrences_distinct :
    (0, 2) ∈ bagObservation.containment 2 ∧ (0, 3) ∈ bagObservation.containment 2 ∧
    (2, 1) ∈ bagObservation.dereference 2 ∧ (3, 1) ∈ bagObservation.dereference 2 ∧
    (2 : Nat) ≠ 3 := by decide

def missingOwner : Observation 3 :=
  { bagObservation with containment := fun d =>
      if d == 2 then [(0, 2)] else bagObservation.containment d }

theorem violating_roundtrip : decode bagValidated (encode bagValidated missingOwner) = .ok missingOwner :=
  decode_encode bagValidated missingOwner (by unfold TableWellFormed; decide) rfl (by decide)

set_option maxRecDepth 10000 in
theorem missing_owner_fact_false :
    (ownership bagValidated 2).eval 5 (encode bagValidated missingOwner) [] = some false := by
  simp only [ownership, head, signatureId, encode, bag_order]
  decide

end ClaferCompiler.Tests.StructuralRepresentation
