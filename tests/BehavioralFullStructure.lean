module

public import tests.BehavioralStructuralNative
public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationDecoding

public section
namespace ClaferCompiler.Tests.BehavioralFullStructure
open Backend.Alloy Backend.Alloy.Behavioral.Full

def v := BehavioralStructural.validated

/-- Two inherited bag occurrences share a target; an ordinary inherited field
has its own identity despite its effective abstract flag. -/
def observations : ObservedLasso 7 6 3 where
  objects := {
    identities := {
      ids := #v[10, 20, 30, 40, 50, 60]
      root := 0
      directType := #v[0, 1, 4, 5, 5, 6]
      parent := #v[none, some 0, some 0, some 2, some 2, some 3] }
    frames := #v[
      ⟨#v[true, true, true, true, true, true], [(3, 3, 1), (3, 4, 1), (6, 5, 1)]⟩,
      ⟨#v[true, true, true, false, false, false], []⟩,
      ⟨#v[true, true, true, true, true, true], [(3, 3, 1), (3, 4, 1), (6, 5, 1)]⟩]
    loop := 1 }
  values := #v[#v[0, 0, 0, 7, 7, -2], #v[0, 0, 0, 0, 0, 0], #v[0, 0, 0, 9, 9, -2]]

-- [utest->req~compiler-full-behavioral-correctness~1]
theorem inherited_group_union :
    (childHeads v 4).eval (schema v) 5 (encode observations).unfold [.object 30] 0 =
      [[.object 40], [.object 50]] := by decide

theorem ordinary_inherited_child :
    (head v 6).eval (schema v) 5 (encode observations).unfold [] 0 = [[.object 60]] := by decide

theorem inherited_occurrences :
    (deref v 5).eval (schema v) 5 (encode observations).unfold [] 0 =
      [[.object 40, .object 20], [.object 50, .object 20]] := by decide

theorem facts_wellTyped :
    (identityFacts v ++ stateFacts v ++ [reachabilityFact v 6]).all
      (Temporal.Formula.wellTyped (schema v) 0) = true := by decide

theorem decode_encoded : (decode v (encode observations)).isOk = true := by decide

theorem scalar_observations :
    ((encode observations).unfold.state 0).values[0]?.getD [] =
      [(10, 0), (20, 0), (30, 0), (40, 7), (50, 7), (60, -2)] := by decide

theorem period_retained : (encode observations).index 3 = 1 ∧
    (encode observations).index 4 = 2 := by decide

noncomputable def globalRepresentation : Correctness.Behavioral.Full.TraceRep v observations (encode observations) :=
  Correctness.Behavioral.Full.encode_rep v observations (by decide) (by decide) (by decide)

theorem reappearance_parent : observations.objects.identities.parent[3] = some 2 ∧
    (observations.objects.at 1).live[3] = false ∧
    (observations.objects.at 2).live[3] = true := by decide

/-- Scalar values are allowed to change; one global object map still preserves
the head on both sides of its absence. -/
theorem changing_values : (observations.valuesAt 0)[3] = 7 ∧
    (observations.valuesAt 2)[3] = 9 := by decide

def lostValue : Temporal.Lasso :=
  let original := encode observations
  { original with frames := original.frames.map (fun frame => { frame with values := [[]] })
                  nonempty := by simpa using original.nonempty
                  loopValid := by simpa using original.loopValid }

-- [utest->req~compiler-full-behavioral-correctness~1]
theorem rejects_lost_value : (decode v lostValue).isOk = false := by decide

def changingIdentity : Temporal.Lasso :=
  let original := encode observations
  { original with frames := original.frames.mapIdx (fun i frame =>
      if i == 1 then { frame with fields := frame.fields.set 0 [[40, 10]] } else frame)
                  nonempty := by simpa using original.nonempty
                  loopValid := by simpa using original.loopValid }

theorem rejects_changed_parent : (decode v changingIdentity).isOk = false := by decide

def integerCore : IR.BehavioralStructural.Core 3 := ⟨⟨#v[
  { id := 0, name := "root", origin := .syntheticRoot },
  { id := 1, name := "integer", origin := .integer, parent := some 0 },
  { id := 2, name := "value", parent := some 0, reference := .bag 1 }], 0⟩,
  #v[false, false, false], Vector.replicate 3 (.bounds {})⟩

def integerModel : IR.BehavioralStructural.Validated 3 :=
  ⟨integerCore, ⟨#v[0, 1, 1], #v[0, 0, 0], Vector.replicate 3 false⟩,
    IR.BehavioralStructural.analyze integerCore, by decide, by decide⟩

def integerTrace : ObservedLasso 3 3 1 :=
  ⟨⟨⟨#v[10, 20, 30], 0, #v[0, 2, 2], #v[none, some 0, some 0]⟩,
      #v[⟨#v[true, true, true], []⟩], 0⟩, #v[#v[0, 7, 7]]⟩

-- [utest->req~compiler-full-behavioral-correctness~1]
theorem integer_head_occurrences :
    (deref integerModel 2).eval (schema integerModel) 5 (encode integerTrace).unfold [] 0 =
      [[.object 20, .integer 7], [.object 30, .integer 7]] := by decide

theorem integer_shape : PrimitiveShape integerModel := by decide

theorem integer_facts_wellTyped :
    (identityFacts integerModel ++ stateFacts integerModel ++ [reachabilityFact integerModel 3]).all
      (Temporal.Formula.wellTyped (schema integerModel) 0) = true := by decide

theorem decode_integer_encoded : (decode integerModel (encode integerTrace)).isOk = true := by decide

end ClaferCompiler.Tests.BehavioralFullStructure
