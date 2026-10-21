module

public import ClaferCompiler.Backend.Alloy.InheritedViews

@[expose] public section
namespace ClaferCompiler.Tests.InheritedNative
open Backend.Alloy
open Backend.Alloy.Inherited

/-! Original resolved Appendix 6 structural inventory, source IDs d01–d26,
synthetic root 0 and integer declaration 27. No c01–c12 constraint bodies.
[utest->req~compiler-inherited-realization~1] -/
def raw : IR.Inherited.Raw := ⟨⟨#[
  { id := 0, name := "Sing", origin := .syntheticRoot, localBounds := ⟨1, .finite 1⟩ },
  { id := 1, name := "options", isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 2, name := "size", parent := some 1, isAbstract := true, localBounds := ⟨1, .finite 1⟩, groupBounds := ⟨1, .finite 1⟩ },
  { id := 3, name := "small", parent := some 2, isAbstract := true, localBounds := ⟨0, .finite 1⟩ },
  { id := 4, name := "large", parent := some 2, isAbstract := true, localBounds := ⟨0, .finite 1⟩ },
  { id := 5, name := "cache", parent := some 1, isAbstract := true, localBounds := ⟨0, .finite 1⟩ },
  { id := 6, name := "size", parent := some 5, reference := .set 27, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 7, name := "fixed", parent := some 6, isAbstract := true, localBounds := ⟨0, .finite 1⟩ },
  { id := 8, name := "comp", isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 9, name := "version", parent := some 8, reference := .set 27, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 10, name := "ECU", super := some 8, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 11, name := "display", super := some 8, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 12, name := "server", parent := some 11, reference := .set 10, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 13, name := "options", parent := some 11, super := some 1, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 14, name := "plaECU", super := some 10, isAbstract := true, localBounds := ⟨1, .finite 1⟩ },
  { id := 15, name := "plaDisplay", parent := some 14, super := some 11, isAbstract := true, localBounds := ⟨1, .finite 2⟩ },
  { id := 16, name := "ECU1", parent := some 0, super := some 14, localBounds := ⟨1, .finite 1⟩ },
  { id := 17, name := "ECU2", parent := some 0, super := some 14, localBounds := ⟨0, .finite 1⟩ },
  { id := 18, name := "master", parent := some 17, reference := .set 16, localBounds := ⟨1, .finite 1⟩ },
  { id := 19, name := "telematics", parent := some 0, localBounds := ⟨1, .finite 1⟩ },
  { id := 20, name := "channel", parent := some 19, localBounds := ⟨1, .finite 1⟩, groupBounds := ⟨1, .finite 1⟩ },
  { id := 21, name := "single", parent := some 20, localBounds := ⟨0, .finite 1⟩ },
  { id := 22, name := "dual", parent := some 20, localBounds := ⟨0, .finite 1⟩ },
  { id := 23, name := "extraDisplay", parent := some 19, localBounds := ⟨0, .finite 1⟩ },
  { id := 24, name := "size", parent := some 19, localBounds := ⟨1, .finite 1⟩, groupBounds := ⟨1, .finite 1⟩ },
  { id := 25, name := "small", parent := some 24, localBounds := ⟨0, .finite 1⟩ },
  { id := 26, name := "large", parent := some 24, localBounds := ⟨0, .finite 1⟩ },
  { id := 27, name := "int", origin := .integer, parent := some 0 }], 0,
  #[0, 0, 1, 2, 2, 1, 2, 3, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3, 1],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 2, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]⟩,
  #[false, true, false, false, false, false, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[0, 6, 7, 8, 8, 7, 8, 9, 5, 6, 3, 4, 5, 5, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3, 1]⟩

def observation : Structural.Observation 28 := ⟨[100, 201, 202, 301, 302, 401, 402, 403, 404, 501, 502, 601, 602, 701, 702, 801, 802, 901, 999, 1001, 1002, 1003, 1004, 1005], 100,
  (fun d => (#v[[100], [601, 602], [701, 702], [801], [802], [], [], [], [201, 202, 301, 302], [401, 402, 403, 404], [201, 202], [301, 302], [501, 502], [601, 602], [201, 202], [301, 302], [201], [202], [901], [1001], [1002], [1003], [], [], [1004], [], [1005], [999]])[d]),
  (fun d => (#v[[], [], [(601, 701), (602, 702)], [(701, 801)], [(702, 802)], [], [], [], [], [(201, 401), (202, 402), (301, 403), (302, 404)], [], [], [(301, 501), (302, 502)], [(301, 601), (302, 602)], [], [(201, 301), (202, 302)], [(100, 201)], [(100, 202)], [(202, 901)], [(100, 1001)], [(1001, 1002)], [(1002, 1003)], [], [], [(1001, 1004)], [], [(1004, 1005)], [(100, 999)]])[d]),
  (fun d => (#v[[], [], [], [], [], [], [], [], [], [(401, 999), (402, 999), (403, 999), (404, 999)], [], [], [(501, 201), (502, 202)], [], [], [], [], [], [(901, 201)], [], [], [], [], [], [], [], [], []])[d])⟩

def limits : Structural.Bounds :=
  ⟨(List.range 28).map (fun d => (d, ⟨30, false⟩)), 30, 12⟩

def badOwner : Structural.Observation 28 :=
  { observation with containment := fun d => if d == 9 then
      (202, 401) :: observation.containment d else observation.containment d }

/-- Remove the second option-size choice entirely. Its optional local bounds
still hold; the ordinary inherited xor field now has zero children. -/
def badGroup : Structural.Observation 28 :=
  { observation with
    objects := observation.objects.filter (· != 802),
    heads := fun d => (observation.heads d).filter (· != 802),
    containment := fun d => (observation.containment d).filter (fun pair => pair.2 != 802) }

def badCover : Structural.Observation 28 :=
  { observation with
    objects := 777 :: observation.objects,
    heads := fun d => if d == 1 then 777 :: observation.heads d else observation.heads d }

def require (p : Bool) (label : String) : IO Unit :=
  unless p do throw (IO.userError label)

def run : IO Unit := do
  let .ok v := IR.Inherited.validateRaw raw | throw (IO.userError "Appendix 6 admission")
  let .ok c := compile v limits | throw (IO.userError "Appendix 6 compilation")
  require (c.declarations.length == 28 && c.module.raw.schema.signatures.length == 29)
    "copied or missing declaration"
  require ((c.obligations.filter fun tag => match tag with
    | .structural (.abstractCover _) => true | _ => false).length == 5) "explicit family inventory"
  require ((raw.structural.declarations.filter (·.super.isSome)).size == 7) "super inventory"
  require ((raw.structural.declarations.filter (fun d => d.groupBounds == ⟨1, .finite 1⟩)).size == 3)
    "xor inventory"
  for (label, o, expected) in [("positive", observation, true),
      ("ownership", badOwner, false), ("inherited xor", badGroup, false), ("cover", badCover, false)] do
    let i := encode v o
    let .ok result := evaluate c.module i | throw (IO.userError s!"evaluation: {label}")
    require (result == expected) label
    let .ok decoded := decode v i | throw (IO.userError s!"decode: {label}")
    require (decoded.objects == o.objects && (encode v decoded).fields == i.fields &&
      (encode v decoded).signatures == i.signatures) s!"round trip: {label}"
  require (viewHeads observation 9 16 == [401] && viewHeads observation 9 17 == [402])
    "context field identity"
  require (viewContains observation 9 16 == [(201, 401)] &&
    viewDeref observation 9 16 == [(401, 999)]) "context link identity"
  require (match IR.Structural.validateRaw raw.structural with | .error _ => true | _ => false)
    "M1 boundary widened"
  for r in [{ raw with explicitAbstract := #[] }, { raw with realizationRanks := #[] },
      { raw with realizationRanks := Array.replicate 28 0 },
      { raw with explicitAbstract := raw.explicitAbstract.set! 2 true },
      { raw with structural := { raw.structural with
          declarations := raw.structural.declarations.set! 27
            { raw.structural.declarations[27] with origin := .string } } }] do
    require (match IR.Inherited.validateRaw r with | .error _ => true | _ => false) "invalid admission"
  IO.println "Appendix 6: 28 declarations, 7 super edges, 5 families, 3 xor groups; 4 candidates, context identity, 5 admission mutations"

end ClaferCompiler.Tests.InheritedNative
