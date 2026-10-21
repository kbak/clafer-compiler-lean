module

public import tests.StructuralAlloyNative
public import ClaferCompiler.Backend.Alloy.StructuralRepresentation

@[expose] public section
namespace ClaferCompiler.Tests.StructuralRepresentationNative
open Backend.Alloy Backend.Alloy.Structural
open Tests.StructuralAlloy

/-! Native representation checks across the existing structural corpus, with
explicit malformed-input and lost-occurrence mutations.
[utest->req~compiler-structural-representation~1] -/

def sameInstance (a b : Instance) : Bool := a.signatures == b.signatures && a.fields == b.fields

def renameAtoms (i : Instance) : Instance where
  signatures := i.signatures.map (List.map fun x => 37 * x + 1009)
  fields := i.fields.map (List.map (List.map fun x => 37 * x + 1009))

def run : IO Unit := do
  let mut roundtrips := 0
  for fixture in cases do
    let .ok v := IR.Structural.validateRaw fixture.input
      | throw (IO.userError s!"admission: {fixture.label}")
    for i in [fixture.candidate, renameAtoms fixture.candidate] do
      match decode v.toLayout i with
      | .ok o =>
        unless sameInstance (encode v.toLayout o) i do
          throw (IO.userError s!"round trip changed data: {fixture.label}")
        roundtrips := roundtrips + 1
      | .error e =>
        unless (fixture.label == "missing root" || fixture.label == "multiple roots" ||
            fixture.label == "exact root zero still compiles") &&
            e == .rootNotSingleton do
          throw (IO.userError s!"unexpected decode error: {fixture.label}: {repr e}")
  unless roundtrips == 72 do throw (IO.userError s!"lost fixtures: {roundtrips}")
  let .ok v := IR.Structural.validateRaw bag | throw (IO.userError "bag admission")
  let .ok o := decode v.toLayout bagInstance | throw (IO.userError "bag decoding")
  let d : Fin bag.declarations.size := ⟨2, by decide⟩
  unless o.heads d == [2, 3] && o.containment d == [(0, 2), (0, 3)] &&
      o.dereference d == [(2, 1), (3, 1)] do
    throw (IO.userError "collapsed reference occurrence identity")
  let dangling := { bagInstance with fields :=
    [[[0, 1]], [[0, 2], [0, 3]], [[2, 9001], [3, 1]]] }
  let .ok danglingObs := decode v.toLayout dangling | throw (IO.userError "dangling tuple decoding")
  unless sameInstance (encode v.toLayout danglingObs) dangling &&
      danglingObs.dereference d == [(2, 9001), (3, 1)] do
    throw (IO.userError "decoder silently removed an out-of-carrier tuple")
  let malformed : List Instance := [
    { bagInstance with signatures := [[0, 1, 2, 3], [0], [1]] },
    { bagInstance with signatures := [[0, 1, 2, 3], [0], [1], [2, 2, 3]] },
    { bagInstance with fields := [[[0, 1]], [[0, 2], [0, 3]]] },
    { bagInstance with fields := [[[0, 1, 2]], [[0, 2], [0, 3]], [[2, 1], [3, 1]]] },
    { bagInstance with fields := [[[0, 1]], [[0, 2], [0, 3]], [[2, 1], [2, 1], [3, 1]]] }]
  for i in malformed do
    match decode v.toLayout i with
    | .error .malformedInstance => pure ()
    | _ => throw (IO.userError "malformed candidate was not rejected")
  let outside := { bagInstance with signatures := [[1, 2, 3], [0], [1], [2, 3]] }
  match decode v.toLayout outside with
  | .error .rootOutsideObjects => pure ()
  | _ => throw (IO.userError "root outside live objects was not rejected")
  IO.println "72 corpus round trips; 1 dangling-tuple round trip; 2 distinct bag occurrences; 9 rejecting decoder cases"

end ClaferCompiler.Tests.StructuralRepresentationNative
