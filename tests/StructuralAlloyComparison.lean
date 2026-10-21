module

public import tests.StructuralAlloyNative
public import ClaferCompiler.SemanticsBridge.Structural
public meta import tests.StructuralAlloyNative
public meta import ClaferCompiler.SemanticsBridge.Structural

@[expose] public section
namespace ClaferCompiler.Tests.StructuralAlloy
open Backend.Alloy Backend.Alloy.Structural

/-! Finite test adapter only. Compare independently defined upstream truth with
actual generated target truth, retaining reference heads and relation tuples.
This is bounded evidence, not a representation or preservation theorem.
[utest->req~compiler-structural-encoding~1] -/

def sourceObservation (v : IR.Structural.Validated n) (c : Compiled) (i : Instance)
    (b : Structural.Bounds) : Bool := Id.run do
  -- A source candidate needs a distinguished root even for an empty/invalid
  -- target carrier. That case is represented by an unused, nonmember root.
  let objects : List Nat := match i.signatures[0]?.getD [] with | [] => [0] | xs => xs
  have nonempty : 0 < objects.length := by
    cases h : i.signatures[0]?.getD [] <;> simp [objects, h]
  let mapping := fun d : Fin n => declarationMap v d
  let extent := fun d : Fin n => i.signatures[(mapping d).signature]?.getD []
  let roots := extent v.core.root
  let root := ((List.finRange objects.length).find? fun j =>
    roots.contains objects[j]).getD ⟨0, nonempty⟩
  let relation := fun field : Option Nat => (field.bind (i.fields[·]?)).getD []
  let candidate : Clafer.Verification.Candidate n := {
    size := objects.length, root
    head := fun d x => (extent d).contains objects[x]
    contains := fun d p x => (relation (mapping d).containment).contains [objects[p], objects[x]]
    deref := fun d x t => (relation (mapping d).dereference).contains [objects[x], objects[t]] }
  let fits := objects.length ≤ b.objects && (List.finRange n).all fun d =>
    match b.declarations.find? (fun entry => entry.1 == (v.core.get d).id) with
    | none => false
    | some (_, scope) => if scope.exact then (extent d).length == scope.size
      else (extent d).length ≤ scope.size
  -- Check the adapter's identity map against the actual output as well.
  let mapsMatch := c.declarations.map (fun d => (d.id, d.signature)) ==
    (List.finRange n).map (fun d => ((v.core.get d).id, (mapping d).signature))
  return mapsMatch && fits && Clafer.Verification.check (SemanticsBridge.Structural.interpret v.core) candidate

def select (mask : Nat) (edges : List (List Nat)) : List (List Nat) :=
  edges.zipIdx.filterMap fun (edge, bit) => if mask.testBit bit then some edge else none

/-- All 64 subsets of two owner/head and four head/target tuples, for each of
bag, set, exact-four group and exact-three group inputs: 256 supplied candidates.
The five-atom carrier and extents stay fixed; missing/multiple links are retained. -/
def generatedCases : List Case :=
  [bag, set, bagGroup 4, bagGroup 3].zipIdx.flatMap fun (r, model) =>
    (List.range 4).flatMap fun parents => (List.range 16).map fun refs =>
      { label := s!"model={model}, parents={parents}, refs={refs}"
        input := r, limits := bounds r 5
        candidate := ⟨[[0, 1, 2, 3, 4], [0], [1, 4], [2, 3]],
          [[[0, 1], [0, 4]], select parents [[0, 2], [0, 3]],
            select refs [[2, 1], [2, 4], [3, 1], [3, 4]]], []⟩
        expected := false } -- Expected outcomes come from the independent checker.

def runComparison : IO Unit := do
  let mut positives := 0
  for fixture in cases ++ generatedCases do
    let .ok v := IR.Structural.validateRaw fixture.input
      | throw (IO.userError s!"admission: {fixture.label}")
    let .ok c := compile v fixture.limits
      | throw (IO.userError s!"compilation: {fixture.label}")
    let .ok actual := evaluate c.module fixture.candidate
      | throw (IO.userError s!"evaluation: {fixture.label}")
    let expected := sourceObservation v c fixture.candidate fixture.limits
    unless actual == expected do throw (IO.userError s!"source/target discrepancy: {fixture.label}")
  for fixture in generatedCases do
    if observe fixture.input fixture.limits fixture.candidate == some true then
      positives := positives + 1
  unless positives == 10 do throw (IO.userError "generated comparison lost its satisfying witnesses")
  IO.println s!"{cases.length} fixtures and {generatedCases.length} generated candidates agree with upstream; {positives} generated positives"

end ClaferCompiler.Tests.StructuralAlloy

#eval ClaferCompiler.Tests.StructuralAlloy.runComparison
