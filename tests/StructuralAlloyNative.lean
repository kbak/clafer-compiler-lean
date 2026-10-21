module

public import ClaferCompiler.Backend.Alloy.Structural
public import ClaferCompiler.Backend.Alloy.Semantics
public import tests.StructuralNative

@[expose] public section
namespace ClaferCompiler.Tests.StructuralAlloy
open Backend.Alloy
open Backend.Alloy.Structural
open ClaferCompiler.Tests.Structural (root child abstractType raw emptyModel two referenceCycle inheritance unusedChain)

/-! Hand-authored candidates: atom IDs are opaque; tables explicitly use the
documented target layout. These tests do not implement a production decoder.
[utest->req~compiler-structural-encoding~1] -/

def bounds (r : IR.Structural.Raw) (size : Nat := 4) (width : Nat := 5) : Structural.Bounds :=
  ⟨r.declarations.toList.map (fun d => (d.id, ⟨size, false⟩)), size, width⟩

def observe (r : IR.Structural.Raw) (b : Structural.Bounds) (i : Instance) : Option Bool :=
  match compileRaw r b with
  | .error _ => none
  | .ok compiled => match evaluate compiled.module i with
    | .error _ => none
    | .ok result => some result

def bag := raw #[root, child 200, { child 300 with reference := .bag 200 }]
  #[0, 1, 1] #[0, 0, 0] #[false, false, false]
def set := { bag with declarations := #[root, child 200, { child 300 with reference := .set 200 }] }
def bagInstance : Instance := ⟨[[0, 1, 2, 3], [0], [1], [2, 3]],
  [[[0, 1]], [[0, 2], [0, 3]], [[2, 1], [3, 1]]]⟩
def twoInstance : Instance := ⟨[[0, 1, 2], [0], [1, 2]], [[[0, 1], [0, 2]]]⟩
def optional := { two with declarations := #[root, { child 200 with localBounds := ⟨0, .finite 1⟩ }] }
def xor := { two with declarations := #[{ root with groupBounds := ⟨1, .finite 1⟩ }, child 200] }
def bagGroup (k : Nat) := { bag with declarations :=
  #[{ root with groupBounds := ⟨k, .finite k⟩ }, child 200, { child 300 with reference := .bag 200 }] }
def owners := raw #[root, child 10, child 20,
  { child 30 with parent := some 10, reference := .set 20 }]
  #[0, 1, 1, 2] #[0, 0, 0, 0] #[false, false, false, false]
def ownersInstance : Instance := ⟨[[0, 1, 2, 3, 4, 5], [0], [1, 2], [3], [4, 5]],
  [[[0, 1], [0, 2]], [[0, 3]], [[1, 4], [2, 5]], [[4, 3], [5, 3]]]⟩
def nested := raw #[root, child 10, { child 20 with parent := some 10 }]
  #[0, 1, 2] #[0, 0, 0] #[false, false, false]
def abstractLeaf := raw #[root, abstractType 20] #[0, 0] #[0, 0] #[false, false]
def leafInstance : Instance := ⟨[[0, 1], [0], [1]], []⟩
def inheritedInstance : Instance := ⟨[[0, 1], [0], [1], [1]], [[[0, 1]]]⟩
def siblings := raw #[root, abstractType 20,
  { child 200 with super := some 20 }, { child 300 with super := some 20 }]
  #[0, 0, 1, 1] #[0, 0, 1, 1] #[false, false, false, false]
/-- Input order is deliberately the reverse of super order, and root is not first. -/
def reversed := raw #[{ child 200 with super := some 30 },
  { abstractType 30 with super := some 20 }, root, abstractType 20]
  #[1, 0, 0, 0] #[2, 1, 0, 0] #[false, false, false, false]

structure Case where
  label : String
  input : IR.Structural.Raw
  limits : Structural.Bounds
  candidate : Instance
  expected : Bool

def sample (label : String) (r : IR.Structural.Raw) (i : Instance) (expected : Bool)
    (size : Nat := 4) : Case := ⟨label, r, bounds r size, i, expected⟩

def cases : List Case := [
  sample "root only and empty group" emptyModel ⟨[[17], [17]], []⟩ true,
  sample "missing root" emptyModel ⟨[[], []], []⟩ false,
  sample "multiple roots" emptyModel ⟨[[0, 1], [0, 1]], []⟩ false,
  sample "object outside all source extents" emptyModel ⟨[[0, 1], [0]], []⟩ false,
  sample "root freshness" two ⟨[[0], [0], [0]], [[[0, 0]]]⟩ false,
  sample "ordinary containment" two twoInstance true,
  sample "missing owner" two { twoInstance with fields := [[[0, 1]]] } false,
  sample "owner first orientation" two { twoInstance with fields := [[[1, 0], [2, 0]]] } false,
  sample "optional upper bound" optional twoInstance false,
  sample "local lower bound" { two with declarations :=
      #[root, { child 200 with localBounds := ⟨1, .unbounded⟩ }] }
    ⟨[[0], [0], []], [[]]⟩ false,
  sample "empty realized xor" xor ⟨[[0], [0], []], [[]]⟩ false,
  sample "one realized xor" xor ⟨[[0, 1], [0], [1]], [[[0, 1]]]⟩ true,
  sample "group upper bound" xor twoInstance false,
  sample "bag distinct heads one target" bag bagInstance true,
  sample "set duplicate owner target" set bagInstance false,
  sample "bag group counts three heads" (bagGroup 3) bagInstance true,
  sample "bag group does not count two target values" (bagGroup 2) bagInstance false,
  sample "reference totality" bag { bagInstance with fields :=
    [[[0, 1]], [[0, 2], [0, 3]], [[2, 1]]] } false,
  sample "reference functionality" bag
    ⟨[[0, 1, 2, 3, 4], [0], [1, 4], [2, 3]],
      [[[0, 1], [0, 4]], [[0, 2], [0, 3]], [[2, 1], [2, 4], [3, 1]]]⟩ false 5,
  sample "different owners may share target" owners ownersInstance true 6,
  sample "set key remains per owner" owners { ownersInstance with fields :=
    [[[0, 1], [0, 2]], [[0, 3]], [[1, 4], [1, 5]], [[4, 3], [5, 3]]] } false 6,
  sample "two parents rejected" nested
    ⟨[[0, 1, 2, 3], [0], [1, 2], [3]], [[[0, 1], [0, 2]], [[1, 3], [2, 3]]]⟩ false,
  sample "cross containment incomparable overlap" nested
    ⟨[[0, 1], [0], [1], [1]], [[[0, 1]], [[1, 1]]]⟩ false,
  sample "inherited object identity" inheritance inheritedInstance true,
  sample "missing super membership" inheritance
    { inheritedInstance with signatures := [[0, 1], [0], [], [1]] } false,
  sample "uncovered abstract object" inheritance
    ⟨[[0, 1, 2], [0], [1, 2], [1]], [[[0, 1]]]⟩ false,
  sample "sibling overlap" siblings
    ⟨[[0, 1], [0], [1], [1], [1]], [[[0, 1]], [[0, 1]]]⟩ false,
  sample "empty abstract leaf" abstractLeaf ⟨[[0], [0], []], []⟩ true,
  sample "nonempty abstract leaf" abstractLeaf leafInstance false,
  sample "zero unused abstract chain" unusedChain ⟨[[0], [0], [], []], []⟩ true,
  sample "nonempty unused abstract chain" unusedChain ⟨[[0, 1], [0], [1], [1]], []⟩ false,
  sample "reverse order abstract chain" reversed
    ⟨[[0, 1], [0], [1], [1], [1]], [[[0, 1]]]⟩ true,
  sample "reference cycles" referenceCycle
    ⟨[[0, 1, 2], [0], [1], [2]], [[[0, 1]], [[1, 2]], [[0, 2]], [[2, 1]]]⟩ true,
  sample "zero interval empty group" { emptyModel with declarations :=
      #[{ root with groupBounds := ⟨0, .finite 0⟩ }] } ⟨[[0], [0]], []⟩ true,
  sample "empty parent vacuity" { nested with declarations :=
      #[root, child 10, { child 20 with parent := some 10, localBounds := ⟨2, .finite 3⟩ }] }
    ⟨[[0], [0], [], []], [[], []]⟩ true,
  ⟨"total budget is not summed inherited scopes", inheritance,
    { bounds inheritance with objects := 2 }, inheritedInstance, true⟩,
  ⟨"total budget constraint", two, { bounds two with objects := 2 }, twoInstance, false⟩,
  ⟨"exact root zero still compiles", emptyModel,
    ⟨[(100, ⟨0, true⟩)], 0, 1⟩, ⟨[[], []], []⟩, false⟩,
  ⟨"exact declaration scope", two, ⟨[(100, ⟨1, true⟩), (200, ⟨3, true⟩)], 4, 5⟩,
    twoInstance, false⟩
]

def outcome (result : Except Structural.Error Compiled) : String := match result with
  | .ok _ => "ok"
  | .error (.source d) => d.code
  | .error .malformedBounds => "malformedBounds"
  | .error .unsupportedBounds => "unsupportedBounds"
  | .error .internalTarget => "internalTarget"

/-- Remove one generated obligation to show that the negative fixture detects it. -/
def without (c : Compiled) (tag : Obligation) : Module :=
  { c.module.raw with facts :=
    (c.module.raw.facts.zip c.obligations).filterMap fun (f, label) =>
      if label == tag then none else some f }

def run : IO Unit := do
  for c in cases do
    unless observe c.input c.limits c.candidate == some c.expected do
      throw (IO.userError s!"{c.label}: wrong outcome or compilation/evaluation error")
  let rejects := [
    ("duplicate scopes", { bounds two with declarations := [(100, ⟨1, false⟩), (100, ⟨1, false⟩)] }, "malformedBounds"),
    ("missing scope", { bounds two with declarations := [(100, ⟨1, false⟩)] }, "malformedBounds"),
    ("unknown scope", { bounds two with declarations := [(100, ⟨1, false⟩), (999, ⟨1, false⟩)] }, "malformedBounds"),
    ("extra scope", { bounds two with declarations := (999, ⟨1, false⟩) :: (bounds two).declarations }, "malformedBounds"),
    ("zero width", { bounds two with bitwidth := 0 }, "unsupportedBounds"),
    ("large width", { bounds two with bitwidth := 17 }, "unsupportedBounds")]
  for (label, b, expected) in rejects do
    unless outcome (compileRaw two b) == expected do throw (IO.userError label)
  unless outcome (compileRaw optional (bounds optional 8 4)) == "unsupportedBounds" &&
      outcome (compileRaw optional (bounds optional 8 5)) == "ok" do
    throw (IO.userError "count range boundary")
  let literal := { two with declarations := #[root, { child 200 with localBounds := ⟨8, .finite 8⟩ }] }
  unless outcome (compileRaw literal (bounds literal 1 4)) == "unsupportedBounds" do
    throw (IO.userError "literal range boundary")
  -- Every native IR admission fixture is also exercised through compilation.
  for (label, r, expected) in ClaferCompiler.Tests.Structural.cases do
    unless outcome (compileRaw r (bounds r 8 8)) == expected do
      throw (IO.userError s!"source boundary: {label}")
  let .ok c := compileRaw reversed (bounds reversed) | throw (IO.userError "ordering")
  unless c.declarations.map (fun d => (d.id, d.signature)) ==
      [(200, 4), (30, 3), (100, 1), (20, 2)] do
    throw (IO.userError "source-to-target identity map")
  let .ok reordered := compileRaw reversed
      { bounds reversed with declarations := (bounds reversed).declarations.reverse }
    | throw (IO.userError "bounds order")
  unless c.module.raw.command.scopes.map (fun s => (s.size, s.exact)) ==
      reordered.module.raw.command.scopes.map (fun s => (s.size, s.exact)) do
    throw (IO.userError "bound input order changed allocation")
  for (r, i, tag) in [
      (emptyModel, ⟨[[], []], []⟩, Obligation.root),
      (two, { twoInstance with fields := [[[0, 1]]] }, Obligation.ownership 200),
      (optional, twoInstance, Obligation.localBounds 200),
      (xor, ⟨[[0], [0], []], [[]]⟩, Obligation.groupBounds 100),
      (set, bagInstance, Obligation.setKey 300),
      (abstractLeaf, leafInstance, Obligation.abstractCover 20)] do
    let .ok original := compileRaw r (bounds r) | throw (IO.userError "mutation input")
    unless (evaluate original.module i).toOption == some false do throw (IO.userError "negative fixture")
    let .ok mutant := check (without original tag) | throw (IO.userError "mutation syntax")
    unless (evaluate mutant i).toOption == some true do throw (IO.userError "mutation escaped detection")
  IO.println s!"{cases.length} structural candidates; 28 admission fixtures; 6 obligation mutations; bounds and allocation passed"

end ClaferCompiler.Tests.StructuralAlloy
