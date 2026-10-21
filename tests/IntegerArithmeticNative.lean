module

public import ClaferCompiler.Backend.Alloy.Print
public import ClaferCompiler.Backend.Alloy.Semantics

@[expose] public section
namespace ClaferCompiler.Tests.IntegerArithmeticNative
open Backend.Alloy

/-! [utest->req~compiler-target-arithmetic~1]
[utest->req~compiler-alloy-text~1] -/

def model (width : Nat) (body : Formula) : Module :=
  ⟨⟨[], []⟩, [], ⟨.run, body, [], width⟩⟩

def badIntermediate : Integer := .subtract (.add (.literal 7) (.literal 1)) (.literal 1)
def comparison (n : Integer) (v : Int) : Formula := .compare .eq n (.literal v)

def cases : List (Module × Bool) := [
  (model 4 (comparison (.add (.literal 2) (.literal 3)) 5), true),
  (model 4 (comparison (.subtract (.literal 2) (.literal 5)) (-3)), true),
  (model 4 (comparison (.subtract (.literal 5) (.literal 2)) (-3)), false),
  (model 4 (.compare .lt (.subtract (.literal 2) (.literal 5)) (.literal 0)), true),
  (model 4 (.compare .lt (.literal 0) (.subtract (.literal 2) (.literal 5))), false),
  (model 4 (comparison (.add (.subtract (.literal 2) (.literal 5)) (.literal 4)) 1), true),
  (model 4 (comparison (.subtract (.literal 0) (.literal 7)) (-7)), true),
  (model 4 (comparison (.add (.literal (-8)) (.literal 0)) (-8)), true),
  (model 4 (comparison (.subtract (.literal 7) (.literal 0)) 7), true),
  (model 1 (comparison (.add (.literal (-1)) (.literal 0)) (-1)), true),
  (model 4 (.implies .falsity (comparison (.subtract (.literal 2) (.literal 5)) 0)), true),
  (model 4 (.neg (comparison (.subtract (.literal 2) (.literal 5)) 0)), true),
  (model 4 (comparison (.subtract (.literal 5) (.subtract (.literal 2) (.literal 1))) 4), true),
  (model 4 (comparison (.subtract (.subtract (.literal 5) (.literal 2)) (.literal 1)) 4), false),
  (model 16 (comparison (.subtract (.literal (-32767)) (.literal 1)) (-32768)), true),
  (model 16 (comparison (.add (.literal 32766) (.literal 1)) 32767), true),
  (⟨⟨[{}], []⟩, [], ⟨.run, comparison (.add (.count (.sig 0)) (.literal 2)) 5,
    [⟨3, true⟩], 4⟩⟩, true),
  (⟨⟨[{}], []⟩, [], ⟨.run, comparison (.subtract (.literal 2) (.count (.sig 0))) (-1),
    [⟨3, true⟩], 4⟩⟩, true),
  (⟨⟨[{}], []⟩, [], ⟨.run, .all (.sig 0)
    (.compare .eq (.add (.count (.var 0)) (.literal 2)) (.literal 3)), [⟨2, true⟩], 4⟩⟩, true),
  (⟨⟨[{}, {}], [⟨0, 1, .set⟩]⟩,
    [.equal (.field 0) (.product (.sig 0) (.sig 1))], ⟨.run,
    comparison (.subtract (.count (.field 0)) (.count (.sig 0))) 2,
    [⟨2, true⟩, ⟨2, true⟩], 4⟩⟩, true)
]

def run (directory : String) : IO Unit := do
  let root := System.FilePath.mk directory
  IO.FS.createDirAll root
  let mut boundaries := 0
  for width in List.range' 1 16 do
    -- Expected admission is calculated directly from signed mathematical bounds.
    let lo := -(2 ^ (width - 1) : Int)
    let hi := (2 ^ (width - 1) : Int) - 1
    let values := [lo - 1, lo, lo + 1, -1, 0, 1, hi - 1, hi, hi + 1].eraseDups
    let inRange := fun v => lo ≤ v && v ≤ hi
    for x in values do
      for y in values do
        for add in [true, false] do
          let value := if add then x + y else x - y
          let term := if add then Integer.add (.literal x) (.literal y)
            else Integer.subtract (.literal x) (.literal y)
          let expected := inRange x && inRange y && inRange value
          let m := model width (comparison term 0)
          if term.safe m 0 != expected || term.eval width ⟨[], []⟩ [] !=
              (if expected then some value else none) then
            throw (IO.userError s!"boundary mismatch width={width} x={x} y={y} add={add}")
          boundaries := boundaries + 1
  for body in [comparison badIntermediate 7,
      .neg (comparison badIntermediate 7),
      .implies .falsity (comparison badIntermediate 7),
      .all (.empty .unary) (comparison badIntermediate 7)] do
    if (check (model 4 body)).isOk then throw (IO.userError "hidden overflow admitted")
  for code in [[], [.add], [.literal 1, .subtract], [.literal 1, .literal 2],
      [.literal 1, .literal 2, .add, .add], [.count (.sig 99)]] do
    if (check (model 4 (comparison ⟨code⟩ 0))).isOk then
      throw (IO.userError "malformed integer code admitted")
  for width in [0, 17] do
    if (check (model width (comparison (.literal 0) 0))).isOk then
      throw (IO.userError "invalid width admitted")
  -- Correlation is deliberately not used to relax conservative interval bounds.
  let countDifference := Integer.subtract (.count (.sig 0)) (.count (.sig 0))
  let unsafeCount : Module := ⟨⟨[{}], []⟩, [],
    ⟨.run, comparison countDifference 0, [⟨8, false⟩], 4⟩⟩
  if (check unsafeCount).isOk then throw (IO.userError "unsafe count intermediate")
  for (item, index) in cases.zipIdx do
    let (m, expected) := item
    let .ok checked := check m | throw (IO.userError s!"admission {index}")
    let .ok rendered := Text.render checked (Text.anonymousNames m)
      | throw (IO.userError s!"round trip {index}: {Text.serialize m}")
    let .ok repeated := Text.render checked (Text.anonymousNames m)
      | throw (IO.userError "repeat render")
    if rendered.text != repeated.text then throw (IO.userError "nondeterminism")
    let candidate : Instance := if index < 16 then ⟨[], []⟩ else if index == 19 then
      ⟨[[0, 1], [2, 3]], [[[0, 2], [0, 3], [1, 2], [1, 3]]]⟩
      else ⟨[List.range ((m.command.scopes.head?).map Scope.size |>.getD 0)], []⟩
    let .ok value := evaluate checked candidate | throw (IO.userError s!"undefined {index}")
    if value != expected then throw (IO.userError s!"meaning {index}")
    IO.FS.writeFile (root / s!"case_{index}.als") rendered.text
    IO.FS.writeFile (root / s!"case_{index}.truth") (if expected then "true" else "false")
  -- The kernel reconstruction check must reject valid-Alloy noncanonical forms.
  let text := Text.serialize (model 4 (comparison (.subtract (.literal 2) (.literal 5)) (-3)))
  for replacement in ["sub", "+", "unknown"] do
    if (Text.parse (text.replace "minus [" (replacement ++ " ["))).isSome then
      throw (IO.userError "noncanonical arithmetic parsed")
  IO.println s!"{boundaries} arithmetic boundaries; {cases.length} serialized cases"

end ClaferCompiler.Tests.IntegerArithmeticNative
