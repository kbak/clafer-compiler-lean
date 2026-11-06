module

public import ClaferCompiler.Frontend.Parser
public import ClaferCompiler.Frontend.BehavioralDeclarations
public import ClaferCompiler.IR.BehavioralSupport
public import ClaferCompiler.IR.BehavioralArithmetic

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralStructural
open IR.BehavioralStructural IR.BehavioralArithmetic

/-- Original fixture: concrete refinement, nested authored abstract reference,
ordinary inherited child, and a reference inherited by a refined-parent subtype. -/
def core : Core 7 := ⟨⟨#v[
  { id := 10, name := "root", origin := .syntheticRoot },
  { id := 11, name := "Target", parent := some 0 },
  { id := 12, name := "System", parent := some 0 },
  { id := 13, name := "Port", parent := some 2, isAbstract := true, reference := .bag 1 },
  { id := 14, name := "SubSystem", parent := some 0, super := some 2 },
  { id := 15, name := "port", parent := some 4, super := some 3 },
  { id := 16, name := "entry", parent := some 3, isAbstract := true, reference := .bag 1 }
  ], 0⟩, #v[false, false, false, true, false, false, false], Vector.replicate 7 (.bounds {})⟩

def certificate : IR.Structural.Certificate 7 :=
  ⟨#v[0, 1, 1, 2, 1, 2, 3], #v[0, 0, 0, 0, 1, 1, 0], Vector.replicate 7 false⟩

def validated : Validated 7 := ⟨core, certificate, analyze core, by decide, by decide⟩

def support : IR.Expr.Support 4 4 :=
  ⟨#v[15, 11, 14, 13], #v[
    {owner := 15, kind := .dereference, source := 0, target := 1},
    {owner := 15, kind := .target, source := 2, target := 1},
    {owner := 15, kind := .inclusion, source := 0, target := 3},
    {owner := 15, kind := .dereference, source := 0, target := 1}], 0,
    Vector.replicate 4 false⟩

def fail (message : String) : IO α := throw (IO.userError message)

def accepted (source : String) : IO Unit := do
  let .ok doc := Frontend.parse "behavioral.cfr" source | fail ("parse: " ++ source)
  let .ok _ := Frontend.BehavioralResolution.elaborate profile doc | fail ("resolve: " ++ source)

def rejected (source : String) (code : String) : IO Unit := do
  let .ok doc := Frontend.parse "behavioral.cfr" source | fail ("parse: " ++ source)
  match Frontend.BehavioralResolution.elaborate profile doc with
  | .ok _ => fail ("unexpected acceptance: " ++ source)
  | .error e => unless e.code == code do fail ("expected " ++ code ++ ", got " ++ e.code)

def sourceFixtures : IO Unit := do
  for name in ["refinement", "groups", "integers"] do
    let file := "tests/fixtures/behavioral-structural/" ++ name ++ ".cfr"
    let .ok doc := Frontend.parse file (← IO.FS.readFile file) | fail file
    let .ok result := Frontend.BehavioralResolution.elaborate profile doc | fail file
    let rows := result.candidate.core.declarations.toList
    for row in rows do
      unless row.origin != .user || row.source.isSome do fail "lost source span"
    if name == "groups" then
      let find := fun name => rows.find? (·.name == name)
      let .some optional := find "defaultOptional" | fail "optional child missing"
      let .some mandatory := find "defaultMandatory" | fail "mandatory child missing"
      unless optional.localBounds == ⟨0, .finite 1⟩ && mandatory.localBounds == ⟨1, .finite 1⟩ do
        fail "keyword versus numeric inherited defaults"
      let .some chosen := (List.finRange result.count).find? (fun i => (result.admitted.core.structural.get i).name == "chosen")
        | fail "group owner missing"
      let names := (childDeclarations result.admitted chosen).map (fun i => (result.admitted.core.structural.get i).name)
      unless names == ["inherited", "extra"] do fail "effective child union"
    if name == "integers" then
      unless (rows.filter (·.origin == .integer)).length == 1 do fail "primitive aliases split identity"
  for length in List.range 20 do
    let source := String.join ((List.range (length + 1)).map fun i =>
      "D" ++ toString i ++ (if i = length then "" else " : D" ++ toString (i + 1)) ++ "\n")
    accepted source

-- [utest->req~compiler-behavioral-structural-bridge~1]
def run : IO Unit := do
  sourceFixtures
  let .ok _ := validate profile core certificate | fail "rich core admission"
  let .error _ := validate "m1-effective" core certificate | fail "profile separation"
  let .error _ := IR.Structural.validate core.structural certificate | fail "static admission widened"
  let .ok _ := IR.BehavioralSupport.resolve validated support | fail "inherited typed support"
  let wrong := { support with maps := support.maps.set 0 { support.maps[0] with target := 2 } }
  let .error _ := IR.BehavioralSupport.resolve validated wrong | fail "fabricated dereference target"
  let integerFlag := { support with integer := support.integer.set 0 true }
  let .error _ := IR.BehavioralSupport.resolve validated integerFlag | fail "fabricated primitive domain"
  let .some view := IR.BehavioralSupport.referenceView validated 5 | fail "inherited reference view"
  unless view.head == 5 && view.owner == 3 && view.target == 1 do fail "reference identities"
  let chained := { core with structural := { core.structural with
    declarations := core.structural.declarations.set 1 { core.structural.get 1 with reference := .bag 2 } } }
  let .ok chainedValid := validate profile chained certificate | fail "reference target with own reference"
  let .some oneStep := IR.BehavioralSupport.referenceView chainedValid 5 | fail "chained view"
  unless oneStep.target == 1 do fail "implicit double dereference"
  let badParents := { core with structural := { core.structural with
    declarations := core.structural.declarations.set 5 { core.structural.get 5 with parent := some 1 } } }
  let .error _ := validate profile badParents certificate | fail "wrong refined parent"
  let badPrimitive := { core with structural := { core.structural with
    declarations := core.structural.declarations.set 1 { core.structural.get 1 with origin := .string } } }
  let .error unsupported := validate profile badPrimitive certificate | fail "runtime string domain"
  unless unsupported.category == .unsupported do fail "unsupported primitive category"
  let badAnalysis : Analysis 7 := { validated.analysis with referenceOwners := validated.analysis.referenceOwners.set 5 (some 6) }
  if decide (badAnalysis.Valid core) then fail "fabricated reference owner"
  let lostAncestor : Analysis 7 := { validated.analysis with ancestors := validated.analysis.ancestors.set 5 [5] }
  if decide (lostAncestor.Valid core) then fail "missing inherited ancestor"
  accepted "Target\nSystem\n  abstract Port ->> Target\n    entry ->> Target\nSubSystem : System\n  port : Port\n"
  accepted "Base\nChild : Base\n"
  accepted "Target\nNarrow : Target\nabstract Ref ->> Target\nr : Ref -> Narrow\n"
  accepted "abstract xor Choice\n  a ?\nchosen : Choice\n  b ?\n"
  accepted "xor Empty ?\n"
  accepted "abstract opt Choice\n  a\nchosen : Choice\n  b\n"
  rejected "System\n  abstract Port\nOther\n  p : Port\n" "behavioral.structural-admission"
  rejected "Target\nOther\nabstract Ref ->> Target\nr : Ref ->> Other\n" "behavioral.structural-admission"
  rejected "Target\nabstract Ref -> Target\nr : Ref ->> Target\n" "behavioral.structural-admission"
  rejected "A : B\nB : A\n" "resolve.inheritance-cycle"
  rejected "A : Missing\n" "resolve.missing-name"
  rejected "A : integer\n" "resolve.primitive-super"
  let .ok doc := Frontend.parse "static.cfr" "Base\nChild : Base\n" | fail "static parser"
  let .error _ := Frontend.Resolution.elaborate doc | fail "static concrete-super guard"
  let .error _ := Frontend.parse "static.cfr" "enum Colour = Red | Blue\n" | fail "static enum guard"
  let token : Frontend.Token := ⟨"Colour", ⟨"enum.cfr", 5, 11⟩, 1, 6, 6⟩
  let red := { token with text := "Red", span := ⟨"enum.cfr", 14, 17⟩ }
  let blue := { token with text := "Blue", span := ⟨"enum.cfr", 20, 24⟩ }
  let .ok expanded := Frontend.BehavioralDeclarations.expandEnum profile token [red, blue] ⟨"enum.cfr", 0, 24⟩
    | fail "enum expansion"
  let enumDoc : Frontend.Document := ⟨"enum.cfr", "enum Colour = Red | Blue", expanded.elements⟩
  let .ok enumResolved := Frontend.BehavioralResolution.elaborate profile enumDoc | fail "enum resolution"
  unless enumResolved.count == 4 && expanded.finalLiterals == [red, blue] do fail "enum inventory/finality"
  let .error _ := Frontend.BehavioralDeclarations.expandEnum profile token [] token.span
    | fail "empty enum"
  let .error _ := Frontend.BehavioralDeclarations.expandEnum "m1-effective" token [red] token.span
    | fail "enum profile separation"
  let .error error := Frontend.BehavioralDeclarations.constantInitializer { token with text := ":=" }
    (.name token) (.name token) (.name red) | fail "default initializer"
  unless error.category == .unsupported do fail "default initializer category"
  let .ok (.binary implication (.unary presence _ _) (.binary equal _ _ _) span) :=
    Frontend.BehavioralDeclarations.constantInitializer { token with text := "=" }
    (.name token) (.name token) (.name red) | fail "constant initializer"
  unless implication.text == "=>" && presence.text == "some" && equal.text == "=" &&
    span.startByte == token.span.startByte && span.endByte == red.span.endByte do
    fail "initializer shape/spans"
  unless coerce [] == 0 && coerce [3, 3] == 3 && extract [] == none do fail "set conversion"
  unless Fold.sum.eval [[some 3, some 3], [some 3]] == some 9 do fail "aggregate occurrences"
  unless Fold.product.eval [[some 3, some 3]] == some 9 && Fold.product.eval [] == some 1 do fail "product occurrences"
  unless Fold.product.eval [[some 0, none]] == none do fail "strict aggregate"
  unless minimum [] == [] && maximum [] == [] && minimum [3, -4, 0] == [-4] do fail "empty extrema"
  unless Binary.divide.eval (some (-7)) (some 3) == some (-2) &&
    Binary.remainder.eval (some (-7)) (some 3) == some (-1) do fail "signed arithmetic"
  unless Binary.divide.eval (some 0) (some 0) == none &&
    Binary.multiply.eval (some 0) none == none &&
    conditional (some false) (none : Option Int) (some 1) == none do fail "strict definedness"
  let .ok _ := validateOperation .multiply 8 ⟨-4, 4⟩ ⟨-4, 4⟩ | fail "safe product range"
  let .error _ := validateOperation .multiply 4 ⟨-4, 4⟩ ⟨-4, 4⟩ | fail "unsafe product range"
  let .error _ := validateOperation .divide 8 ⟨-4, 4⟩ ⟨-1, 1⟩ | fail "zero divisor range"
  let .ok _ := validateOperation .divide 8 ⟨-4, 4⟩ ⟨1, 3⟩ | fail "nonzero divisor range"
  unless (productRange 0 ⟨0, 0⟩).fits 2 && (setSumRange 0 ⟨-100, 100⟩).fits 1 do
    fail "empty aggregate bounds"
  IO.println "behavioral structural, resolution, support, enums, initializers and arithmetic checks passed"

end ClaferCompiler.Tests.BehavioralStructural
