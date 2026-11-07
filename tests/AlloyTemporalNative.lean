module

public import tests.AlloyTemporal
public import tests.BehavioralPartialNative
public import tests.BehavioralFullNative
public import tests.BehavioralFullExpressionsNative
public import tests.BehavioralFullModifiersNative
public import tests.BehavioralFullPatternsNative
public import tests.BehavioralFullTemporalNative
public import tests.BehavioralFullStructureNative
public import tests.BehavioralFullFrontendNative

@[expose] public section
namespace ClaferCompiler.Tests.AlloyTemporalNative
open Backend.Alloy.Temporal
open Backend.Alloy.Temporal.Text
open Backend.Alloy.Text (Names SourceName sourceFor)
open AlloyTemporal

-- [utest->req~compiler-alloy-temporal-text~1]
def run (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected directory")
  let root := System.FilePath.mk directory
  IO.FS.createDirAll root
  let .ok full := BehavioralFull.cases | throw (IO.userError "full compilation")
  let .ok expressions := BehavioralFullExpressions.cases | throw (IO.userError "expression compilation")
  let .ok patterns := BehavioralFullPatterns.cases | throw (IO.userError "pattern compilation")
  let .ok modifiers := BehavioralFullModifiers.cases | throw (IO.userError "modifier compilation")
  let temporal ← match BehavioralFullTemporal.cases with
    | .ok cases => pure cases
    | .error error => throw (IO.userError ("temporal compilation: " ++ error))
  let structureCases ← match BehavioralFullStructureNative.cases with
    | .ok cases => pure cases
    | .error error => throw (IO.userError ("structure compilation: " ++ error))
  let frontend ← match BehavioralFullFrontend.cases with
    | .ok cases => pure cases
    | .error error => throw (IO.userError ("frontend compilation: " ++ error))
  let modules := (cases ++ BehavioralPartial.cases ++ full ++ expressions ++ patterns ++ modifiers ++ temporal ++ structureCases ++ frontend).map (fun (id, expected, m) => (id, some expected, m)) ++
    syntaxBodies.zipIdx.map (fun (p, i) => (s!"syntax-{i}", none, base p))
  let hostile : SourceName := ⟨"var\n/* cc0 λ */", some "input.cfr", some 2, some 8⟩
  for (id, expected, m) in modules do
    let .ok checked := check m | throw (IO.userError s!"admission {id}")
    let names : Names := ⟨List.replicate m.schema.declarations.signatures.length (some hostile),
      List.replicate m.schema.declarations.fields.length (some hostile)⟩
    let .ok out := render checked names | throw (IO.userError s!"render {id}: {serialize m}")
    let .ok again := render checked names | throw (IO.userError "repeat render")
    let .ok anonymous := render checked (anonymousNames m) | throw (IO.userError "anonymous render")
    if out.text != again.text || out.mappings != again.mappings || out.text != anonymous.text then
      throw (IO.userError "determinism or metadata affected text")
    if out.mappings.length != names.signatures.length + names.fields.length +
        (m.schema.declarations.signatures.filter (·.scalar)).length then
      throw (IO.userError "missing map")
    if !(out.mappings.all fun entry => entry.source == sourceFor names entry.symbol) then
      throw (IO.userError "lost source metadata")
    IO.FS.writeFile (root / s!"{id}.als") out.text
    IO.FS.writeFile (root / s!"{id}.map") (String.join (out.mappings.map fun entry =>
      s!"{entry.name}\t{entry.startByte}\t{entry.endByte}\n"))
    let scalarFields := m.schema.declarations.signatures.zipIdx.filterMap fun (sig, i) =>
      if sig.scalar then some s!"this/cc{i * 4}/cc{i * 4 + 3}\n" else none
    IO.FS.writeFile (root / s!"{id}.integer-fields") (String.join scalarFields)
    let scopes := m.command.scopes.zipIdx.map fun (scope, i) =>
      s!"cc{i * 4}\t{scope.size}\t{scope.exact}\n"
    IO.FS.writeFile (root / s!"{id}.bounds") (s!"{m.command.bitwidth}\t{m.command.minSteps}\t{m.command.maxSteps}\n" ++ String.join scopes)
    if let some expected := expected then
      IO.FS.writeFile (root / s!"{id}.expected") (if expected then "sat" else "bounded_unsat")
  let text := serialize (base p)
  let mutations := [text ++ "run { ( no none ) } for 4 Int , 1 .. 4 steps\n",
    text.replace "some" "sometime", text.replace "cc0" "cc1",
    text.replace "1 .. 4" "1 ... 4", text.replace " steps" " step",
    text.replace "( some ( cc0 ) )" "( some ( cc2 ) )",
    text.replace "( some ( cc0 ) )" "( some ( cc0 )", text.replace "var sig" "variable sig"]
  for bad in mutations do
    if (parse bad).isSome then throw (IO.userError s!"malformed text accepted: {bad}")
  for depth in [0, 1, 16, 128] do
    let m := base ((List.range depth).foldl (fun p _ => .unary .after p) p)
    let .ok checked := check m | throw (IO.userError "deep admission")
    if !(render checked (anonymousNames m)).isOk then throw (IO.userError "deep reconstruction")
  let .ok checked := check (base p) | throw (IO.userError "base admission")
  if (render checked ⟨[], []⟩).isOk then throw (IO.userError "malformed names accepted")
  if (render checked ⟨[some ⟨"bad", some "x", some 9, some 2⟩], []⟩).isOk then
    throw (IO.userError "invalid span accepted")
  IO.println s!"{modules.length} temporal modules; {mutations.length} rejecting parser mutations"

end ClaferCompiler.Tests.AlloyTemporalNative
