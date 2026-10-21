module

public import ClaferCompiler.Driver
public import ClaferCompiler.Frontend.Parser

public section
open ClaferCompiler Lean
namespace ClaferCompiler.Tests.Driver

/-! [utest->req~compiler-cli~1]
[utest->req~compiler-diagnostics~1] -/
def run : IO Unit := do
  let input ← IO.FS.readFile "tests/fixtures/cli/optional.json"
  let bounds ← IO.FS.readFile "tests/fixtures/cli/bounds.json"
  let .ok result := Driver.compileText "optional.json" input "bounds.json" bounds
    | throw (IO.userError "compileText")
  let .error diagnostic := Frontend.parse "é.cfr" "é\r\n["
    | throw (IO.userError "expected EOF diagnostic")
  let mappings := result.mappings.map fun m => Json.mkObj [
    ("name", toJson m.name), ("startByte", toJson m.startByte), ("endByte", toJson m.endByte),
    ("displayName", toJson (m.source.map (·.displayName))),
    ("file", toJson (m.source.bind (·.logicalFile))),
    ("sourceStart", toJson (m.source.bind (·.startByte))),
    ("sourceEnd", toJson (m.source.bind (·.endByte)))]
  IO.println (Json.mkObj [
    ("text", toJson result.text), ("ids", toJson (result.declarations.map (·.id))),
    ("mappings", toJson mappings), ("diagnostic", Driver.sourceDiagnosticJson diagnostic),
    ("relatedDiagnostic", Driver.sourceDiagnosticJson
      { diagnostic with related := #[⟨"other.cfr", 1, 3⟩] })]).compress

end ClaferCompiler.Tests.Driver
