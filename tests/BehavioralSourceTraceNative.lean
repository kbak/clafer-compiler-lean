module

public import ClaferCompiler.Driver.BehavioralSourceTrace

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralSourceTrace
open Lean

-- [utest->req~compiler-behavioral-integration~1]
-- [utest->req~compiler-behavioral-qualification~1]
def run (args : List String) : IO Unit := do
  let [sourcePath, tracePath] := args | throw (IO.userError "expected source and Analyzer trace")
  let source ← IO.FS.readFile sourcePath
  let trace ← IO.FS.readFile tracePath
  let result : Except Driver.Diagnostic Json := do
    let p ← Frontend.Behavioral.parseAndElaborate IR.BehavioralStructural.profile "input.cfr" source
      |>.mapError Driver.Diagnostic.ofSource
    let v := p.elaborated.model.structural
    let ⟨_, _, l⟩ ← Driver.BehavioralSourceTrace.decode v "trace.json" trace
    return Driver.BehavioralSourceTrace.json v.core.structural l
  IO.println (match result with
    | .ok j => j
    | .error d => Json.mkObj [("status", toJson "malformed"), ("diagnostic", d.json)]).compress

end ClaferCompiler.Tests.BehavioralSourceTrace
