module

public import ClaferCompiler.Frontend.Behavioral.Parser
public import ClaferCompiler.Frontend.Behavioral.Declarations

@[expose] public section
namespace ClaferCompiler.Tests.SuperLookup
open Frontend Frontend.Resolution

/-- Authored declaration paths, independent of numeric compiler IDs and backend names. -/
def pathName (doc : Frontend.Document) (path : Path) : String :=
  String.intercalate "." ((List.range path.length).map fun i =>
    ((headerAt doc (path.take (i + 1))).map (·.name.text)).getD "?")

def edges (doc : Frontend.Document) (c : Candidate n) : String :=
  String.intercalate ";" ((List.finRange n).filterMap fun i => do
    let target ← (c.core.get i).super
    let sourcePath ← c.paths[i]
    let targetPath ← c.paths[target]
    return pathName doc sourcePath ++ "->" ++ pathName doc targetPath)

def diagnostic (d : Diagnostic) : String :=
  s!"error|{d.code}|{if d.category == .unsupported then "unsupported" else "malformed"}|{d.primary.startByte}|{d.primary.endByte}"

-- [utest->req~compiler-resolution~1]
-- [utest->req~compiler-behavioral-structural-bridge~1]
-- [utest->req~compiler-behavioral-frontend~1]
/-- Observe both production parser/resolver paths without changing their policy.
The Python assertions distinguish current behavior from proposed lookup rules. -/
def render (behavioral : Bool) (file source : String) : String :=
  let result : Except Diagnostic String := do
    if behavioral then
      let doc ← Behavioral.parseBehavioral IR.BehavioralStructural.profile file source
      let bound ← Behavioral.bindDeclarations IR.BehavioralStructural.profile doc
      return edges (Behavioral.declarationDocument doc bound.projectedElements) bound.resolved.candidate
    else
      let doc ← Frontend.parse file source
      let bound ← Resolution.elaborate doc
      return edges doc bound.candidate
  match result with
  | .error d => diagnostic d
  | .ok rows => "ok|" ++ rows

def run : IO Unit := do
  let files ← System.FilePath.readDir "tests/fixtures/super-lookup"
  for entry in files do
    if entry.path.extension == some "cfr" then
      let source ← IO.FS.readFile entry.path
      IO.println (entry.fileName ++ "\t" ++ render false entry.fileName source ++
        "\t" ++ render true entry.fileName source)

end ClaferCompiler.Tests.SuperLookup
