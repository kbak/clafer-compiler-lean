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

def bind (source : String) : IO Behavioral.Document := do
  match Behavioral.parseBehavioral IR.BehavioralStructural.profile "lookup.cfr" source with
  | .ok doc => pure doc
  | .error e => throw (IO.userError (diagnostic e))

-- [utest->req~compiler-behavioral-structural-bridge~1]
-- [utest->req~compiler-behavioral-frontend~1]
/-- Wrong targets can satisfy structural admission; independent source
correspondence must still reject them. -/
def mutations : IO Unit := do
  for (source, targetName) in [
      ("abstract Person\n  abstract Head\nBob : Person\n  abstract Head : Head\n  h : Bob.Head\n", "Person.Head"),
      ("abstract Head\nOwner\n  Head\n  h : Head\n", "Head")] do
    let doc := ← bind source
    let .ok bound := Behavioral.bindDeclarations IR.BehavioralStructural.profile doc
      | throw (IO.userError "positive lookup control rejected")
    let projected := Behavioral.declarationDocument doc bound.projectedElements
    let c := bound.resolved.candidate
    let some i := (List.finRange bound.resolved.count).find? (fun i => (c.core.get i).name == "h")
      | throw (IO.userError "missing h")
    let some j := (List.finRange bound.resolved.count).find? (fun j =>
        (c.paths[j].map (pathName projected)).getD "" == targetName)
      | throw (IO.userError "missing wrong-target control")
    let wrong := { (c.core.get i) with super := some j }
    let changed := { c with core := { c.core with declarations := c.core.declarations.set i wrong } }
    let core := Frontend.BehavioralResolution.core projected changed
    unless decide (IR.BehavioralStructural.checks core c.certificate (IR.BehavioralStructural.analyze core)) do
      throw (IO.userError "wrong-target witness must remain structurally admissible")
    if decide (Frontend.BehavioralResolution.Elaboration projected changed) then
      throw (IO.userError "source correspondence accepted wrong target")
    let absent := { (c.core.get i) with super := none }
    let dropped := { c with core := { c.core with declarations := c.core.declarations.set i absent } }
    if decide (Frontend.BehavioralResolution.Elaboration projected dropped) then
      throw (IO.userError "source correspondence accepted dropped super path")

-- [utest->req~compiler-behavioral-frontend~1]
def variants : IO Unit := do
  let first := "abstract Family\n  abstract Person\n    abstract Head\n"
  let second := "family : Family\n  person : Family.Person\n    h : Head\n"
  let expected := "ok|family->Family;family.person->Family.Person;family.person.h->Family.Person.Head"
  for source in [first ++ second, second ++ first] do
    for variant in [source, source.replace "\n" "\r\n", "// Café\n" ++ source,
        source.replace "\n" " // comment\n\n"] do
      unless render true "lookup.cfr" variant == expected do
        throw (IO.userError "forward/order/whitespace lookup identity changed")
  let ambiguous := "abstract A\n  abstract P\nabstract B\n  abstract P\nh : P.Missing\n"
  let doc := ← bind ambiguous
  let .error e := Behavioral.bindDeclarations IR.BehavioralStructural.profile doc
    | throw (IO.userError "ambiguous first segment accepted")
  unless e.code == "resolve.ambiguous-name" && e.related.size == 2 &&
      e.related.all (fun span => span.endByte - span.startByte == 1) do
    throw (IO.userError "ambiguity did not retain all candidate locations")

def run : IO Unit := do
  mutations
  variants
  let files ← System.FilePath.readDir "tests/fixtures/super-lookup"
  for entry in files do
    if entry.path.extension == some "cfr" then
      let source ← IO.FS.readFile entry.path
      IO.println (entry.fileName ++ "\t" ++ render false entry.fileName source ++
        "\t" ++ render true entry.fileName source)

end ClaferCompiler.Tests.SuperLookup
