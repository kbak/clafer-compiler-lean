module

public import ClaferCompiler.Driver.Decode
public import ClaferCompiler.Driver.Source
public import ClaferCompiler.Driver.Behavioral
public import ClaferCompiler.Driver.BehavioralSource
public import ClaferCompiler.Backend.Alloy.Print

@[expose] public section
/-! Native resolved-IR and source-text integration.
[impl->req~compiler-cli~1]
[impl->req~compiler-pipeline-correctness~1]
[impl->req~compiler-build~1] -/

namespace ClaferCompiler.Driver
open Backend.Alloy

def version : String := "clafer-compiler 0.1.0\nprofiles: m1-effective; m2-source (selected static)\n" ++
  "ir: clafer-ir/1; bounds: clafer-bounds/1 (IR), clafer-bounds/2 (source)\n" ++
  "semantics: a18890612e38872f3fb5842ed323042aea34e1ed\n" ++
  "haskell-reference: f6ca5b887d7bacc09915c6fc0278064c8371beac\n" ++
  "source-text: selected static; compilation does not run a solver"
  ++ "\nbehavioral: behavioral-core/1; clafer-behavioral-ir/1; clafer-behavioral-bounds/1"
  ++ "\nbehavioral-source: behavioral-0.5.7-candidate/v1; clafer-behavioral-bounds/2"
  ++ "\nbehavioral-source-policy: literal-empty-navigation/1; warnings: clafer-warning/1"

def usage : String := "usage: clafer-compiler --version | --help\n" ++
  "       clafer-compiler compile-ir INPUT --bounds BOUNDS --output OUTPUT\n" ++
  "       clafer-compiler compile-source INPUT --bounds BOUNDS --output OUTPUT\n" ++
  "       clafer-compiler compile-behavioral-ir INPUT --bounds BOUNDS --output OUTPUT\n" ++
  "       clafer-compiler compile-behavioral-source INPUT --bounds BOUNDS --output OUTPUT\n" ++
  "         [--assertion N | --scenario FILE [--owner ID]]\n" ++
  "         [--objects N] [--bitwidth N] [--diagnostics text|json]\n" ++
  "Behavioral compilation additionally accepts --format alloy|json.\n" ++
  "Use - for stdin/stdout (only one input may use stdin).\n" ++
  "Bounds are required; no inference or solver execution."

def response (args : List String) : Option String :=
  if args == ["--version"] then some version else none

structure Options where
  input : String
  bounds : String
  output : String
  objects : Option Nat := none
  bitwidth : Option Nat := none
  source : Bool := false
  behavioral : Bool := false
  formatJson : Bool := false
  behavioralSource : Bool := false
  assertion : Option Nat := none
  scenario : Option String := none
  owner : Option Nat := none

def argumentError (message : String) : Diagnostic :=
  { code := "cli.arguments", phase := "arguments", message }

def optionPairs (args : List String) : Except Diagnostic (List (String × String)) := do
  let (pending, pairs) ← args.foldlM (fun (state : Option String × List (String × String)) value =>
    match state.1 with
    | none => pure (some value, state.2)
    | some key => do
      if !["--bounds", "--output", "--objects", "--bitwidth", "--diagnostics", "--format",
          "--assertion", "--scenario", "--owner"].contains key then
        throw (argumentError "unknown option")
      if state.2.any (fun entry => entry.1 == key) then throw (argumentError "duplicate option")
      pure (none, (key, value) :: state.2)) (none, [])
  if pending.isSome then throw (argumentError "missing option value")
  return pairs.reverse

def options (args : List String) : Except Diagnostic Options := do
  let command :: input :: rest := args | throw (argumentError usage)
  if !["compile-ir", "compile-source", "compile-behavioral-ir", "compile-behavioral-source"].contains command then
    throw (argumentError usage)
  if input.isEmpty then throw (argumentError "empty input path")
  let pairs ← optionPairs rest
  let get := fun key => (pairs.find? (fun entry => entry.1 == key)).map Prod.snd
  let some bounds := get "--bounds" | throw (argumentError "--bounds is required")
  let some output := get "--output" | throw (argumentError "--output is required")
  if bounds.isEmpty || output.isEmpty then throw (argumentError "empty path")
  if input == "-" && bounds == "-" then throw (argumentError "both inputs cannot use stdin")
  if let some format := get "--diagnostics" then
    if format != "text" && format != "json" then throw (argumentError "unknown diagnostic format")
  if let some format := get "--format" then
    if !(command == "compile-behavioral-ir" || command == "compile-behavioral-source") ||
        (format != "alloy" && format != "json") then
      throw (argumentError "--format alloy|json requires behavioral compilation")
  if ["--assertion", "--scenario", "--owner"].any (fun key => (get key).isSome) &&
      command != "compile-behavioral-source" then
    throw (argumentError "property/scenario options require compile-behavioral-source")
  if (get "--assertion").isSome && (get "--scenario").isSome then
    throw (argumentError "select either an assertion or a scenario")
  if (get "--owner").isSome && (get "--scenario").isNone then
    throw (argumentError "--owner requires --scenario")
  if get "--scenario" == some "" then throw (argumentError "empty scenario path")
  if get "--scenario" == some "-" && (input == "-" || bounds == "-") then
    throw (argumentError "only one input may use stdin")
  let number := fun key => (get key).mapM fun value => do
    let some n := value.toNat? | throw (argumentError "expected natural-number option")
    if value != toString n then throw (argumentError "expected canonical natural-number option")
    return n
  return ⟨input, bounds, output, ← number "--objects", ← number "--bitwidth",
    command == "compile-source", command == "compile-behavioral-ir", get "--format" == some "json",
    command == "compile-behavioral-source", ← number "--assertion", get "--scenario", ← number "--owner"⟩

/-- Recognize diagnostic pairs only in the option suffix, never path arguments. -/
def jsonDiagnostics (args : List String) : Bool :=
  (args.drop 2).zipIdx.any fun (key, i) =>
    i % 2 == 0 && key == "--diagnostics" && args[i + 3]? == some "json"

def sourceName (d : Structural.DeclarationMap) : Text.SourceName := {
  displayName := d.name, logicalFile := d.source.map (·.file)
  startByte := d.source.map (·.startByte), endByte := d.source.map (·.endByte) }

def declarationNames (m : Module) (ds : List Structural.DeclarationMap) : Text.Names := {
  signatures := (List.range m.schema.signatures.length).map fun i =>
    (ds.find? (fun d => d.signature == i)).map sourceName
  fields := (List.range m.schema.fields.length).map fun i =>
    (ds.find? (fun d => d.containment == some i || d.dereference == some i)).map sourceName }

/-- Pure handoff retains source IDs and generated byte maps for both input profiles. -/
structure Product where
  text : String
  declarations : List Structural.DeclarationMap
  mappings : List Text.Mapping

def renderProduct (m : CheckedModule) (declarations : List Structural.DeclarationMap) :
    Except Diagnostic Product := do
  let rendered ← Text.render m (declarationNames m.raw declarations) |>.mapError fun _ =>
    { code := "compiler.render", phase := "serialization", category := .operational
      message := "generated text failed checked reconstruction" : Diagnostic }
  return ⟨rendered.text, declarations, rendered.mappings⟩

def compileText (inputFile input boundsFile boundsText : String)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Product := do
  let raw ← Decode.document inputFile input
  let admitted ← IR.Structural.validateDocument "clafer-ir/1" "m1-effective" raw
    |>.mapError (admissionDiagnostic inputFile)
  let b ← Decode.bounds boundsFile boundsText
  let b := { b with objects := objects.getD b.objects, bitwidth := bitwidth.getD b.bitwidth }
  let compiled ← Structural.compile admitted b
    |>.mapError (backendDiagnostic boundsFile (admissionDiagnostic inputFile))
  renderProduct compiled.module compiled.declarations

def compileSource (inputFile input boundsFile boundsText : String)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Product := do
  let compiled ← Source.compile inputFile input boundsFile boundsText objects bitwidth
  renderProduct compiled.module compiled.encoded.declarations

def logicalFile (path : String) : String :=
  if path == "-" then "<stdin>" else (System.FilePath.mk path).fileName.getD "<input>"

def readInput (path : String) : IO (Except Diagnostic String) := do
  try
    let bytes ← if path == "-" then (← IO.getStdin).readBinToEnd else IO.FS.readBinFile path
    return match String.fromUTF8? bytes with
    | some text => .ok text
    | none => .error {
        code := "input.utf8", phase := "decode", file := logicalFile path
        message := "input is not valid UTF-8" }
  catch _ =>
    return .error {
      code := "io.read", phase := "io", category := .operational
      file := logicalFile path, message := "cannot read input" }

/-- Exclusive sibling creation keeps rename on the destination filesystem.
Only an owned temporary file is removed on failure; output is never pre-truncated. -/
def writeOutput (path text : String) : IO Unit := do
  if path == "-" then
    let stdout ← IO.getStdout
    stdout.putStr text
    stdout.flush
  else
    let target := System.FilePath.mk path
    let parent := target.parent.getD "."
    let temp := parent / s!".clafer-compiler-{← IO.rand 0 18446744073709551615}.tmp"
    let handle ← IO.FS.Handle.mk temp .writeNew
    try
      handle.putStr text
      handle.flush
      IO.FS.rename temp target
    catch error =>
      try IO.FS.removeFile temp catch _ => pure ()
      throw error

def emitDiagnostic (json : Bool) (d : Diagnostic) : IO UInt32 := do
  (← IO.getStderr).putStrLn (if json then d.json.compress else d.text)
  return d.category.exitCode

-- [impl->req~compiler-behavioral-integration~1]
def behavioralQuery (opts : Options) : IO (Except Diagnostic BehavioralSource.Query) := do
  if let some index := opts.assertion then return .ok (.check index)
  if let some path := opts.scenario then
    return (← readInput path).map fun source =>
      .run ⟨logicalFile path, source, opts.owner⟩
  return .ok .model

def run (args : List String) : IO UInt32 := do
  if let some text := response args then
    IO.println text
    return 0
  if args == ["--help"] then
    IO.println usage
    return 0
  let json := jsonDiagnostics args
  match options args with
  | .error d => emitDiagnostic json d
  | .ok opts =>
    match ← readInput opts.input with
    | .error d => emitDiagnostic json d
    | .ok input =>
      match ← readInput opts.bounds with
      | .error d => emitDiagnostic json d
      | .ok bounds =>
        let query ← behavioralQuery opts
        let result := if opts.behavioralSource then
          (query.bind fun q => BehavioralSource.compileReport (logicalFile opts.input) input
            (logicalFile opts.bounds) bounds q opts.objects opts.bitwidth).map (fun p =>
              (if opts.formatJson then p.product.json.compress ++ "\n" else p.product.text, p.warnings))
        else if opts.behavioral then
          (Behavioral.compileText (logicalFile opts.input) input (logicalFile opts.bounds)
            bounds opts.objects opts.bitwidth).map (fun p =>
              (if opts.formatJson then p.json.compress ++ "\n" else p.text, []))
        else if opts.source then
          (compileSource (logicalFile opts.input) input (logicalFile opts.bounds) bounds opts.objects opts.bitwidth).map (fun p => (p.text, []))
        else (compileText (logicalFile opts.input) input (logicalFile opts.bounds) bounds opts.objects opts.bitwidth).map (fun p => (p.text, []))
        match result with
        | .error d => emitDiagnostic json d
        | .ok result =>
          try
            writeOutput opts.output result.1
            for w in result.2 do
              (← IO.getStderr).putStrLn (if json then (BehavioralSource.warningJson w).compress
                else BehavioralSource.warningText w)
            return 0
          catch _ => emitDiagnostic json {
            code := "io.write", phase := "io", category := .operational, file := logicalFile opts.output
            message := "cannot write output" }

end ClaferCompiler.Driver
