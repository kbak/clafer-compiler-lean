module

public import tests.AlloyText

@[expose] public section

open ClaferCompiler.Backend.Alloy ClaferCompiler.Backend.Alloy.Text
open ClaferCompiler.Tests.AlloyText

namespace ClaferCompiler.Tests.AlloyTextOracle

/-- Exercise successful API behavior and determinism, never discard rejected
members of the finite property domain. External Python checks the resulting
source-map slices and sends every output through the real Analyzer parser. -/
def run (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let root := System.FilePath.mk directory
  IO.FS.createDirAll root
  let allModules := modules ++ generated
  for (m, i) in allModules.zipIdx do
    let .ok c := check m | throw (IO.userError s!"admission {i}")
    let names := hostileNames m
    let .ok out := render c names | throw (IO.userError s!"render {i}: {serialize m}")
    let .ok again := render c names | throw (IO.userError "repeat render")
    if out.text != again.text || out.mappings != again.mappings then
      throw (IO.userError "nondeterministic rendering")
    let .ok anonymous := render c (anonymousNames m) | throw (IO.userError "anonymous render")
    if out.text != anonymous.text then throw (IO.userError "labels affected syntax")
    for entry in out.mappings do
      if entry.source != sourceFor names entry.symbol then throw (IO.userError "lost source label")
    if out.mappings.length != m.schema.signatures.length + m.schema.fields.length then
      throw (IO.userError "missing mapping")
    let maps := out.mappings.map fun entry =>
      s!"{entry.name}\t{entry.startByte}\t{entry.endByte}\n"
    IO.FS.writeFile (root / s!"case_{i}.als") out.text
    IO.FS.writeFile (root / s!"case_{i}.map") (String.join maps)
  for text in negativeParses do
    if (parse text).isSome then throw (IO.userError s!"bad text parsed: {text}")
  for (body, i) in bodies.zipIdx do
    let some value := ClaferCompiler.Tests.AlloyCore.observe
      (ClaferCompiler.Tests.AlloyCore.model body) ClaferCompiler.Tests.AlloyCore.fixture
      | throw (IO.userError "undefined expected observation")
    IO.FS.writeFile (root / s!"case_{i}.truth") (if value then "true" else "false")
  -- Exercise every adversarial source label, plus original UTF-8 spans.
  let .ok c := check (ClaferCompiler.Tests.AlloyCore.model .truth) | throw (IO.userError "fixture")
  for label in labels do
    let source : SourceName := ⟨label, some "model.clafer", some 2, some 8⟩
    let names : Names := ⟨[some source, some source], [some source]⟩
    let .ok out := render c names | throw (IO.userError "hostile names")
    if out.text != serialize c.raw || !(out.mappings.all (fun m => m.source == some source)) then
      throw (IO.userError "label or span preservation")
  if (render c ⟨[], []⟩).isOk then throw (IO.userError "metadata length")
  if (render c ⟨[some ⟨"bad", some "x", some 9, some 2⟩, none], [none]⟩).isOk then
    throw (IO.userError "metadata interval")
  -- Names cover all four namespaces and include a larger decimal boundary.
  let symbols := (List.range 1000).flatMap fun i =>
    [Symbol.signature i, Symbol.field i, Symbol.binder i, Symbol.auxiliary i]
  if !(symbols.all (fun s => readSymbol s.name == some s)) then
    throw (IO.userError "name decoding")
  IO.println s!"{allModules.length} target modules; {symbols.length} names; {negativeParses.length} parser mutations"

end ClaferCompiler.Tests.AlloyTextOracle
