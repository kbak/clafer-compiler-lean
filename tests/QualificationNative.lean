module

public import ClaferCompiler.Driver

@[expose] public section
/-! External measurement probe; never linked into the production executable.
[impl->req~compiler-performance~1] -/
namespace ClaferCompiler.Tests.Qualification
open Frontend Backend.Alloy Driver Lean

/-- Keep the computation inside the timed IO action. Inputs are already read;
the caller consumes each result before proceeding to the next stage. -/
@[noinline] def timed (action : Unit → Except String α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let result ← IO.ofExcept (action ())
  let finish ← IO.monoNanosNow
  return (result, finish - start)

def run (args : List String) : IO Unit := do
  let [input, boundsFile, output] := args | throw (IO.userError "expected INPUT BOUNDS OUTPUT")
  let source ← IO.FS.readFile input
  let boundsText ← IO.FS.readFile boundsFile
  let (doc, parsing) ← timed fun _ => parse (logicalFile input) source |>.mapError (·.message)
  let (resolved, resolution) ← timed fun _ => Resolution.elaborate doc |>.mapError (·.message)
  let (attached, constraints) ← timed fun _ =>
    MonadAttach.attach (Constraints.elaborate doc resolved) |>.mapError (·.message)
  let prepared : Pipeline.Prepared := ⟨doc, resolved, attached.val, attached.property⟩
  let v := Pipeline.inherited doc resolved
  let (b, boundsDecode) ← timed fun _ => Source.bounds (logicalFile boundsFile) boundsText
    |>.mapError (·.message)
  let (compiled, backend) ← timed fun _ => do
    let ranges ← Source.intervals (logicalFile boundsFile) v b |>.mapError (·.message)
    let encoded ← Expressions.compile v (Source.targetBounds v b) ranges prepared.bodies
      |>.mapError fun e => (Source.backendDiagnostic (logicalFile boundsFile) e).message
    let target ← check { encoded.module.raw with facts := encoded.module.raw.facts ++
      [Source.objectBudget v b.structural.objects] } |>.mapError fun _ => "target check failed"
    return (target, encoded.declarations)
  let (rendered, rendering) ← timed fun _ =>
    Text.render compiled.1 (declarationNames compiled.1.raw compiled.2)
      |>.mapError fun _ => "checked rendering failed"
  IO.FS.writeFile output rendered.text
  IO.println (Lean.Json.mkObj [
    ("parse_ns", toJson parsing), ("resolve_ns", toJson resolution),
    ("constraints_ns", toJson constraints), ("bounds_ns", toJson boundsDecode),
    ("backend_ns", toJson backend), ("render_ns", toJson rendering),
    ("output_bytes", toJson rendered.text.utf8ByteSize),
    ("signatures", toJson (compiled.2.map fun d => Lean.Json.mkObj [
      ("id", toJson d.id), ("name", toJson (Text.Symbol.signature d.signature).name)])),
    ("declarations", toJson resolved.count), ("bodies", toJson prepared.bodies.length)]).compress

end ClaferCompiler.Tests.Qualification
