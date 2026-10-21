module

public import tests.AlloyCore
public meta import tests.AlloyCore

public section

namespace ClaferCompiler.Tests.AlloyOracle

/-- The external bridge compares these actual Lean evaluations with hand-written
Alloy witnesses. Interpreter evaluation is tested, not a proof of the Analyzer. -/
def printObservations : IO Unit := do
  for (name, value) in ClaferCompiler.Tests.AlloyCore.observations do
    match value with
    | none => throw (IO.userError s!"Target observation failed: {name}")
    | some b => IO.println s!"{name} {b}"

#eval printObservations

end ClaferCompiler.Tests.AlloyOracle
