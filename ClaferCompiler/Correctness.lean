module

public import ClaferCompiler.Driver
public import ClaferCompiler.Correctness.StructuralCorrectness

public section

/-! Bootstrap equations, concrete representations and M1 preservation.
Inherited and expression extensions retain their separate proof obligations. -/

namespace ClaferCompiler.Correctness

theorem version_response :
    Driver.response ["--version"] = some Driver.version := by rfl

theorem empty_response : Driver.response [] = none := by rfl

end ClaferCompiler.Correctness
