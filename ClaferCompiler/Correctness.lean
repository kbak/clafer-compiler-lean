module

public import ClaferCompiler.Correctness.InheritedViews

public import ClaferCompiler.Driver
public import ClaferCompiler.Correctness.StructuralCorrectness

public section

/-! Bootstrap equations, concrete representations and M1/inherited preservation.
Static expression preservation retains its separate proof obligations. -/

namespace ClaferCompiler.Correctness

theorem version_response :
    Driver.response ["--version"] = some Driver.version := by rfl

theorem empty_response : Driver.response [] = none := by rfl

end ClaferCompiler.Correctness
