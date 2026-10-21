module

public import ClaferCompiler.Driver
public import ClaferCompiler.Correctness.StructuralDecoding

public section

/-! Bootstrap equations and the structural representation proof layer.
Global preservation remains unfinished under #11; M2 proofs belong to #15/#20. -/

namespace ClaferCompiler.Correctness

theorem version_response :
    Driver.response ["--version"] = some Driver.version := by rfl

theorem empty_response : Driver.response [] = none := by rfl

end ClaferCompiler.Correctness
