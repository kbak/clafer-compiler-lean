module

public import ClaferCompiler.Driver

public section

/-! Build witness only. Compiler correctness remains with #11/#15/#20. -/

namespace ClaferCompiler.Correctness

theorem version_response :
    Driver.response ["--version"] = some Driver.version := by rfl

theorem empty_response : Driver.response [] = none := by rfl

end ClaferCompiler.Correctness
