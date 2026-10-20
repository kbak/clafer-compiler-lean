module

public import ClaferCompiler

public section

namespace ClaferCompiler.Tests

theorem compile_command_unavailable : Driver.response ["compile-ir"] = none := by decide
theorem version_extra_unavailable : Driver.response ["--version", "extra"] = none := by decide

end ClaferCompiler.Tests

#check ClaferCompiler.Correctness.version_response
#check ClaferCompiler.Correctness.empty_response
