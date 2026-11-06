module

public import ClaferCompiler

/-!
[utest->req~compiler-boundaries~1]
[utest->req~compiler-build~1]
-/

public section

namespace ClaferCompiler.Tests

theorem incomplete_compile_has_no_informational_response : Driver.response ["compile-ir"] = none := by decide
theorem version_extra_unavailable : Driver.response ["--version", "extra"] = none := by decide

end ClaferCompiler.Tests

#check ClaferCompiler.Correctness.version_response
#check ClaferCompiler.Correctness.empty_response
