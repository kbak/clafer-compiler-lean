module

public import ClaferCompiler.Driver

public section

/-! IO boundary: Lean's native code generator, C toolchain, runtime and OS are
trusted for execution. Driver integration is tested, not a new semantic proof. -/

-- [impl->req~compiler-build~1]
-- [impl->req~compiler-cli~1]
def main (args : List String) : IO UInt32 := ClaferCompiler.Driver.run args
