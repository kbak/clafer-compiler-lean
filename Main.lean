module

public import ClaferCompiler.Driver

public section

/-! IO boundary: Lean's native code generator, C toolchain, runtime and OS are
trusted for execution. Kernel proofs concern the pure response, not IO. -/

def main (args : List String) : IO UInt32 := do
  match ClaferCompiler.Driver.response args with
  | some output =>
    IO.println output
    return 0
  | none =>
    (← IO.getStderr).putStrLn "usage: clafer-compiler --version; compilation is not implemented"
    return 2
