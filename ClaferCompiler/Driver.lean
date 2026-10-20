module

@[expose] public section
/-! Pure bootstrap response. Compilation commands belong to #19/#20. -/

namespace ClaferCompiler.Driver

def version : String := "clafer-compiler 0.1.0 (build bootstrap)"

def response (args : List String) : Option String :=
  if args == ["--version"] then some version else none

end ClaferCompiler.Driver
