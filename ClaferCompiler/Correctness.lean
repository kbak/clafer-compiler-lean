module

public import ClaferCompiler.Correctness.InheritedViews

public import ClaferCompiler.Driver
public import ClaferCompiler.Correctness.StructuralCorrectness
public import ClaferCompiler.Correctness.IntegerArithmetic
public import ClaferCompiler.Correctness.ExprIntermediateRanges
public import ClaferCompiler.Correctness.ExpressionScalarFacts

public section

/-! Bootstrap equations, concrete representations and M1/inherited preservation.
Static expression/attachment preservation uses concrete leaf representations and
checked finite observations; source pipeline composition belongs to #20. -/

namespace ClaferCompiler.Correctness

theorem version_response :
    Driver.response ["--version"] = some Driver.version := by rfl

theorem empty_response : Driver.response [] = none := by rfl

end ClaferCompiler.Correctness
