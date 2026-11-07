module

public import ClaferCompiler.Backend.Alloy.Temporal.Syntax
public import ClaferCompiler.IR.BehavioralArithmetic

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Arithmetic

-- [impl->req~compiler-alloy-temporal-target~1]
/-- Scalar operator selection only. Collections, partial observations and their
strict domains remain obligations of expression compilation. -/
def binary : IR.BehavioralArithmetic.Binary → Temporal.Integer → Temporal.Integer → Temporal.Integer
  | .add => .add | .subtract => .subtract | .multiply => .multiply
  | .divide => .divide | .remainder => .remainder

end ClaferCompiler.Backend.Alloy.Behavioral.Arithmetic
