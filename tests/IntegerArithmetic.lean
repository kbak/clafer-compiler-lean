module

public import ClaferCompiler.Correctness.IntegerArithmetic

public section
namespace ClaferCompiler.Tests.IntegerArithmetic
open Backend.Alloy

/-! [utest->req~compiler-target-arithmetic~1] -/

example : (Integer.subtract (.literal 2) (.literal 5)).eval 4 ⟨[], []⟩ [] = some (-3) := by decide
example : (Integer.add (.literal 7) (.literal 1)).eval 4 ⟨[], []⟩ [] = none := by decide
example : (Integer.subtract (.add (.literal 7) (.literal 1)) (.literal 1)).eval 4 ⟨[], []⟩ [] = none := by decide
example : (Integer.subtract (.literal (-8)) (.literal 1)).eval 4 ⟨[], []⟩ [] = none := by decide
example : (Integer.subtract (.literal 0) (.literal (-8))).eval 4 ⟨[], []⟩ [] = none := by decide
example : (Integer.add (.literal 0) (.literal (-1))).eval 1 ⟨[], []⟩ [] = some (-1) := by decide

/-- A false antecedent cannot hide an undefined integer intermediate in target
evaluation. Admission checks this branch independently as well. -/
example : (Formula.implies .falsity
    (.compare .eq (.add (.literal 7) (.literal 1)) (.literal 0))).eval 4 ⟨[], []⟩ [] = none := by decide

/-- A quantified body need not be evaluated over an empty actual domain. -/
example : (Formula.all (.empty .unary)
    (.compare .eq (.add (.literal 7) (.literal 1)) (.literal 0))).eval 4 ⟨[], []⟩ [] = some true := by decide

end ClaferCompiler.Tests.IntegerArithmetic
