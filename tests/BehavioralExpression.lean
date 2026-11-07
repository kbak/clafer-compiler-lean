module

public import ClaferCompiler.SemanticsBridge.Behavioral.Expression
public import ClaferCompiler.Frontend.Behavioral.ExpressionRules

@[expose] public noncomputable section
namespace ClaferCompiler.Tests.BehavioralExpression
open IR.Behavioral
open SemanticsBridge.Behavioral.Expression
open Clafer.Behavioral (Environment Trace)

variable (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
  (R : Clafer.Constraints.IntegerRealization U) (ρ : Environment U n) (t : Nat)

-- [utest->req~compiler-behavioral-elaboration~1]
/-- The unselected zero is defined, and does not become an extra divisor. -/
theorem selected_denominator :
    integer m τ R (.binary .divide (.literal 1) (.ite .truth (.literal 1) (.literal 0))) ρ t = some 1 := by
  change Clafer.Behavioral.Arithmetic.Binary.divide.eval (some 1)
    (IR.BehavioralArithmetic.conditional (condition τ .truth ρ t) (some 1) (some 0)) = some 1
  rw [condition_truth]
  rfl

-- [utest->req~compiler-behavioral-elaboration~1]
theorem undefined_unselected_branch :
    integer m τ R (.ite .truth (.literal 1) (.binary .divide (.literal 1) (.literal 0))) ρ t = none := by
  classical
  simp [integer, choose, condition, IR.BehavioralArithmetic.conditional,
    Clafer.Behavioral.Formula.Defined, Clafer.Behavioral.Formula.raw,
    SemanticsBridge.BehavioralArithmetic.binary, Clafer.Behavioral.Arithmetic.Binary.eval,
    Clafer.Behavioral.Arithmetic.Binary.apply]

-- [utest->req~compiler-behavioral-elaboration~1]
theorem partial_navigation (s : Step k) :
    collection m τ R (.step s (.integer (.binary .divide (.literal 1) (.literal 0)))) ρ t = none := by
  simp [collection, SemanticsBridge.BehavioralArithmetic.binary,
    Clafer.Behavioral.Arithmetic.Binary.eval, Clafer.Behavioral.Arithmetic.Binary.apply]

open Frontend Frontend.Behavioral Frontend.Behavioral.Values in
-- [utest->req~compiler-behavioral-elaboration~1]
/-- Tail-name existence and uniqueness are deliberately absent from the rule. -/
theorem literal_empty_navigation (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (Γ : Context k n) (root op tail : Token) (span : SourceSpan)
    (hr : root.text = "noclafer") (hd : op.text = ".")
    (ht : Resolution.integerName tail.text = false) :
    Expressions.Elaborates v owner Γ none (.binary op (.name root) (.name tail) span)
      (.collection .empty (.set .empty)) :=
  .emptyNavigation (.dot hd (.literal hr) (.name ht)) .empty

open Frontend Frontend.Behavioral Frontend.Behavioral.Values in
-- [utest->req~compiler-behavioral-elaboration~1]
theorem relative_empty_navigation (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (Γ : Context k n) (root op tail : Token) (span : SourceSpan) (type : Values.Ty k)
    (a : Expression.Collection k n) (hr : root.text = "noclafer") (hd : op.text = ".")
    (ht : Resolution.integerName tail.text = false) :
    Expressions.Elaborates v owner Γ (some (.collection type a))
      (.binary op (.name root) (.name tail) span) (.collection .empty (.inter a (.set .empty))) :=
  .emptyNavigation (.dot hd (.literal hr) (.name ht)) .emptyRelative

end ClaferCompiler.Tests.BehavioralExpression
