module

public import ClaferCompiler.IR.Behavioral.Modifiers

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Properties

structure Constraint (k : Nat) (A D : Nat → Type) where
  owner : Fin k
  body : FormulaF A D 0
  source : Structural.SourceSpan

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Assertions are queries over the model and never enter its constraint list.
Bodies retain their original strict domain, before truth normalization. -/
structure Model (k : Nat) (A D : Nat → Type) where
  structural : BehavioralStructural.Validated k
  modifiers : Vector (List Surface.Modifiers.Modifier) k
  constraints : List (Constraint k A D)
  assertions : List (Constraint k A D)

inductive Command (k : Nat) (A D : Nat → Type) (assertionCount : Nat) where
  | check (assertion : Fin assertionCount)
  | run (scenario : List (Constraint k A D))

structure Request (k : Nat) (A D : Nat → Type) where
  model : Model k A D
  command : Command k A D model.assertions.length

-- [impl->req~compiler-behavioral-elaboration~1]
def Model.withScenario (model : Model k A D) (additional : List (Constraint k A D)) : Model k A D :=
  { model with constraints := model.constraints ++ additional }

end ClaferCompiler.IR.Behavioral.Properties
