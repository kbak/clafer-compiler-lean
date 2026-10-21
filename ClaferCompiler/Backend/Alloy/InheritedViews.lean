module

public import ClaferCompiler.Backend.Alloy.Inherited

@[expose] public section
/-! [impl->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Backend.Alloy.Inherited

/-- Contexts restrict original tuples. They allocate no heads or links. -/
def viewContains (o : Structural.Observation n) (f q : Fin n) : List (Nat × Nat) :=
  (o.containment f).filter fun pair => (o.heads q).contains pair.1

def viewHeads (o : Structural.Observation n) (f q : Fin n) : List Nat :=
  (o.heads f).filter fun x => (viewContains o f q).any fun pair => pair.2 == x

def viewDeref (o : Structural.Observation n) (f q : Fin n) : List (Nat × Nat) :=
  (o.dereference f).filter fun pair => (viewHeads o f q).contains pair.1

end ClaferCompiler.Backend.Alloy.Inherited
