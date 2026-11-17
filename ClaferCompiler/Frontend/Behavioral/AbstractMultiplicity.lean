module

public import ClaferCompiler.Frontend.Behavioral.Declarations
public import ClaferCompiler.IR.Behavioral.Expression
public import ClaferCompiler.IR.Behavioral.Properties

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.AbstractMultiplicity
open IR.Behavioral IR.Structural

/-- Ordinary strict integer comparisons retain both endpoints. Cardinality
counts head identities, including references, without following their targets. -/
-- [impl->req~compiler-abstract-multiplicity~1]
def formula (heads : SetExpr k n) (bounds : Bounds) : Expression.Formula k n :=
  let count := Expression.Integer.cardinality (.set heads)
  .and (.not (.atom (.primitive (.less count (.literal bounds.lower)))))
    (match bounds.upper with
    | .unbounded => .truth
    | .finite hi => .not (.atom (.primitive (.less (.literal hi) count))))

def heads (m : Core k) (d : Fin k) : SetExpr k n :=
  if (m.get d).parent.isSome then .thisStep (.child d) else .extent d

def authored (m : Core k) (d : Fin k) : Bounds :=
  ((m.get d).authored.bind (·.localBounds)).getD {}

def constraint (m : Core k) (d : Fin k) :
    Properties.Constraint k (Expression.Atom k) (Expression.Collection k) :=
  ⟨(m.get d).parent.getD m.root, formula (heads m d) (authored m d),
    (m.get d).source.getD ⟨"", 0, 0⟩⟩

/-- Each original abstract declaration contributes exactly one aggregate.
The existing attachment compiler quantifies over every live owner at every time.
No subtype sum, inferred scope cap or synthetic abstract-parent edge is used. -/
-- [impl->req~compiler-abstract-multiplicity~1]
def generate (v : IR.BehavioralStructural.Validated k) :
    List (Properties.Constraint k (Expression.Atom k) (Expression.Collection k)) :=
  ((List.finRange k).filter fun i => v.core.authoredAbstract[i]).map (constraint v.core.structural)

def constraints {source : Document} (d : BoundDeclarations source) :
    List (Properties.Constraint d.resolved.count (Expression.Atom d.resolved.count)
      (Expression.Collection d.resolved.count)) :=
  if d.resolved.aggregate then generate d.resolved.admitted else []

end ClaferCompiler.Frontend.Behavioral.AbstractMultiplicity
