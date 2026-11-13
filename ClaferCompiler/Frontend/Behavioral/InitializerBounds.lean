module

public import ClaferCompiler.Frontend.Behavioral.InitializerClassification
public import ClaferCompiler.IR.Behavioral.Expression

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Initializers
open IR.Behavioral

def singleBound (r : IR.Structural.Bounds) : Bool := match r.upper with
  | .finite n => decide (n ≤ 1)
  | .unbounded => false

def scalarStep (c : IR.Structural.Core k) : Step k → Bool
  | .parent | .deref _ => true
  | .child d => singleBound (c.get d).localBounds

/-- Declaration bounds and functional parent/reference navigation are the only
leaf evidence. Constraint truth and backend scopes are never consulted. -/
def scalarSet (c : IR.Structural.Core k) : Nat → SetExpr k n → Bool :=
  Nat.rec (fun _ => false) fun _ next a => match a with
    | .empty | .this | .root => true
    | .var _ => false
    | .extent d => d == c.root ||
        ((c.get d).parent == some c.root && singleBound (c.get d).localBounds)
    | .union _ _ => false
    | .inter a b => next a || next b
    | .diff a _ => next a
    | .step s a => next a && scalarStep c s
    | .thisStep s => scalarStep c s

def integerLiteral : Expression.Collection k n → Option Int
  | .literal i | .integer (.literal i) => some i
  | _ => none

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Conservative scalar analysis extends the accepted primitive rules with
strict value conditionals and ordinary resolved navigation. Exhaustion cannot
admit an expression. Definedness is never inferred from a scalar bound. -/
def scalarAt (c : IR.Structural.Core k) : Nat → Expression.Collection k n → Bool :=
  Nat.rec (fun _ => false) fun fuel next a => match a with
    | .set a => scalarSet c (fuel + 1) a
    | .literal _ | .integer _ | .extreme _ _ => true
    | .union a b => match integerLiteral a, integerLiteral b with
      | some i, some j => i == j
      | _, _ => false
    | .inter a b => next a || next b
    | .diff a _ | .ofType _ a => next a
    | .step s a => next a && scalarStep c s
    | .ite _ a b => next a && next b

end ClaferCompiler.Frontend.Behavioral.Initializers
