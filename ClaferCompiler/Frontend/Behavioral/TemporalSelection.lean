module

public import ClaferCompiler.Frontend.Behavioral.Surface

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral

/-- Inspect authored syntax before enum/header expansion. An initializer token
alone never selects temporal interpretation. -/
def temporalExpression : Nat → Expr → Bool :=
  Nat.rec (fun _ => true) fun _ next e => match e with
    | .name _ | .integer _ _ => false
    | .unary op a _ =>
        ["X", "next", "F", "eventually", "G", "globally", "initially", "finally"].contains op.text || next a
    | .binary op a b _ => ["U", "until", "W", "weakuntil"].contains op.text || next a || next b
    | .quantified _ _ _ a b _ => next a || next b
    | .letSet _ _ _ a _ | .parens a _ => next a
    | .conditional _ c a b _ => next c || next a || next b
    | .transition .. | .pattern .. => true

def temporalElements (fuel : Nat) : Nat → List Element → Bool :=
  Nat.rec (fun _ => true) fun _ next es => es.any fun e => match e with
    | .enumeration .. => false
    | .property _ bodies _ => bodies.any (temporalExpression fuel)
    | .declaration h children _ => !h.modifiers.isEmpty || h.transition.isSome ||
        h.initializer.any (fun (_, rhs) => temporalExpression fuel rhs) || next children

-- [impl->req~compiler-behavioral-profile~1]
def Document.temporal (source : Document) : Bool :=
  let fuel := source.source.utf8ByteSize + 1
  temporalElements fuel fuel source.elements

end ClaferCompiler.Frontend.Behavioral
