module

public import ClaferCompiler.IR.Behavioral.Primitive

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Grouped

inductive Count where
  | one | lone
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Counting is a raw-body barrier over complete ordered assignments. Its body
is retained inside the atom, so signed normalization cannot turn grouped
uniqueness into nested uniqueness or distribute temporal negation into it. -/
inductive Atom (k : Nat) : Nat → Type where
  | primitive (a : Primitive.Atom k n) : Atom k n
  | count (q : Count) (arity : Nat) (disjoint : Bool) (domain : Primitive.Collection k n)
      (body : FormulaF (Atom k) (Primitive.Collection k) (n + arity)) : Atom k n

abbrev Formula (k : Nat) := FormulaF (Atom k) (Primitive.Collection k)

end ClaferCompiler.IR.Behavioral.Grouped
