module

public import ClaferCompiler.IR.Behavioral.Syntax
public import ClaferCompiler.IR.BehavioralArithmetic

/-! Resolved syntax corresponding to the accepted upstream PrimitiveExpression
constructors at 6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4 (MIT, Kacper Bak).
The syntax makes partial operations explicit; it does not assume definedness.
-/

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Primitive

inductive Extreme where
  | minimum | maximum
  deriving DecidableEq, Repr

mutual
  -- [impl->req~compiler-behavioral-elaboration~1]
  inductive Collection (k : Nat) : Nat → Type where
    | set (a : SetExpr k n) : Collection k n
    | literal (i : Int) : Collection k n
    | integer (a : Integer k n) : Collection k n
    | extreme (op : Extreme) (a : Collection k n) : Collection k n
    | union (a b : Collection k n) : Collection k n
    | inter (a b : Collection k n) : Collection k n
    | diff (a b : Collection k n) : Collection k n
  inductive Integer (k : Nat) : Nat → Type where
    | literal (i : Int) : Integer k n
    | coerce (a : Collection k n) : Integer k n
    | extract (a : Collection k n) : Integer k n
    | cardinality (a : Collection k n) : Integer k n
    | binary (op : BehavioralArithmetic.Binary) (a b : Integer k n) : Integer k n
    | negate (a : Integer k n) : Integer k n
    | fold (op : BehavioralArithmetic.Fold) (domains : Collections k n)
        (body : Integer k (n + 1)) : Integer k n
  inductive Collections (k : Nat) : Nat → Type where
    | nil : Collections k n
    | cons (head : Collection k n) (tail : Collections k n) : Collections k n
end

inductive Atom (k n : Nat) where
  | inhabited (a : Collection k n)
  | equal (a b : Collection k n)
  | subset (a b : Collection k n)
  | integerEqual (a b : Integer k n)
  | less (a b : Integer k n)

abbrev Formula (k : Nat) := FormulaF (Atom k) (Collection k)

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Ordinary enclosing-context equation, with no birth/initially wrapper.
Strict definedness still inspects the equation when the heads are absent. -/
def constantInitializer (heads left value : Collection k n) : Formula k n :=
  .implies (.atom (.inhabited heads)) (.atom (.equal left value))

/-- Keeping the original formula is mandatory: signed normalization does not
preserve the original strict definedness obligations by itself. -/
structure Normalized (k n : Nat) where
  original : Formula k n
  positive : Bool
  truth : Formula k n
  fuel : Nat
  enough : sizeOf original < fuel
  correspondence : truth = FormulaF.normalize original positive fuel enough

-- [impl->req~compiler-behavioral-elaboration~1]
def normalize (a : Formula k n) (positive : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) : Normalized k n :=
  ⟨a, positive, FormulaF.normalize a positive fuel enough, fuel, enough, rfl⟩

end ClaferCompiler.IR.Behavioral.Primitive
