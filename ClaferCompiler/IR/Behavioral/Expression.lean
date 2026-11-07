module

public import ClaferCompiler.IR.Behavioral.Binders

/-! Authored value expressions compose the accepted partial primitives with
current navigation and strict value conditionals. Conditions stay inside the
value that they select; later operations are not distributed across branches.
The resolved Primitive/Grouped interfaces retain their existing contracts.
-/

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Expression

mutual
  -- [impl->req~compiler-behavioral-elaboration~1]
  inductive Collection (k : Nat) : Nat → Type where
    | set (a : SetExpr k n) : Collection k n
    | literal (i : Int) : Collection k n
    | integer (a : Integer k n) : Collection k n
    | extreme (op : Primitive.Extreme) (a : Collection k n) : Collection k n
    | union (a b : Collection k n) : Collection k n
    | inter (a b : Collection k n) : Collection k n
    | diff (a b : Collection k n) : Collection k n
    | step (s : Step k) (a : Collection k n) : Collection k n
    /-- Filter by fixed identity type, including captured absent identities. -/
    | ofType (declaration : Fin k) (a : Collection k n) : Collection k n
    | ite (condition : FormulaF (Atom k) (Collection k) n)
        (yes no : Collection k n) : Collection k n
  inductive Integer (k : Nat) : Nat → Type where
    | literal (i : Int) : Integer k n
    | coerce (a : Collection k n) : Integer k n
    | extract (a : Collection k n) : Integer k n
    | cardinality (a : Collection k n) : Integer k n
    | binary (op : BehavioralArithmetic.Binary) (a b : Integer k n) : Integer k n
    | negate (a : Integer k n) : Integer k n
    | fold (op : BehavioralArithmetic.Fold) (domains : Collections k n)
        (body : Integer k (n + 1)) : Integer k n
    | ite (condition : FormulaF (Atom k) (Collection k) n)
        (yes no : Integer k n) : Integer k n
  inductive Collections (k : Nat) : Nat → Type where
    | nil : Collections k n
    | cons (head : Collection k n) (tail : Collections k n) : Collections k n
  inductive Predicate (k : Nat) : Nat → Type where
    | inhabited (a : Collection k n) : Predicate k n
    | equal (a b : Collection k n) : Predicate k n
    | subset (a b : Collection k n) : Predicate k n
    | integerEqual (a b : Integer k n) : Predicate k n
    | less (a b : Integer k n) : Predicate k n
  inductive Atom (k : Nat) : Nat → Type where
    | primitive (a : Predicate k n) : Atom k n
    | count (q : Grouped.Count) (arity : Nat) (disjoint : Bool) (domain : Collection k n)
        (body : FormulaF (Atom k) (Collection k) (n + arity)) : Atom k n
end

abbrev Formula (k : Nat) := FormulaF (Atom k) (Collection k)

-- [impl->req~compiler-behavioral-elaboration~1]
def binders (q : Quantifier) (arity : Nat) (disjoint : Bool)
    (domain : Collection k n) (body : Formula k (n + 1 + arity)) : Formula k n :=
  .letSet domain (match q with
    | .all => Binders.successiveWith (fun {_} => Collection.set) n .all disjoint arity 0
        (cast (congrArg (Formula k) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body)
    | .some => Binders.successiveWith (fun {_} => Collection.set) n .some disjoint arity 0
        (cast (congrArg (Formula k) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body)
    | .no => .not (Binders.successiveWith (fun {_} => Collection.set) n .some disjoint arity 0
        (cast (congrArg (Formula k) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body))
    | .one => .atom (.count .one arity disjoint (.set (.var 0)) body)
    | .lone => .atom (.count .lone arity disjoint (.set (.var 0)) body))

end ClaferCompiler.IR.Behavioral.Expression
