module

public import ClaferCompiler.IR.Behavioral.Grouped

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Binders

/-- The hidden domain capture follows the previously introduced locals.
Disjointness excludes those identities before evaluating the next body. -/
def choices (k n bound : Nat) (disjoint : Bool) : SetExpr k (n + 1 + bound) :=
  let domain : SetExpr k (n + 1 + bound) := .var ⟨bound, by omega⟩
  if disjoint then
    (List.finRange bound).foldl
      (fun domain i => .diff domain (.var ⟨i.val, by omega⟩)) domain
  else domain

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Nested all/some over a shared capture, with pairwise-distinct choices when
requested. `bound` counts locals already introduced, not outer lexical slots. -/
def successiveWith (set : ∀ {n}, SetExpr k n → D n) (n : Nat)
    (q : Quantifier) (disjoint : Bool) :
    (remaining : Nat) → (bound : Nat) → FormulaF A D (n + 1 + (bound + remaining)) →
      FormulaF A D (n + 1 + bound) :=
  Nat.rec (fun _ body => body) (fun remaining next bound body =>
    .quant q (set (choices k n bound disjoint))
      (next (bound + 1) (cast (congrArg (FormulaF A D)
        (by omega : n + 1 + (bound + (remaining + 1)) = n + 1 + ((bound + 1) + remaining))) body)))

def successive (k n : Nat) :=
  successiveWith (k := k) (A := Grouped.Atom k) (fun {_} => Primitive.Collection.set) n

/-- Every grouped quantifier captures its domain once, before authored binders
are in scope. The caller synthesizes its body with the hidden slot plus locals.
Counting preserves the original body inside a single ordered-assignment atom. -/
def elaborate (q : Quantifier) (arity : Nat) (disjoint : Bool)
    (domain : Primitive.Collection k n) (body : Grouped.Formula k (n + 1 + arity)) :
    Grouped.Formula k n :=
  .letSet domain (match q with
    | .all => successive k n .all disjoint arity 0 (by simpa using body)
    | .some => successive k n .some disjoint arity 0 (by simpa using body)
    | .no => .not (successive k n .some disjoint arity 0 (by simpa using body))
    | .one => .atom (.count .one arity disjoint (.set (.var 0)) body)
    | .lone => .atom (.count .lone arity disjoint (.set (.var 0)) body))

end ClaferCompiler.IR.Behavioral.Binders
