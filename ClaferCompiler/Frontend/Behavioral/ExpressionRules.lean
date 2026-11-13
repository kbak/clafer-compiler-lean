module

public import ClaferCompiler.Frontend.Behavioral.Operations

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Expressions
open IR.Behavioral Values ValueRules

mutual
/-- Independent rules for the complete authored expression tree. Source spans,
lexical contexts, domain captures and navigation cursors are explicit indices.
No rule has a successful compiler invocation as a premise. -/
-- [impl->req~compiler-behavioral-elaboration~1]
inductive Elaborates (v : IR.BehavioralStructural.Validated k) (owner : Fin k) :
    {n : Nat} → Context k n → Option (Value k n) → Expr → Value k n → Prop where
  | name (lookup : Names.Name v owner Γ cursor token.text a) : Elaborates v owner Γ cursor (.name token) a
  | emptyNavigation (path : EmptyNavigation e)
      (literal : Names.Name v owner Γ cursor "noclafer" a) : Elaborates v owner Γ cursor e a
  | integer : Elaborates v owner Γ cursor (.integer token i) (.integer (.literal (Int.ofNat i)))
  | parens (body : Elaborates v owner Γ cursor e a) : Elaborates v owner Γ cursor (.parens e span) a
  | unary (body : Elaborates v owner Γ cursor e a) (operation : Unary v op.text a b) :
      Elaborates v owner Γ cursor (.unary op e span) b
  | aggregate (spelling : op.text = "sum" ∨ op.text = "product") (split : Operands e operands)
      (inputs : ElaboratesList v owner Γ cursor operands values)
      (operation : Aggregate v (if op.text == "sum" then .sum else .product) values a) :
      Elaborates v owner Γ cursor (.unary op e span) a
  | binary (left : Elaborates v owner Γ cursor e a) (right : Elaborates v owner Γ cursor f b)
      (operation : Binary v op.text a b c) : Elaborates v owner Γ cursor (.binary op e f span) c
  | dot (spelling : op.text = ".") (ordinary : ¬ EmptyNavigation (.binary op e f span))
      (left : Elaborates v owner Γ cursor e a)
      (right : Elaborates v owner Γ (some a) f b) : Elaborates v owner Γ cursor (.binary op e f span) b
  | quantified (legal : Binders.Legal names) (spelling : Binders.QuantifierSpelling op.text q)
      (domain : Elaborates v owner Γ cursor e a) (heads : Heads a type d)
      (body : Elaborates v owner (Binders.context Γ names type) none f b) (boolean : Boolean b p) :
      Elaborates v owner Γ cursor (.quantified op disjoint names e f span)
        (.formula (Expression.binders q names.length disjoint.isSome d p))
  | letSet (legal : Resolution.reserved binder.text = false)
      (domain : Elaborates v owner Γ cursor value a) (heads : Heads a type d)
      (body : Elaborates v owner (push Γ binder type) none e b) (boolean : Boolean b p) :
      Elaborates v owner Γ cursor (.letSet token binder value e span) (.formula (.letSet d p))
  | conditional (guard : Elaborates v owner Γ cursor e a) (boolean : Boolean a p)
      (yes : Elaborates v owner Γ cursor f b) (no : Elaborates v owner Γ cursor g c)
      (operation : Conditional v p b c d) : Elaborates v owner Γ cursor (.conditional token e f g span) d
  | transition (source : Elaborates v owner Γ cursor e a)
      (guard : ElaboratesOption v owner Γ cursor f b) (target : Elaborates v owner Γ cursor g c)
      (operation : Chain arrow.text a b c d) : Elaborates v owner Γ cursor (.transition arrow e f g span) d
  | pattern (first : Elaborates v owner Γ cursor e a)
      (second : ElaboratesOption v owner Γ cursor f b)
      (opener : ElaboratesOption v owner Γ cursor g c)
      (closer : ElaboratesOption v owner Γ cursor h d)
      (operation : Pattern kind.text (scope.map (·.text)) a b c d value) :
      Elaborates v owner Γ cursor (.pattern kind e f scope g h span) value

inductive ElaboratesList (v : IR.BehavioralStructural.Validated k) (owner : Fin k) :
    {n : Nat} → Context k n → Option (Value k n) → List Expr → List (Value k n) → Prop where
  | nil : ElaboratesList v owner Γ cursor [] []
  | cons (head : Elaborates v owner Γ cursor e a) (tail : ElaboratesList v owner Γ cursor es as) :
      ElaboratesList v owner Γ cursor (e :: es) (a :: as)
inductive ElaboratesOption (v : IR.BehavioralStructural.Validated k) (owner : Fin k) :
    {n : Nat} → Context k n → Option (Value k n) → Option Expr → Option (Value k n) → Prop where
  | none : ElaboratesOption v owner Γ cursor none none
  | some (body : Elaborates v owner Γ cursor e a) : ElaboratesOption v owner Γ cursor (some e) (some a)
end

theorem elaboratesList (h : Traversal.Related (Elaborates v owner Γ cursor) es values) :
    ElaboratesList v owner Γ cursor es values := by
  induction es generalizing values with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons _ _ => simp [Traversal.Related] at h
  | cons e es ih =>
    cases values with
    | nil => simp [Traversal.Related] at h
    | cons value values =>
      have parts := Traversal.Related.of_cons h
      exact .cons parts.1 (ih parts.2)

theorem elaboratesOption (h : Option.Rel (Elaborates v owner Γ cursor) e value) :
    ElaboratesOption v owner Γ cursor e value := by
  cases h with
  | none => exact .none
  | some body => exact .some body

def FormulaElaborates (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (e : Expr)
    (f : Expression.Formula k 0) : Prop :=
  ∃ a, Elaborates v owner #v[] none e a ∧ Boolean a f

end ClaferCompiler.Frontend.Behavioral.Expressions
