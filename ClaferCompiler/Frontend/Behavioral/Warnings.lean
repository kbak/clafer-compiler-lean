module

public import ClaferCompiler.Frontend.Behavioral.ExpressionCore

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral

/-- Nonfatal source information is separate from the existing error protocol. -/
structure Warning where
  code : String
  message : String
  operator : String
  primary : SourceSpan
  line : Nat
  column : Nat
  deriving BEq, Repr

namespace Warnings

def optionalToken : Option Token → List String
  | none => ["none"]
  | some t => ["some", t.text]

/-- Prefix encoding of authored syntax, ignoring positions and parentheses.
Constructor arities, optional markers and binder counts delimit every field.
Standard list/string equality avoids a second recursive expression equality.
This is neither alpha equivalence nor a semantic simplifier. -/
def shapeAt : Nat → Expr → Option (List String) :=
  Nat.rec (fun _ => none) (fun _ next e =>
    let optional := fun a => match a with
      | none => some ["none"]
      | some e => (next e).map ("some" :: ·)
    match e with
    | .name t => some ["name", t.text]
    | .integer t i => some ["integer", t.text, toString i]
    | .parens a _ => next a
    | .unary op a _ => do return ["unary", op.text] ++ (← next a)
    | .binary op a b _ => do return ["binary", op.text] ++ (← next a) ++ (← next b)
    | .quantified op disjoint names a b _ => do
      return ["quantified", op.text] ++ optionalToken disjoint ++ [toString names.length] ++
        names.map (·.text) ++ (← next a) ++ (← next b)
    | .letSet op binder value body _ => do return ["let", op.text, binder.text, value.text] ++ (← next body)
    | .conditional op a b c _ => do return ["conditional", op.text] ++ (← next a) ++ (← next b) ++ (← next c)
    | .transition op a b c _ => do return ["transition", op.text] ++ (← next a) ++ (← optional b) ++ (← next c)
    | .pattern op a b scope c d _ => do
      return ["pattern", op.text] ++ (← next a) ++ (← optional b) ++ optionalToken scope ++
        (← optional c) ++ (← optional d))

def sameExpression (fuel : Nat) (a b : Expr) : Bool :=
  match shapeAt fuel a, shapeAt fuel b with
  | some a, some b => a == b
  | _, _ => false

def warningAt (doc : Document) (e : Expr) (code operator message : String) : Warning :=
  let d := Constraints.errorAt ⟨doc.file, doc.source, []⟩ e.span code message
  ⟨code, message, operator, d.primary, d.line, d.column⟩

-- [impl->req~compiler-diagnostics~1]
-- [impl->req~compiler-behavioral-elaboration~1]
/-- Call only after successful elaboration. A rewritten maximal chain emits one
warning; its discarded names cannot create additional expression warnings. -/
def expressionAt (doc : Document) : Nat → Expr → List Warning :=
  Nat.rec (fun _ => []) (fun fuel next e =>
    if (match Expressions.emptyNavigationAt (fuel + 1) e with
        | some (.isTrue _) => true | _ => false) then
      [warningAt doc e "behavioral.empty-navigation" "."
        "Navigation starting at literal noclafer is empty; tail names are not resolved."]
    else
      match e with
      | .name _ | .integer _ _ => []
      | .parens a _ | .unary _ a _ | .letSet _ _ _ a _ => next a
      | .binary op a b _ =>
          let own := if ["=", "!=", "--", "**"].contains op.text && sameExpression (fuel + 1) a b then
            [warningAt doc e "behavioral.redundant-expression" op.text
              "Both operands are the same expression; ordinary typing and definedness still apply."] else []
          own ++ next a ++ next b
      | .quantified _ _ _ a b _ => next a ++ next b
      | .conditional _ a b c _ => next a ++ next b ++ next c
      | .transition _ a b c _ => next a ++ b.toList.flatMap next ++ next c
      | .pattern _ a b _ c d _ => next a ++ (b.toList ++ c.toList ++ d.toList).flatMap next)

def expression (doc : Document) (e : Expr) : List Warning := expressionAt doc (64 + 8 * doc.source.utf8ByteSize) e

def elementAt (doc : Document) : Nat → Element → List Warning :=
  Nat.rec (fun _ => []) (fun _ next e => match e with
    | .property _ bodies _ => bodies.flatMap (expression doc)
    | .enumeration _ _ _ => []
    | .declaration h children _ =>
        h.initializer.toList.flatMap (fun (_, e) => expression doc e) ++
        h.transition.toList.flatMap (fun (_, guard, target) =>
          guard.toList.flatMap (expression doc) ++ expression doc target) ++
        children.flatMap next)

def element (doc : Document) (e : Element) : List Warning := elementAt doc (64 + 8 * doc.source.utf8ByteSize) e

/-- Sort by source start, retaining preorder for equal starts. Generated header
constraints and inherited expansions do not duplicate authored warnings. -/
def document (doc : Document) : List Warning :=
  (doc.elements.flatMap (element doc)).mergeSort (fun a b => a.primary.startByte ≤ b.primary.startByte)

end Warnings
end ClaferCompiler.Frontend.Behavioral
