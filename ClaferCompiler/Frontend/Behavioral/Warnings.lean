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

def token (t : Token) : Token := ⟨t.text, ⟨"", 0, 0⟩, 0, 0, 0⟩

/-- Syntactic identity in the same lexical/cursor context. Retain every name,
binder and operator; only source positions and parentheses are irrelevant.
This is neither alpha equivalence nor a semantic simplifier. -/
def shape : Expr → Expr
  | .name t => .name (token t)
  | .integer t i => .integer (token t) i
  | .parens a _ => shape a
  | .unary op a _ => .unary (token op) (shape a) ⟨"", 0, 0⟩
  | .binary op a b _ => .binary (token op) (shape a) (shape b) ⟨"", 0, 0⟩
  | .quantified op disjoint names a b _ =>
      .quantified (token op) (disjoint.map token) (names.map token) (shape a) (shape b) ⟨"", 0, 0⟩
  | .letSet op binder value body _ => .letSet (token op) (token binder) (token value) (shape body) ⟨"", 0, 0⟩
  | .conditional op a b c _ => .conditional (token op) (shape a) (shape b) (shape c) ⟨"", 0, 0⟩
  | .transition op a b c _ => .transition (token op) (shape a)
      (match b with | none => none | some e => some (shape e)) (shape c) ⟨"", 0, 0⟩
  | .pattern op a b scope c d _ =>
      .pattern (token op) (shape a) (match b with | none => none | some e => some (shape e))
        (scope.map token) (match c with | none => none | some e => some (shape e))
        (match d with | none => none | some e => some (shape e)) ⟨"", 0, 0⟩

def warningAt (doc : Document) (e : Expr) (code operator message : String) : Warning :=
  let d := Constraints.errorAt ⟨doc.file, doc.source, []⟩ e.span code message
  ⟨code, message, operator, d.primary, d.line, d.column⟩

-- [impl->req~compiler-diagnostics~1]
-- [impl->req~compiler-behavioral-elaboration~1]
/-- Call only after successful elaboration. A rewritten maximal chain emits one
warning; its discarded names cannot create additional expression warnings. -/
def expression (doc : Document) (e : Expr) : List Warning :=
  if (Expressions.emptyNavigation e).isSome then
    [warningAt doc e "behavioral.empty-navigation" "."
      "Navigation starting at literal noclafer is empty; tail names are not resolved."]
  else
    match e with
    | .name _ | .integer _ _ => []
    | .parens a _ | .unary _ a _ | .letSet _ _ _ a _ => expression doc a
    | .binary op a b _ =>
        let own := if ["=", "!=", "--", "**"].contains op.text && shape a == shape b then
          [warningAt doc e "behavioral.redundant-expression" op.text
            "Both operands are the same expression; ordinary typing and definedness still apply."] else []
        own ++ expression doc a ++ expression doc b
    | .quantified _ _ _ a b _ => expression doc a ++ expression doc b
    | .conditional _ a b c _ => expression doc a ++ expression doc b ++ expression doc c
    | .transition _ a b c _ => expression doc a ++
        (match b with | none => [] | some e => expression doc e) ++ expression doc c
    | .pattern _ a b _ c d _ => expression doc a ++
        (match b with | none => [] | some e => expression doc e) ++
        (match c with | none => [] | some e => expression doc e) ++
        (match d with | none => [] | some e => expression doc e)
termination_by structural e

def element (doc : Document) : Element → List Warning
  | .property _ bodies _ => bodies.flatMap (expression doc)
  | .enumeration _ _ _ => []
  | .declaration h children _ =>
      h.initializer.toList.flatMap (fun (_, e) => expression doc e) ++
      h.transition.toList.flatMap (fun (_, guard, target) =>
        guard.toList.flatMap (expression doc) ++ expression doc target) ++
      children.flatMap (element doc)

/-- Sort by source start, retaining preorder for equal starts. Generated header
constraints and inherited expansions do not duplicate authored warnings. -/
def document (doc : Document) : List Warning :=
  (doc.elements.flatMap (element doc)).mergeSort (fun a b => a.primary.startByte ≤ b.primary.startByte)

end Warnings
end ClaferCompiler.Frontend.Behavioral
