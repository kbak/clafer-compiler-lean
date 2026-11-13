module

public import ClaferCompiler.Frontend.Behavioral.Declarations

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral

inductive HeaderPropertyKind where
  | initializer | transition
  deriving DecidableEq, BEq, Repr

/-- Generated properties retain their header origin separately from the
declaration at which they are evaluated. The authored header is not overwritten. -/
structure HeaderProperty (k : Nat) where
  declaration : Fin k
  owner : Fin k
  kind : HeaderPropertyKind
  expression : Expr
  span : SourceSpan

def initializerExpression (token : Token) (_heads left value : Expr) : Except Diagnostic Expr :=
  if token.text = "=" ∨ token.text = ":=" then
    .ok (.binary token left value ⟨left.span.file, left.span.startByte, value.span.endByte⟩)
  else .error (Resolution.errorAt token "behavioral.initializer-token" "Invalid initializer token.")

/-- Independent attachment rules: a constant equation belongs to the enclosing
scope; an outgoing transition belongs to the declaration itself. -/
def HeaderAttachment (c : IR.Structural.Core k) (declaration owner : Fin k) : HeaderPropertyKind → Prop
  | .initializer => owner = (c.get declaration).parent.getD c.root
  | .transition => owner = declaration

structure BoundHeaderProperty (c : IR.Structural.Core k) extends HeaderProperty k where
  attachment : HeaderAttachment c declaration owner kind

-- [impl->req~compiler-behavioral-elaboration~1]
def headerProperties {source : Document} (b : BoundDeclarations source) :
    Except Diagnostic (List (BoundHeaderProperty b.resolved.candidate.core)) := do
  let lists ← (List.finRange b.resolved.count).mapM fun declaration => do
    match b.resolved.candidate.paths[declaration].bind (headerAt b.expanded) with
    | none => return []
    | some header =>
      let name := header.structural.name
      let init ← match header.initializer with
        | none => pure []
        | some (token, value) => do
          let expression ← initializerExpression token (.name name) (.name name) value
          let owner := (b.resolved.candidate.core.get declaration).parent.getD b.resolved.candidate.core.root
          pure [(⟨⟨declaration, owner, .initializer, expression, expression.span⟩, rfl⟩ :
            BoundHeaderProperty b.resolved.candidate.core)]
      let transitions ← match header.transition with
        | none => pure []
        | some (arrow, guard, target) => do
          unless arrow.text == "-->" || arrow.text == "-->>" do
            throw (Resolution.errorAt arrow "behavioral.arrow" "Invalid transition arrow.")
          let span := { name.span with endByte := target.span.endByte }
          let expression := Expr.transition arrow (.name { name with text := "this" }) guard target span
          pure [(⟨⟨declaration, declaration, .transition, expression, span⟩, rfl⟩ :
            BoundHeaderProperty b.resolved.candidate.core)]
      return init ++ transitions
  return lists.flatten

end ClaferCompiler.Frontend.Behavioral
