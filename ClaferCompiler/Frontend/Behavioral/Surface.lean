module

public import ClaferCompiler.Frontend.Surface

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral

-- [impl->req~compiler-behavioral-frontend~1]
/-- Authored tokens retain aliases, repeated modifiers, polarity and byte spans.
No resolution, normalization or implicit temporal attachment occurs in parsing. -/
inductive Expr where
  | name (token : Name)
  | integer (token : Token) (value : Nat)
  | unary (op : Token) (body : Expr) (span : SourceSpan)
  | binary (op : Token) (left right : Expr) (span : SourceSpan)
  | quantified (quantifier : Token) (disjoint : Option Token) (binders : List Name)
      (domain body : Expr) (span : SourceSpan)
  | letSet (token : Token) (binder value : Name) (body : Expr) (span : SourceSpan)
  | conditional (token : Token) (condition yes no : Expr) (span : SourceSpan)
  | transition (arrow : Token) (source : Expr) (guard : Option Expr) (target : Expr)
      (span : SourceSpan)
  | pattern (kind : Token) (first : Expr) (second : Option Expr)
      (scope : Option Token) (opener closer : Option Expr) (span : SourceSpan)
  | parens (body : Expr) (span : SourceSpan)
  deriving BEq

def Expr.span : Expr → SourceSpan
  | .name t | .integer t _ => t.span
  | .unary _ _ s | .binary _ _ _ s | .quantified _ _ _ _ _ s
  | .letSet _ _ _ _ s | .conditional _ _ _ _ s | .transition _ _ _ _ s
  | .pattern _ _ _ _ _ _ s | .parens _ s => s

inductive PropertyKind where
  | constraint | assertion
  deriving BEq, DecidableEq, Repr

structure Header where
  structural : Frontend.Header
  modifiers : List Token := []
  initializer : Option (Token × Expr) := none
  transition : Option (Token × Option Expr × Expr) := none

inductive Element where
  | declaration (header : Header) (children : List Element) (span : SourceSpan)
  | property (kind : PropertyKind) (bodies : List Expr) (span : SourceSpan)
  | enumeration (name : Name) (literals : List Name) (span : SourceSpan)

def Element.span : Element → SourceSpan
  | .declaration _ _ s | .property _ _ s | .enumeration _ _ s => s

structure Document where
  file : String
  source : String
  elements : List Element

/-- A scenario is selected by the caller; source spelling is shared with models.
Assertions are never turned into constraints or source-negated counterexamples. -/
inductive RequestKind where
  | model | scenario
  deriving BEq, DecidableEq, Repr

end ClaferCompiler.Frontend.Behavioral
