module

public import ClaferCompiler.IR.Structural

@[expose] public section
namespace ClaferCompiler.Frontend

abbrev SourceSpan := IR.Structural.SourceSpan
abbrev Category := IR.Structural.Category

-- Requirement: compiler-diagnostics; trace artifacts are in docs/parser.md.
structure Diagnostic where
  version : Nat := 1
  code : String
  phase : String
  category : Category
  message : String
  primary : SourceSpan
  line : Nat
  column : Nat
  related : Array SourceSpan := #[]
  deriving Repr, BEq

structure Token where
  text : String
  span : SourceSpan
  line : Nat
  column : Nat
  layoutColumn : Nat
  deriving Repr, BEq

-- Requirement: compiler-parser; trace artifacts are in docs/parser.md.
/-- Authored spelling and location; no lookup, defaults or coercions. -/
abbrev Name := Token

inductive Expr where
  | name (token : Name)
  | integer (token : Token) (value : Nat)
  | unary (op : Token) (body : Expr) (span : SourceSpan)
  | binary (op : Token) (left right : Expr) (span : SourceSpan)
  | quantified (quantifier : Token) (binder : Name) (domain body : Expr) (span : SourceSpan)
  | parens (body : Expr) (span : SourceSpan)

def Expr.span : Expr → SourceSpan
  | .name t | .integer t _ => t.span
  | .unary _ _ s | .binary _ _ _ s | .quantified _ _ _ _ s | .parens _ s => s

/-- Tokens distinguish keywords, numeric intervals and omitted annotations. -/
structure Cardinality where
  tokens : Array Token
  lower : Nat
  upper : Option Nat
  deriving Repr, BEq

structure Header where
  name : Name
  abstractToken : Option Token := none
  useToken : Option Token := none
  group : Option Cardinality := none
  super : Option Name := none
  reference : Option (Token × Name) := none
  cardinality : Option Cardinality := none
  deriving Repr, BEq

inductive Element where
  | declaration (header : Header) (children : List Element) (span : SourceSpan)
  | constraint (bodies : List Expr) (span : SourceSpan)

def Element.span : Element → SourceSpan
  | .declaration _ _ s | .constraint _ s => s

structure Document where
  file : String
  source : String
  elements : List Element

end ClaferCompiler.Frontend
