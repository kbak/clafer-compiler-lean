module

public import ClaferCompiler.Frontend.BehavioralResolution

@[expose] public section
namespace ClaferCompiler.Frontend.BehavioralDeclarations

/-- Enum literals retain authored token identities and spans. The behavioral
frontend carries `finalLiterals` through resolution to modifier attachments. -/
structure EnumExpansion where
  elements : List Element
  finalLiterals : List Name

-- [impl->req~compiler-behavioral-structural-bridge~1]
def expandEnum (selectedProfile : String) (name : Name) (literals : List Name)
    (span : SourceSpan) : Except Diagnostic EnumExpansion := do
  if selectedProfile != IR.BehavioralStructural.profile then
    throw (Resolution.errorAt name "behavioral.profile" "unsupported behavioral profile" .unsupported)
  if literals.isEmpty then
    throw (Resolution.errorAt name "behavioral.enum-empty" "an enum requires a literal")
  let abstractToken := { name with text := "abstract" }
  let family := Element.declaration { name, abstractToken := some abstractToken } [] span
  let values := literals.map fun literal => Element.declaration
    { name := literal, super := some name,
      cardinality := some ⟨#[], 1, some 1⟩ } [] literal.span
  return ⟨family :: values, literals⟩

/-- `=` becomes a strict presence-guarded equation in the enclosing attachment.
Both views are supplied by the expression resolver; no extra dref is inserted. -/
def constantInitializer (token : Token) (heads left value : Expr) : Except Diagnostic Expr :=
  if token.text = "=" then
    let present := Expr.unary { token with text := "some" } heads heads.span
    let equation := Expr.binary token left value
      ⟨left.span.file, left.span.startByte, value.span.endByte⟩
    .ok (.binary { token with text := "=>" } present equation
      ⟨heads.span.file, heads.span.startByte, value.span.endByte⟩)
  else if token.text = ":=" then
    .error (Resolution.errorAt token "behavioral.default-initializer" "default initializers are unsupported" .unsupported)
  else .error (Resolution.errorAt token "behavioral.initializer-token" "invalid initializer")

end ClaferCompiler.Frontend.BehavioralDeclarations
