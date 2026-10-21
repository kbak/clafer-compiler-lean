module

public import ClaferCompiler.Backend.Alloy.Bounds
public import ClaferCompiler.Backend.Alloy.Parse

@[expose] public section

namespace ClaferCompiler.Backend.Alloy.Text

/-! Deterministic, fully parenthesized serialization with checked reconstruction.
No source name, filename, diagnostic, or comment enters executable syntax.
[impl->req~compiler-alloy-text~1] -/

def parens (s : String) : String := "( " ++ s ++ " )"
def binary (op a b : String) : String := parens (a ++ " " ++ op ++ " " ++ b)
def unary (op a : String) : String := parens (op ++ " " ++ a)

def multText : Multiplicity → String
  | .set => "set" | .lone => "lone" | .one => "one" | .some => "some"

def relText (depth : Nat) (r : Rel) : String := r.fold {
  empty := fun a => match a with | .unary => parens "none" | .binary => parens "none -> none"
  sig := fun i => parens (Symbol.signature i).name
  field := fun i => parens (Symbol.field i).name
  var := fun i => parens (Symbol.binder (depth - i - 1)).name
  union := binary "+", inter := binary "&", diff := binary "-"
  product := binary "->", join := binary ".", transpose := unary "~"
} ""

def intText (depth : Nat) : Integer → String
  | .literal n => parens n.repr
  | .count r => unary "#" (relText depth r)

def formulaText (p : Formula) (depth : Nat := 0) : String := p.fold {
  truth := fun _ => parens "no none", falsity := fun _ => parens "some none"
  equal := fun a b d => binary "=" (relText d a) (relText d b)
  subset := fun a b d => binary "in" (relText d a) (relText d b)
  mult := fun m r d => match m with
    | .set => binary "in" (parens (relText d r)) (parens (relText d r))
    | _ => unary (multText m) (relText d r)
  compare := fun op a b d => binary (match op with | .eq => "=" | .lt => "<" | .le => "=<")
      (intText d a) (intText d b)
  neg := fun p d => unary "not" (p d)
  conj := fun p q d => binary "and" (p d) (q d)
  disj := fun p q d => binary "or" (p d) (q d)
  implies := fun p q d => binary "implies" (p d) (q d)
  all := fun r p d => parens ("all " ++ (Symbol.binder d).name ++ " : " ++ relText d r ++ " | " ++ p (d + 1))
  exists_ := fun r p d => parens ("some " ++ (Symbol.binder d).name ++ " : " ++ relText d r ++ " | " ++ p (d + 1))
} (fun _ => "") depth

/-- Token pieces optionally locate a declaration identity. Only these pieces
contribute source-map ranges; every output character is ASCII. -/
structure Chunk where
  text : String
  symbol : Option Symbol := none

def signatureChunks (m : Module) (sig : Signature) (i : Nat) : List Chunk :=
  let leading := (if sig.isAbstract then "abstract " else "") ++
    (if sig.multiplicity == .set then "" else multText sig.multiplicity ++ " ") ++ "sig "
  let parent := sig.parent.map (fun p => " extends " ++ (Symbol.signature p).name) |>.getD ""
  let fields := (m.schema.fields.zipIdx.filter (fun (f, _) => f.owner == i)).map fun (f, j) =>
    [⟨(Symbol.field j).name, some (.field j)⟩,
     ⟨" : " ++ multText f.multiplicity ++ " " ++ (Symbol.signature f.target).name, none⟩]
  [⟨leading, none⟩, ⟨(Symbol.signature i).name, some (.signature i)⟩, ⟨parent ++ " { ", none⟩] ++
    (List.intercalate [⟨" , ", none⟩] fields) ++ [⟨" }\n", none⟩]

def commandText (c : Command) : String :=
  let scopes := c.scopes.zipIdx.map fun (s, i) =>
    (if s.exact then "exactly " else "") ++ s.size.repr ++ " " ++ (Symbol.signature i).name
  (match c.kind with | .run => "run" | .check => "check") ++
    " { " ++ formulaText c.body ++ " } for " ++ c.bitwidth.repr ++ " Int" ++
    (if scopes.isEmpty then "" else " , " ++ String.intercalate " , " scopes) ++ "\n"

def chunks (m : Module) : List Chunk :=
  (m.schema.signatures.zipIdx.flatMap fun (s, i) => signatureChunks m s i) ++
  (m.facts.map fun p => ⟨"fact { " ++ formulaText p ++ " }\n", none⟩) ++
  [⟨commandText m.command, none⟩]

def serialize (m : Module) : String := String.join ((chunks m).map Chunk.text)

def sourceFor (names : Names) : Symbol → Option SourceName
  | .signature i => (names.signatures[i]?).join
  | .field i => (names.fields[i]?).join
  | _ => none

def sourceMap (m : Module) (names : Names) : List Mapping :=
  ((chunks m).foldl (fun (state : Nat × List Mapping) c =>
    let next := state.1 + c.text.utf8ByteSize
    let entries := match c.symbol with
      | none => state.2
      | some s => ⟨s, c.text, sourceFor names s, state.1, next⟩ :: state.2
    (next, entries)) (0, [])).2.reverse

def SourceName.valid (s : SourceName) : Bool :=
  match s.logicalFile, s.startByte, s.endByte with
  | none, none, none => true
  | some _, some a, some b => a ≤ b
  | _, _, _ => false

def Names.valid (names : Names) (m : Module) : Bool :=
  names.signatures.length == m.schema.signatures.length &&
  names.fields.length == m.schema.fields.length &&
  (names.signatures ++ names.fields).all (fun source => source.all SourceName.valid)

def anonymousNames (m : Module) : Names :=
  ⟨List.replicate m.schema.signatures.length none, List.replicate m.schema.fields.length none⟩

inductive RenderError where
  | malformedMetadata | syntaxCorrespondence
  deriving DecidableEq, BEq

/-- A successful rendering carries a kernel-level text reconstruction equation.
Native evaluation of the check and subsequent Analyzer execution retain their
usual runtime trust boundaries. This is translation validation, not a theorem
that every checked target necessarily renders successfully. -/
structure Rendered (m : CheckedModule) where
  text : String
  mappings : List Mapping
  reconstructed : parse text = some m.raw

def render (m : CheckedModule) (names : Names) : Except RenderError (Rendered m) :=
  if names.valid m.raw then
    let text := serialize m.raw
    if h : parse text = some m.raw then .ok ⟨text, sourceMap m.raw names, h⟩
    else .error .syntaxCorrespondence
  else .error .malformedMetadata

/-- The independent parser reconstructs the entire resolved target, including
facts, field identity/order, binder indices, command polarity and all scopes.
[proof->req~compiler-alloy-text~1] -/
theorem render_roundTrip (m : CheckedModule) (out : Rendered m) :
    parse out.text = some m.raw := out.reconstructed

/-- Successful API calls validate the actual serializer output, not a caller's
alternate text or a representation supplied to the parser. -/
theorem render_reconstructs (m : CheckedModule) (names : Names) (out : Rendered m)
    (success : render m names = .ok out) : parse (serialize m.raw) = some m.raw := by
  unfold render at success
  split at success
  · dsimp only at success
    split at success
    · assumption
    · contradiction
  · contradiction

end ClaferCompiler.Backend.Alloy.Text
