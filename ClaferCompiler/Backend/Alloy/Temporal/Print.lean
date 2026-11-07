module

public import ClaferCompiler.Backend.Alloy.Temporal.Parse
public import ClaferCompiler.Backend.Alloy.Print

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Temporal.Text
open Alloy.Text (Symbol Names Mapping Chunk parens binary unary multText sourceMapChunks RenderError)

-- [impl->req~compiler-alloy-temporal-text~1]
def relText (d : Nat) (r : Rel) : String :=
  r.fold {
    empty := fun a => if a == .unary then parens "none" else parens "none -> none"
    sig := fun i => parens (Symbol.signature i).name
    field := fun i => parens (Symbol.field i).name
    var := fun i => parens (Symbol.binder (d - i - 1)).name
    univ := parens "univ", iden := parens "iden", ints := parens "Int"
    integer := fun n => parens ("Int [ " ++ parens n.repr ++ " ]")
    values := fun owner => parens (Symbol.auxiliary owner).name
    union := binary "+", inter := binary "&", diff := binary "-"
    product := binary "->", join := binary ".", transpose := unary "~"
    prime := fun r => parens (r ++ " '") } ""

def intText (d : Nat) (n : Integer) : String :=
  n.fold {
    literal := fun n => parens n.repr
    count := fun r => unary "#" (relText d r)
    scalar := fun lo hi r =>
      let rel := relText d r
      let value := parens ("sum [ " ++ rel ++ " ]")
      let guard := binary "and" (unary "one" rel)
        (binary "and" (binary "in" rel (parens "Int"))
          (binary "and" (binary "=<" (parens lo.repr) value)
            (binary "=<" value (parens hi.repr))))
      parens (guard ++ " implies " ++ value ++ " else " ++ parens lo.repr)
    add := fun a b => parens ("plus [ " ++ a ++ " , " ++ b ++ " ]")
    subtract := fun a b => parens ("minus [ " ++ a ++ " , " ++ b ++ " ]")
    multiply := fun a b => parens ("mul [ " ++ a ++ " , " ++ b ++ " ]")
    divide := fun a b => parens ("div [ " ++ a ++ " , " ++ b ++ " ]")
    remainder := fun a b => parens ("rem [ " ++ a ++ " , " ++ b ++ " ]") } ""

def unaryText : Unary → String
  | .neg => "not" | .after => "after" | .always => "always" | .eventually => "eventually"
  | .before => "before" | .once => "once" | .historically => "historically"

def binaryText : Binary → String
  | .conj => "and" | .disj => "or" | .implies => "implies" | .until => "until"
  | .releases => "releases" | .since => "since" | .triggered => "triggered"

def formulaText (d : Nat) (p : Formula) : String :=
  p.fold {
    truth := fun _ => parens "no none", falsity := fun _ => parens "some none"
    equal := fun a b d => binary "=" (relText d a) (relText d b)
    subset := fun a b d => binary "in" (relText d a) (relText d b)
    mult := fun m r d => if m == .set then
        binary "in" (parens (relText d r)) (parens (relText d r))
      else unary (multText m) (relText d r)
    compare := fun op a b d => binary (match op with | .eq => "=" | .lt => "<" | .le => "=<")
      (intText d a) (intText d b)
    unary := fun op p d => unary (unaryText op) (p d)
    binary := fun op p q d => binary (binaryText op) (p d) (q d)
    all := fun r p d => parens ("all " ++ (Symbol.binder d).name ++ " : " ++ relText d r ++ " | " ++ p (d + 1))
    exists_ := fun r p d => parens ("some " ++ (Symbol.binder d).name ++ " : " ++ relText d r ++ " | " ++ p (d + 1)) } (fun _ => "") d

def signatureChunks (m : Module) (sig : Alloy.Signature) (i : Nat) : List Chunk :=
  let leading := (if m.schema.mutableSignatures[i]?.getD false then "var " else "") ++
    (if sig.isAbstract then "abstract " else "") ++
    (if sig.multiplicity == .set then "" else multText sig.multiplicity ++ " ") ++ "sig "
  let parent := sig.parent.map (fun p => " extends " ++ (Symbol.signature p).name) |>.getD ""
  let fields := (m.schema.declarations.fields.zipIdx.filter (fun (f, _) => f.owner == i)).map fun (f, j) =>
    [⟨if m.schema.mutableFields[j]?.getD false then "var " else "", none⟩,
     ⟨(Symbol.field j).name, some (.field j)⟩,
     ⟨" : " ++ multText f.multiplicity ++ " " ++ (Symbol.signature f.target).name, none⟩]
  let fields := fields ++ if sig.scalar then
    [[⟨"var ", none⟩, ⟨(Symbol.auxiliary i).name, some (.auxiliary i)⟩,
      ⟨" : one Int", none⟩]] else []
  [⟨leading, none⟩, ⟨(Symbol.signature i).name, some (.signature i)⟩, ⟨parent ++ " { ", none⟩] ++
    List.intercalate [⟨" , ", none⟩] fields ++ [⟨" }\n", none⟩]

def commandText (c : Command) : String :=
  let scopes := c.scopes.zipIdx.map fun (s, i) =>
    (if s.exact then "exactly " else "") ++ s.size.repr ++ " " ++ (Symbol.signature i).name
  (match c.kind with | .run => "run" | .check => "check") ++
    " { " ++ formulaText 0 c.body ++ " } for " ++ c.bitwidth.repr ++ " Int , " ++
    c.minSteps.repr ++ " .. " ++ c.maxSteps.repr ++ " steps" ++
    (if scopes.isEmpty then "" else " , " ++ String.intercalate " , " scopes) ++ "\n"

def chunks (m : Module) : List Chunk :=
  (m.schema.declarations.signatures.zipIdx.flatMap fun (s, i) => signatureChunks m s i) ++
  m.facts.map (fun p => ⟨"fact { " ++ formulaText 0 p ++ " }\n", none⟩) ++
  [⟨commandText m.command, none⟩]

def serialize (m : Module) : String := String.join ((chunks m).map Chunk.text)

def validNames (names : Names) (m : Module) : Bool :=
  names.signatures.length == m.schema.declarations.signatures.length &&
  names.fields.length == m.schema.declarations.fields.length &&
  (names.signatures ++ names.fields).all (fun s => s.all Alloy.Text.SourceName.valid)

def anonymousNames (m : Module) : Names :=
  ⟨List.replicate m.schema.declarations.signatures.length none,
   List.replicate m.schema.declarations.fields.length none⟩

structure Rendered (m : CheckedModule) where
  text : String
  mappings : List Mapping
  reconstructed : parse text = some m.raw

/-- Translation validation is mandatory before returning bytes and mappings. -/
def render (m : CheckedModule) (names : Names) : Except RenderError (Rendered m) :=
  if validNames names m.raw then
    let pieces := chunks m.raw
    let text := String.join (pieces.map Chunk.text)
    if h : parse text = some m.raw then .ok ⟨text, sourceMapChunks pieces names, h⟩
    else .error .syntaxCorrespondence
  else .error .malformedMetadata

-- [proof->req~compiler-alloy-temporal-text~1]
theorem render_roundTrip (m : CheckedModule) (out : Rendered m) :
    parse out.text = some m.raw := out.reconstructed

theorem render_reconstructs (m : CheckedModule) (names : Names) (out : Rendered m)
    (success : render m names = .ok out) : parse (serialize m.raw) = some m.raw := by
  unfold render at success
  split at success
  · dsimp only at success
    split at success
    · assumption
    · contradiction
  · contradiction

end ClaferCompiler.Backend.Alloy.Temporal.Text
