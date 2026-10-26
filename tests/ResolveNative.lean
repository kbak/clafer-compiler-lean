module

public import ClaferCompiler.Frontend.Parser
public import ClaferCompiler.Frontend.Resolve

@[expose] public section
namespace ClaferCompiler.Tests.Resolve
open Frontend Frontend.Resolution IR.Structural

def boundText (b : Bounds) : String :=
  s!"{b.lower}.." ++ (match b.upper with | .finite n => toString n | .unbounded => "*")

def groupText : Group → String
  | .bounds _ => "numeric" | .xor => "xor" | .or => "or" | .mux => "mux" | .opt => "opt"

def render (file source : String) : String :=
  match Frontend.parse file source with
  | .error e => s!"error|{e.code}|{e.primary.startByte}|{e.primary.endByte}"
  | .ok doc => match elaborate doc with
    | .error e => s!"error|{e.code}|{e.primary.startByte}|{e.primary.endByte}|{e.line}|{e.column}|{e.related.size}"
    | .ok e => Id.run do
      let c := e.candidate
      let mut lines := ["ok", match toM1 doc e with | .ok _ => "m1|ok" | .error err => "m1|" ++ err.code]
      for i in List.finRange e.count do
        let d := c.core.get i
        let edge := fun (o : Option (Fin e.count)) => o.map (toString ∘ Fin.val) |>.getD "_"
        let ref := match d.reference with | .basic => "basic" | .set _ => "set" | .bag _ => "bag"
        let origin := match d.origin with
          | .syntheticRoot => "root" | .integer => "int" | _ => "user"
        lines := lines ++ [String.intercalate "|" [toString d.id, d.name, origin,
          edge d.parent, edge d.super, ref, edge d.reference.target, toString d.isAbstract,
          boundText d.localBounds, boundText d.groupBounds, groupText c.groups[i],
          toString (constraints doc c i).length,
          String.intercalate "." ((c.paths[i].getD []).map toString),
          (d.authored.map (fun a => toString a.isAbstract)).getD "_",
          (d.authored.bind (·.localBounds) |>.map boundText).getD "_"]]
      return String.intercalate "\n" lines

/-- Deliberate mutations exercise the independent source validator, including
well-formed tables whose target/defaults no longer correspond to the source. -/
def mutationChecks : IO Unit := do
  -- Exact fixed points may stop early; nonconverging updates retain their budget.
  unless repeatStable (fun x : Nat => x + 1) 0 7 == 7 &&
      repeatStable (fun x : Nat => x + 1) 5 0 == 5 &&
      repeatStable (fun x : Nat => if x == 0 then 1 else 0) 5 0 == 1 &&
      repeatStable (fun x : Nat => min (x + 1) 3) 20 0 == 3 do
    throw (IO.userError "bounded fixed-point iteration")
  let .ok doc := Frontend.parse "mutations.cfr" "Target\nOther\nOwner\n  r -> Target\n"
    | throw (IO.userError "mutation parser failed")
  let .ok e := elaborate doc | throw (IO.userError "mutation elaboration failed")
  if h : 4 < e.count then
    let c := e.candidate
    let r : Fin e.count := ⟨4, h⟩
    let other : Fin e.count := ⟨2, by omega⟩
    let owner : Fin e.count := ⟨3, by omega⟩
    let wrongTarget := { c with core := { c.core with
      declarations := c.core.declarations.set r { c.core.get r with reference := .set other } } }
    let wrongDefault := { c with core := { c.core with
      declarations := c.core.declarations.set r { c.core.get r with localBounds := ⟨0, .finite 1⟩ } } }
    let wrongParent := { c with core := { c.core with
      declarations := c.core.declarations.set r { c.core.get r with parent := some other } } }
    let missingSource := { c with paths := c.paths.set r none }
    let duplicatePath := { c with paths := c.paths.set r c.paths[owner] }
    for candidate in [wrongTarget, wrongDefault, wrongParent, missingSource, duplicatePath] do
      if decide (Elaboration doc candidate) then
        throw (IO.userError "source validator accepted a semantic mutation")
    unless decide (coreChecks wrongTarget.core wrongTarget.certificate) do
      throw (IO.userError "wrong-target witness must remain structurally well-formed")
  else throw (IO.userError "mutation inventory incomplete")
  let .ok numericDoc := Frontend.parse "numeric.cfr" "1..1 Owner\n  child\n"
    | throw (IO.userError "numeric mutation parser failed")
  let .ok numeric := elaborate numericDoc
    | throw (IO.userError "numeric mutation elaboration failed")
  if h : 2 < numeric.count then
    let c := numeric.candidate
    let child : Fin numeric.count := ⟨2, h⟩
    let oldDefault := { c with core := { c.core with
      declarations := c.core.declarations.set child
        { c.core.get child with localBounds := ⟨1, .finite 1⟩ } } }
    unless decide (coreChecks oldDefault.core oldDefault.certificate) do
      throw (IO.userError "old numeric default witness must remain structurally well-formed")
    if decide (Elaboration numericDoc oldDefault) then
      throw (IO.userError "source validator accepted the old numeric default")
  else throw (IO.userError "numeric mutation inventory incomplete")

def run (args : List String) : IO Unit := do
  mutationChecks
  for file in args do
    let text ← IO.FS.readFile file
    IO.println (render file text ++ "\nEND")

end ClaferCompiler.Tests.Resolve
