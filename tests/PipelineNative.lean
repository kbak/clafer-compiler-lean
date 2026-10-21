module

public import ClaferCompiler.Driver.Source
public import ClaferCompiler.Backend.Alloy.Print
public import ClaferCompiler.SemanticsBridge.InheritedChecker
public import tests.ComparisonNative

@[expose] public section
/-! Test transport and exact-candidate evaluation. The source body evaluation
is justified by Pipeline.candidate_constraint_iff; inherited structural checking
has its own Inherited.check_correct theorem. Native execution is external evidence.
[utest->req~compiler-pipeline-correctness~1]
[utest->req~compiler-telematics~1] -/
namespace ClaferCompiler.Tests.PipelineNative
open Backend.Alloy

def tables (text : String) : Except String Instance := do
  let lines := text.trimAscii.toString.splitOn "\n"
  let ordinary := lines.filter fun s => !(s.startsWith "2 ")
  let i ← Comparison.tables (String.intercalate "\n" ordinary)
  let mut values := List.replicate i.signatures.length []
  for line in lines.filter (·.startsWith "2 ") do
    let [_, owner, atom, integer] := line.splitOn " " | throw "scalar row"
    let some owner := owner.toNat? | throw "scalar owner"
    let some atom := atom.toNat? | throw "scalar atom"
    let some integer := integer.toInt? | throw "scalar integer"
    if owner ≥ values.length then throw "scalar index"
    values := values.modify owner (· ++ [(atom,integer)])
  return {i with values}

def candidate (p : Driver.Source.Product) (i : Instance) :
    Except String (Clafer.Verification.Candidate p.prepared.resolved.count) := do
  let .ok o := Inherited.decode p.validated i | throw "structural decoding"
  let size := o.objects.length
  if o.objects != List.range size then throw "noncanonical test atom labels"
  if h : o.root < size then
    return {size, root := ⟨o.root,h⟩
            head := fun d x => (o.heads d).contains x.val
            contains := fun d x y => (o.containment d).contains (x.val,y.val)
            deref := fun d x y => (o.dereference d).contains (x.val,y.val)}
  else throw "root outside carrier"

def truth : Option Bool → String
  | none => "undefined" | some true => "true" | some false => "false"

def run (args : List String) : IO Unit := do
  let [source, bounds, directory, tableFile, mutation] := args | throw (IO.userError "arguments")
  let .ok p := Driver.Source.compile source (← IO.FS.readFile source)
      bounds (← IO.FS.readFile bounds) | throw (IO.userError "source compilation")
  let out := System.FilePath.mk directory
  let facts := if mutation.startsWith "drop-constraint:" then
      p.module.raw.facts.filter (fun f => !(p.encoded.bodies.filter
        (fun b => some b.original.id == (mutation.drop 16).toString.toNat?)
        |>.map (·.formula)).contains f)
    else if mutation == "drop-inherited-group" then
      p.module.raw.facts.filter (fun f => !(Inherited.groups p.validated).contains f)
    else p.module.raw.facts
  let .ok target := check {p.module.raw with facts} | throw (IO.userError "target check")
  let .ok rendered := Text.render target (Text.anonymousNames target.raw)
    | throw (IO.userError "render")
  IO.FS.writeFile (out / "generated.als") rendered.text
  let mapping := p.encoded.declarations.map fun d => Comparison.row
    [d.id, d.signature, d.containment.map (· + 1) |>.getD 0,
      d.dereference.map (· + 1) |>.getD 0]
  IO.FS.writeFile (out / "mapping.rows") (String.join mapping)
  let schema := target.raw.schema
  let signatures := schema.signatures.zipIdx.map fun (s,id) => Comparison.row
    [0,id,s.parent.map (· + 1) |>.getD 0,if s.isAbstract then 1 else 0,if s.scalar then 1 else 0]
  let fields := schema.fields.zipIdx.map fun (f,id) => Comparison.row [1,id,f.owner,f.target]
  IO.FS.writeFile (out / "schema.rows") (String.join (signatures ++ fields))
  IO.FS.writeFile (out / "bodies.rows") (String.join (p.encoded.bodies.map fun e =>
    Comparison.row [e.original.id,e.original.owner.val]))
  if tableFile != "-" then
    let .ok i := tables (← IO.FS.readFile tableFile) | throw (IO.userError "table transport")
    let .ok c := candidate p i | throw (IO.userError "candidate transport")
    let .ok value := evaluate target i | throw (IO.userError "target evaluation")
    let w := p.bounds.structural.bitwidth
    let lines := ["target " ++ toString value,
      "inherited " ++ toString (Verification.Inherited.check p.validated c),
      "numeric " ++ toString (p.encoded.numericFacts.all (fun f => f.eval w i [] == some true))] ++
      p.encoded.bodies.map (fun b => s!"body {b.original.id} " ++ truth (b.formula.eval w i []))
    IO.FS.writeFile (out / "evaluation.rows") (String.intercalate "\n" lines ++ "\n")

end ClaferCompiler.Tests.PipelineNative
