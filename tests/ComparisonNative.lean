module

public import ClaferCompiler.Backend.Alloy.Decode
public import ClaferCompiler.Backend.Alloy.Print

@[expose] public section
namespace ClaferCompiler.Tests.Comparison
open Backend.Alloy Backend.Alloy.Structural

/-! Test transport only: numeric rows written by the strict captured-core adapter.
This is not the production clafer-ir/1 parser or CLI (#19).
[utest->req~compiler-differential~1]
[utest->req~compiler-instance-decode~1] -/
def numbers (s : String) : Except String (List Nat) :=
  (s.splitOn " ").mapM fun t => match t.toNat? with
    | some n => .ok n | none => .error "invalid natural"

def upper (n : Nat) : IR.Structural.Upper :=
  if n == 0 then .unbounded else .finite (n - 1)

def edge (n : Nat) : Option Nat := if n == 0 then none else some (n - 1)

def declaration (xs : List Nat) : Except String (IR.Structural.Declaration Nat) := do
  let [id, parent, super, mode, target, abstract, lo, hi, gl, gh, _, _, _, _] := xs
    | throw "declaration row length"
  if mode > 2 || abstract > 1 then throw "declaration tag"
  return { id, name := toString id, origin := if id == 0 then .syntheticRoot else .user
           parent := edge parent, super := edge super
           reference := match mode with | 0 => .basic | 1 => .set target | _ => .bag target
           isAbstract := abstract == 1, localBounds := ⟨lo, upper hi⟩
           groupBounds := ⟨gl, upper gh⟩ }

def model (text : String) : Except String (IR.Structural.Raw × Structural.Bounds) := do
  let rows ← (text.trimAscii.toString.splitOn "\n").mapM numbers
  let [objects, width] :: rows := rows | throw "bounds row"
  let ds ← rows.mapM declaration
  let raw : IR.Structural.Raw := {
    declarations := ds.toArray, root := 0
    parentRanks := (rows.map (fun r => r[10]!)).toArray
    superRanks := (rows.map (fun r => r[11]!)).toArray
    unused := (rows.map fun r => r[12]! == 1).toArray }
  return (raw, ⟨rows.map (fun r => (r[0]!, ⟨r[13]!, false⟩)), objects, width⟩)

def row (xs : List Nat) : String := String.intercalate " " (xs.map toString) ++ "\n"

def candidateText (c : Candidate) : String :=
  row (0 :: c.objects) ++ row [1, c.root] ++
  String.join (c.members.map fun (d, x) => row [2, d, x]) ++
  String.join (c.containment.map fun (d, p, h) => row [3, d, p, h]) ++
  String.join (c.references.map fun (d, h, t) => row [4, d, h, t])

def tables (text : String) : Except String Instance := do
  let rows ← (text.trimAscii.toString.splitOn "\n").mapM numbers
  let [ns, nf] :: rows := rows | throw "table counts"
  if rows.length < ns then throw "missing signatures"
  let signatures ← (rows.take ns).mapM fun r => match r with
    | 0 :: xs => pure xs | _ => throw "signature row"
  let mut fields := List.replicate nf []
  for r in rows.drop ns do
    let [1, id, a, b] := r | throw "field row"
    if id ≥ nf then throw "field index"
    fields := fields.modify id (fun xs => xs ++ [[a, b]])
  return ⟨signatures, fields, []⟩

def run (args : List String) : IO Unit := do
  let [action, input, directory, parameter] := args | throw (IO.userError "arguments")
  let out := System.FilePath.mk directory
  let .ok (r, b) := model (← IO.FS.readFile input) | throw (IO.userError "model transport")
  let .ok v := IR.Structural.validateRaw r | throw (IO.userError "source admission")
  if action == "decode" then
    let .ok i := tables (← IO.FS.readFile parameter) | throw (IO.userError "table transport")
    match decodeCandidate v i with
    | .error e => IO.FS.writeFile (out / "decoded.error") (reprStr e)
    | .ok c => IO.FS.writeFile (out / "decoded.rows") (candidateText c)
  else
    let .ok c := compile v b | do
      let status := match compile v b with
        | .error .unsupportedBounds => "unsupported"
        | .error .malformedBounds => "malformed"
        | _ => "error"
      IO.FS.writeFile (out / "compile.error") status
      return
    let facts := c.module.raw.facts.zip c.obligations
    let retained := facts.filterMap fun (f, tag) =>
      let drop := match tag with
        | .localBounds _ => parameter == "drop-cardinality"
        | .groupBounds _ => parameter == "drop-group"
        | _ => false
      if drop then none else some f
    let .ok m := check { c.module.raw with facts := retained } | throw (IO.userError "target admission")
    let .ok rendered := Text.render m (Text.anonymousNames m.raw) | throw (IO.userError "render")
    IO.FS.writeFile (out / "generated.als") rendered.text
    let maps := c.declarations.map fun d =>
      row [d.id, d.signature, d.containment.map (· + 1) |>.getD 0,
        d.dereference.map (· + 1) |>.getD 0]
    IO.FS.writeFile (out / "mapping.rows") (String.join maps)
    let schema := m.raw.schema
    let sigs := schema.signatures.zipIdx.map fun (s, id) =>
      row [0, id, s.parent.map (· + 1) |>.getD 0, if s.isAbstract then 1 else 0]
    let fields := schema.fields.zipIdx.map fun (f, id) => row [1, id, f.owner, f.target]
    IO.FS.writeFile (out / "schema.rows") (String.join (sigs ++ fields))

end ClaferCompiler.Tests.Comparison
