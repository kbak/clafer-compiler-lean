module

public import ClaferCompiler.Driver.Source
public import ClaferCompiler.Driver.Behavioral
public import ClaferCompiler.Driver.BehavioralSyntax
public import ClaferCompiler.Frontend.Behavioral.Elaborate
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile

@[expose] public section
namespace ClaferCompiler.Driver.BehavioralSource
open Lean Decode Backend.Alloy
namespace Full
abbrev Bounds := Behavioral.Full.Bounds
abbrev Request := Behavioral.Full.Request
abbrev Compiled := Behavioral.Full.Compiled
end Full

structure Scenario where
  file : String
  text : String
  owner : Option Nat := none

inductive Query where
  | model
  | check (assertion : Nat)
  | run (scenario : Scenario)

-- [impl->req~compiler-behavioral-integration~1]
def bounds (file text : String) : Except Diagnostic Full.Bounds := do
  let n ← parse file text true
  version n "version" "clafer-behavioral-bounds/2" "bounds.version"
  version n "profile" IR.BehavioralStructural.profile "behavioral.profile"
  closed n ["version", "profile", "objects", "bitwidth", "declarations", "minSteps", "maxSteps", "integers"]
  let low ← natural (← field n "minSteps")
  let high ← natural (← field n "maxSteps")
  if low == 0 || high < low then throw (bad n "expected 1 ≤ minSteps ≤ maxSteps")
  let ints ← field n "integers"
  closed ints ["lower", "upper"]
  let lo ← Source.integer (← field ints "lower")
  let hi ← Source.integer (← field ints "upper")
  if lo > hi then throw (bad ints "integer interval is reversed")
  return {
    objects := ← natural (← field n "objects")
    bitwidth := ← natural (← field n "bitwidth")
    declarations := (← array scope (← field n "declarations")).toList
    minSteps := low, maxSteps := high, values := some ⟨lo, hi⟩ }

def completeScopes (file : String) (v : IR.BehavioralStructural.Validated k)
    (b : Full.Bounds) : Except Diagnostic Unit := do
  let ids := ((List.finRange k).filter fun d =>
    !Behavioral.Full.integerDeclaration v d).map fun d => (v.core.structural.get d).id
  unless (b.declarations.map Prod.fst).Nodup && b.declarations.length == ids.length &&
      b.declarations.all (fun row => ids.contains row.1) do
    throw {
      code := "bounds.declarations", phase := "bounds", file, pointer := "/declarations"
      message := "each nonprimitive declaration ID requires exactly one scope" }

-- [impl->req~compiler-behavioral-integration~1]
def request (p : Frontend.Behavioral.ParsedModel) (query : Query) :
    Except Diagnostic (Full.Request p.elaborated.declarations.resolved.count) := do
  match query with
  | .model => return ⟨p.elaborated.model, .run []⟩
  | .check index => p.elaborated.check index |>.mapError Diagnostic.ofSource
  | .run scenario =>
    let v := p.elaborated.model.structural
    let owner ← match scenario.owner with
      | none => pure v.core.structural.root
      | some id => match IR.Structural.lookup v.core.structural.declarations id with
        | some d => pure d
        | none => throw {
            code := "behavioral.scenario-owner", phase := "elaboration"
            file := scenario.file, declaration := some id, message := "unknown scenario owner ID" }
    let doc ← Frontend.Behavioral.parseBehavioral IR.BehavioralStructural.profile
      scenario.file scenario.text |>.mapError Diagnostic.ofSource
    p.elaborated.run [⟨owner, doc⟩] |>.mapError Diagnostic.ofSource

/-- Source-size allocation includes room for surface expansions and generated
modifiers. Exhaustion is explicitly unsupported in the existing lowerer. -/
def budget (source : String) (query : Query) : Nat :=
  64 + 8 * (source.utf8ByteSize + match query with | .run s => s.text.utf8ByteSize | _ => 0)

def sourceName (d : IR.Structural.Declaration (Fin k)) : Text.SourceName := {
  displayName := d.name, logicalFile := d.source.map (·.file)
  startByte := d.source.map (·.startByte), endByte := d.source.map (·.endByte) }

def names (v : IR.BehavioralStructural.Validated k) : Text.Names := {
  signatures := none :: (List.finRange k).map (fun d => some (sourceName (v.core.structural.get d)))
  fields := [none, none] ++ (List.finRange k).map (fun d => some (sourceName (v.core.structural.get d))) }

def constraintSyntax (encode : BehavioralSyntax.Pass k) (m : IR.Structural.Core k)
    (c : Behavioral.Full.Constraint k) : Except Diagnostic BehavioralSyntax.Encoded := do
  let body ← encode.formula c.body
  return ⟨Json.mkObj [("owner", toJson (m.get c.owner).id),
    ("source", sourceSpanJson c.source), ("body", body.json)], body.depth⟩

def inspectRequest (r : Full.Request k) (allocation : Nat) : Except Diagnostic BehavioralSyntax.Encoded := do
  let encode := BehavioralSyntax.encode r.model.structural.core.structural allocation
  let constraints ← r.model.constraints.mapM (constraintSyntax encode r.model.structural.core.structural)
  let assertions ← r.model.assertions.mapM (constraintSyntax encode r.model.structural.core.structural)
  let scenario ← (match r.command with | .run cs => cs | .check _ => []).mapM
    (constraintSyntax encode r.model.structural.core.structural)
  let modifiers ← ((List.finRange k).flatMap fun d =>
    (IR.Behavioral.Modifiers.effective r.model.structural r.model.modifiers d).flatMap
      (Behavioral.Full.modifierExpansions d)).mapM fun (_, body) => encode.formula body
  return ⟨Json.mkObj [("version", toJson "clafer-behavioral-source-inspection/1"),
    ("constraints", toJson (constraints.map (·.json))),
    ("assertions", toJson (assertions.map (·.json))),
    ("scenario", toJson (scenario.map (·.json)))],
    (constraints ++ assertions ++ scenario ++ modifiers).foldl (fun n a => max n a.depth) 1⟩

structure Product where
  parsed : Frontend.Behavioral.ParsedModel
  request : Full.Request parsed.elaborated.declarations.resolved.count
  bounds : Full.Bounds
  fuel : Nat
  compiled : Full.Compiled
  text : String
  mappings : List Text.Mapping
  inspected : Json
  compiled_checked : Behavioral.Full.compile request bounds fuel = .ok compiled

def encodingDiagnostic (boundsFile : String) (e : IR.Structural.Diagnostic) : Diagnostic := {
  code := e.code, phase := "encoding", file := boundsFile, pointer := e.pointer
  declaration := e.declaration
  category := if e.code == "behavioral.internal-target" then .operational else
    match e.category with | .malformed => .malformed | .unsupported => .unsupported
  message := "behavioral encoding or conservative range admission failed" }

def bodyDiagnostic (source : String)
    (span : IR.Structural.SourceSpan) (e : IR.Structural.Diagnostic) : Diagnostic :=
  Diagnostic.ofSource (Frontend.Constraints.errorAt ⟨span.file, source, []⟩ span e.code
    "source expression exceeds the selected behavioral encoding bounds" e.category)

-- [impl->req~compiler-behavioral-integration~1]
def compile (file source boundsFile boundsText : String) (query : Query := .model)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Product := do
  let p ← Frontend.Behavioral.parseAndElaborate IR.BehavioralStructural.profile file source
    |>.mapError Diagnostic.ofSource
  let r ← request p query
  let b ← bounds boundsFile boundsText
  let b := { b with objects := objects.getD b.objects, bitwidth := bitwidth.getD b.bitwidth }
  completeScopes boundsFile r.model.structural b
  let encoded ← inspectRequest r (budget source query)
  let fuel := encoded.depth + 1
  let out ← match MonadAttach.attach (Behavioral.Full.compile r b fuel) with
    | .ok out => pure out
    | .error e => do
      -- Attribute only actual expression failures to the authored input.
      if let .ok _ := Behavioral.Full.validateBounds r.model.structural b then
        let active := r.model.constraints.map (source, ·) ++ (match r.command with
          | .run cs => cs.map ((match query with | .run s => s.text | _ => source), ·)
          | .check i => [(source, r.model.assertions[i])])
        for (bodySource, c) in active do
          if let .error error := Behavioral.Full.constraint r.model.structural b fuel c then
            throw (bodyDiagnostic bodySource c.source error)
      throw (encodingDiagnostic boundsFile e)
  let rendered ← Temporal.Text.render out.val.module (names r.model.structural) |>.mapError fun _ =>
    { code := "compiler.render", phase := "serialization", category := .operational
      message := "generated temporal text failed checked reconstruction" : Diagnostic }
  return ⟨p, r, b, fuel, out.val, rendered.text, rendered.mappings, encoded.json, out.property⟩

/-- Additive reporting API; the compiled product and its closed schema are unchanged. -/
structure Report where
  product : Product
  warnings : List Frontend.Behavioral.Warning

-- [impl->req~compiler-diagnostics~1]
-- [impl->req~compiler-behavioral-integration~1]
def compileReport (file source boundsFile boundsText : String) (query : Query := .model)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Report := do
  let product ← compile file source boundsFile boundsText query objects bitwidth
  let scenarioWarnings ← match query with
    | .run s => do
      let doc ← Frontend.Behavioral.parseBehavioral IR.BehavioralStructural.profile s.file s.text
        |>.mapError Diagnostic.ofSource
      pure (Frontend.Behavioral.Warnings.document doc)
    | _ => pure []
  return ⟨product, Frontend.Behavioral.Warnings.document product.parsed.source ++ scenarioWarnings⟩

-- [impl->req~compiler-diagnostics~1]
def warningJson (w : Frontend.Behavioral.Warning) : Json :=
  Json.mkObj [("version", toJson "clafer-warning/1"), ("severity", toJson "warning"),
    ("code", toJson w.code), ("phase", toJson "elaboration"), ("message", toJson w.message),
    ("operator", toJson w.operator), ("primary", Json.mkObj [
      ("kind", toJson "source"), ("file", toJson w.primary.file),
      ("startByte", toJson w.primary.startByte), ("endByte", toJson w.primary.endByte),
      ("line", toJson w.line), ("column", toJson w.column)])]

def warningText (w : Frontend.Behavioral.Warning) : String :=
  s!"{w.primary.file}:{w.line}:{w.column}: warning [{w.code}]: {w.message}"

def constraintJson (m : IR.Structural.Core k) (c : Behavioral.Full.Constraint k) : Json :=
  Json.mkObj [("owner", toJson (m.get c.owner).id), ("source", sourceSpanJson c.source)]

def intervalJson (b : IR.Structural.Bounds) : Json :=
  Json.mkObj [("lower", toJson b.lower), ("upper", match b.upper with
    | .unbounded => Json.null | .finite n => toJson n)]

def modifierName : IR.Behavioral.Surface.Modifiers.Modifier → String
  | .initial => "initial" | .final => "final" | .finalref => "finalref" | .finaltarget => "finaltarget"

-- [impl->req~compiler-behavioral-integration~1]
def Product.json (p : Product) : Json :=
  let v := p.request.model.structural
  let m := p.compiled.module.raw
  Json.mkObj [
    ("version", toJson "clafer-behavioral-compilation/2"),
    ("profile", toJson IR.BehavioralStructural.profile), ("alloy", toJson p.text),
    ("command", match p.request.command with
      | .run _ => Json.mkObj [("kind", toJson "run")]
      | .check i => Json.mkObj [("kind", toJson "check"), ("assertion", toJson i.val)]),
    ("root", toJson (v.core.structural.get v.core.structural.root).id),
    ("resolved", p.inspected),
    ("declarations", toJson ((List.finRange p.parsed.elaborated.declarations.resolved.count).map fun d =>
      let row := v.core.structural.get d
      Json.mkObj [("id", toJson row.id), ("name", toJson row.name),
        ("primitive", toJson (Behavioral.Full.integerDeclaration v d)),
        ("signature", toJson (Behavioral.signatureName (Behavioral.Full.signatureId d))),
        ("referenceField", toJson (Behavioral.fieldName 0 (2 + d.val))),
        ("parent", toJson (row.parent.map fun i => (v.core.structural.get i).id)),
        ("super", toJson (row.super.map fun i => (v.core.structural.get i).id)),
        ("abstract", toJson v.core.authoredAbstract[d]),
        ("localBounds", intervalJson row.localBounds), ("groupBounds", intervalJson row.groupBounds),
        ("reference", Json.mkObj [("kind", toJson (match row.reference with
          | .basic => "basic" | .set _ => "set" | .bag _ => "bag")),
          ("target", toJson (row.reference.target.map fun i => (v.core.structural.get i).id))]),
        ("modifiers", toJson ((IR.Behavioral.Modifiers.effective v p.request.model.modifiers d).map modifierName)),
        ("referenceOwner", toJson (v.analysis.referenceOwners[d].map fun i => (v.core.structural.get i).id)),
        ("source", row.source.map sourceSpanJson |>.getD Json.null)])),
    ("signatures", Json.mkObj (m.schema.declarations.signatures.zipIdx.map fun (s, i) =>
      (Behavioral.signatureName i, Json.mkObj [
        ("mutable", toJson (m.schema.mutableSignatures[i]?.getD false)),
        ("abstract", toJson s.isAbstract),
        ("parent", toJson (s.parent.map Behavioral.signatureName |>.getD "univ"))]))),
    ("fields", Json.mkObj ((m.schema.declarations.fields.zipIdx.map fun (f, i) =>
      (Behavioral.fieldName f.owner i, Json.mkObj [
        ("mutable", toJson (m.schema.mutableFields[i]?.getD false)), ("arity", toJson (2 : Nat))])) ++
      [(Behavioral.signatureName 0 ++ "/" ++ (Text.Symbol.auxiliary 0).name,
        Json.mkObj [("mutable", toJson true), ("arity", toJson (2 : Nat))])])),
    ("scopes", Json.mkObj (m.command.scopes.zipIdx.map fun (s, i) =>
      (Behavioral.signatureName i, Json.mkObj [("count", toJson s.size), ("exact", toJson s.exact)]))),
    ("bitwidth", toJson m.command.bitwidth), ("minSteps", toJson m.command.minSteps),
    ("maxSteps", toJson m.command.maxSteps),
    ("integers", Json.mkObj [("lower", toJson (Behavioral.Full.integerRange p.bounds).lower),
      ("upper", toJson (Behavioral.Full.integerRange p.bounds).upper)]),
    ("constraints", toJson (p.request.model.constraints.map (constraintJson v.core.structural))),
    ("assertions", toJson (p.request.model.assertions.map (constraintJson v.core.structural))),
    ("scenario", toJson ((match p.request.command with | .run cs => cs | .check _ => []).map
      (constraintJson v.core.structural))),
    ("mappings", toJson (p.mappings.map fun m => Json.mkObj [
      ("name", toJson m.name), ("startByte", toJson m.startByte), ("endByte", toJson m.endByte),
      ("source", m.source.map (fun s => Json.mkObj [("name", toJson s.displayName),
        ("file", toJson s.logicalFile), ("startByte", toJson s.startByte),
        ("endByte", toJson s.endByte)]) |>.getD Json.null)]))]

end ClaferCompiler.Driver.BehavioralSource
