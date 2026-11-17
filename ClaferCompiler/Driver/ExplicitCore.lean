module

public import ClaferCompiler.Driver.ExplicitSyntax

@[expose] public section
namespace ClaferCompiler.Driver.ExplicitCore
open Lean Decode IR.Behavioral
open Behavioral (declarationIndex)
abbrev Request := Backend.Alloy.Behavioral.Full.Request
abbrev Constraint := Backend.Alloy.Behavioral.Full.Constraint

def spanJson (span : IR.Structural.SourceSpan) : Json := Json.mkObj [
  ("file", toJson span.file), ("startByte", toJson span.startByte), ("endByte", toJson span.endByte)]

def intervalJson (b : IR.Structural.Bounds) : Json := Json.mkObj [
  ("lower", toJson b.lower), ("upper", match b.upper with
    | .unbounded => toJson "*" | .finite n => toJson n)]

def declarationJson (m : IR.Structural.Core k) (d : Fin k) : Json :=
  let row := m.get d
  let id := fun d => (m.get d).id
  Json.mkObj [("id", toJson row.id), ("name", toJson row.name),
    ("origin", toJson (match row.origin with
      | .syntheticRoot => "root" | .user => "user" | .integer => "integer"
      | .string => "string" | .boolean => "boolean")),
    ("parent", toJson (row.parent.map id)), ("super", toJson (row.super.map id)),
    ("reference", match row.reference with
      | .basic => Json.mkObj [("kind", toJson "basic")]
      | .set d => Json.mkObj [("kind", toJson "set"), ("target", toJson (id d))]
      | .bag d => Json.mkObj [("kind", toJson "bag"), ("target", toJson (id d))]),
    ("isAbstract", toJson row.isAbstract), ("localBounds", intervalJson row.localBounds),
    ("groupBounds", intervalJson row.groupBounds),
    ("source", row.source.map spanJson |>.getD Json.null),
    ("authored", row.authored.map (fun a => Json.mkObj [
      ("isAbstract", toJson a.isAbstract),
      ("localBounds", a.localBounds.map intervalJson |>.getD Json.null),
      ("groupBounds", a.groupBounds.map intervalJson |>.getD Json.null)]) |>.getD Json.null)]

def groupJson : Frontend.Resolution.Group → Json
  | .bounds r => toJson [toJson "bounds", intervalJson r]
  | .xor => toJson [toJson "xor"] | .or => toJson [toJson "or"]
  | .mux => toJson [toJson "mux"] | .opt => toJson [toJson "opt"]

def structureJson (v : IR.BehavioralStructural.Validated k) : Json :=
  let m := v.core.structural
  Json.mkObj [("root", toJson (m.get m.root).id),
    ("declarations", toJson ((List.finRange k).map (declarationJson m))),
    ("parentRanks", toJson v.certificate.parentRank.toArray),
    ("superRanks", toJson v.certificate.superRank.toArray),
    ("unused", toJson v.certificate.unused.toArray),
    ("authoredAbstract", toJson v.core.authoredAbstract.toArray),
    ("groups", toJson (v.core.groups.toList.map groupJson))]

-- [impl->req~compiler-rich-core-explicit~1]
def encode (r : Request k) (budget : Nat) (warnings : List Frontend.Behavioral.Warning := [])
    (profile : String := IR.BehavioralStructural.richProfile) : Except Diagnostic Json := do
  let v := r.model.structural
  let pass := BehavioralSyntax.encode v.core.structural budget
  let property := fun (c : Constraint k) => do
    return Json.mkObj [("owner", toJson (v.core.structural.get c.owner).id),
      ("source", spanJson c.source), ("body", (← pass.formula c.body).json)]
  let command ← match r.command with
    | .check i => pure (Json.mkObj [("kind", toJson "check"), ("assertion", toJson i.val)])
    | .run cs => do pure (Json.mkObj [("kind", toJson "run"), ("scenario", toJson (← cs.mapM property))])
  return Json.mkObj [("version", toJson "clafer-explicit-core/1"),
    ("profile", toJson profile),
    ("structure", structureJson v),
    ("modifiers", toJson (r.model.modifiers.toList.map fun ms => ms.map BehavioralSource.modifierName)),
    ("constraints", toJson (← r.model.constraints.mapM property)),
    ("assertions", toJson (← r.model.assertions.mapM property)), ("command", command),
    ("warnings", toJson (warnings.map BehavioralSource.warningJson))]

def group (n : Node) : Except Diagnostic Frontend.Resolution.Group := do
  match ← Behavioral.tag n with
  | "bounds" => Behavioral.arity n 2; return .bounds (← interval (← Behavioral.arg n 1))
  | "xor" => Behavioral.arity n 1; return .xor
  | "or" => Behavioral.arity n 1; return .or
  | "mux" => Behavioral.arity n 1; return .mux
  | "opt" => Behavioral.arity n 1; return .opt
  | _ => throw (bad n "unknown group provenance")

def structureRead (n : Node) : Except Diagnostic (Σ k, IR.BehavioralStructural.Validated k) := do
  closed n ["root", "declarations", "parentRanks", "superRanks", "unused", "authoredAbstract", "groups"]
  let raw : IR.BehavioralStructural.Raw := {
    structural := {
      root := ← natural (← field n "root"), declarations := ← array declaration (← field n "declarations")
      parentRanks := ← array natural (← field n "parentRanks")
      superRanks := ← array natural (← field n "superRanks"), unused := ← array boolean (← field n "unused") }
    authoredAbstract := ← array boolean (← field n "authoredAbstract")
    groups := ← array group (← field n "groups") }
  let v ← IR.BehavioralStructural.validateRaw IR.BehavioralStructural.richProfile raw
    |>.mapError (admissionDiagnostic n.file)
  return ⟨_, v⟩

def modifier (n : Node) : Except Diagnostic Surface.Modifiers.Modifier :=
  ExplicitSyntax.choose n [("initial", .initial), ("final", .final),
    ("finalref", .finalref), ("finaltarget", .finaltarget)]

def property (m : IR.Structural.Core k) (budget : Nat) (n : Node) : Except Diagnostic (Constraint k) := do
  closed n ["owner", "source", "body"]
  return ⟨← declarationIndex m (← field n "owner"),
    ← (ExplicitSyntax.decode m budget).formula (← field n "body"), ← source (← field n "source")⟩

/-- Retained source diagnostics are metadata, not assumptions of correctness. -/
def warning (n : Node) : Except Diagnostic Frontend.Behavioral.Warning := do
  closed n ["version", "severity", "code", "phase", "message", "operator", "primary"]
  version n "version" "clafer-warning/1" "warning.version"
  version n "severity" "warning" "warning.severity"
  version n "phase" "elaboration" "warning.phase"
  let p ← field n "primary"
  closed p ["kind", "file", "startByte", "endByte", "line", "column"]
  version p "kind" "source" "warning.location"
  return ⟨← string (← field n "code"), ← string (← field n "message"),
    ← string (← field n "operator"),
    ⟨← string (← field p "file"), ← natural (← field p "startByte"), ← natural (← field p "endByte")⟩,
    ← natural (← field p "line"), ← natural (← field p "column")⟩

structure Input (k : Nat) where
  request : Request k
  warnings : List Frontend.Behavioral.Warning
  profile : String := IR.BehavioralStructural.richProfile

-- [impl->req~compiler-rich-core-explicit~1]
def decode (file text : String) : Except Diagnostic (Σ k, Input k) := do
  let n ← parse file text true
  version n "version" "clafer-explicit-core/1" "explicit.version"
  let profile ← string (← field n "profile")
  unless IR.BehavioralStructural.explicitProfile profile do
    throw { bad n "unsupported explicit profile" with code := "behavioral.profile", category := .unsupported }
  closed n ["version", "profile", "structure", "modifiers", "constraints", "assertions", "command", "warnings"]
  let ⟨k, v⟩ ← structureRead (← field n "structure")
  let ms ← array (fun n => (array modifier n).map Array.toList) (← field n "modifiers")
  if length : ms.size = k then
    let model : Properties.Model k (Expression.Atom k) (Expression.Collection k) := {
      structural := v, modifiers := ⟨ms, length⟩
      constraints := (← array (property v.core.structural (text.utf8ByteSize + 1)) (← field n "constraints")).toList
      assertions := (← array (property v.core.structural (text.utf8ByteSize + 1)) (← field n "assertions")).toList }
    let cmd ← field n "command"
    let command ← match ← string (← field cmd "kind") with
      | "run" =>
        closed cmd ["kind", "scenario"]
        pure (Properties.Command.run (← array (property v.core.structural (text.utf8ByteSize + 1))
          (← field cmd "scenario")).toList)
      | "check" => do
        closed cmd ["kind", "assertion"]
        let i ← natural (← field cmd "assertion")
        if h : i < model.assertions.length then pure (Properties.Command.check ⟨i, h⟩)
        else throw (bad cmd "assertion index is out of range")
      | _ => throw (bad cmd "unknown command")
    return ⟨k, ⟨⟨model, command⟩, (← array warning (← field n "warnings")).toList, profile⟩⟩
  else throw (bad n "each declaration requires one modifier list")

structure Product (k : Nat) where
  request : Request k
  bounds : Backend.Alloy.Behavioral.Full.Bounds
  fuel : Nat
  compiled : Backend.Alloy.Behavioral.Full.Compiled
  text : String
  core : Json
  warnings : List Frontend.Behavioral.Warning
  compiled_checked : Backend.Alloy.Behavioral.Full.compile request bounds fuel = .ok compiled

-- [impl->req~compiler-rich-core-explicit~1]
def compile (file text boundsFile boundsText : String) (objects bitwidth : Option Nat := none) :
    Except Diagnostic (Σ k, Product k) := do
  let ⟨k, input⟩ ← decode file text
  let r := input.request
  let selected ← BehavioralSource.selectedProfile boundsFile boundsText
  if selected != input.profile then
    throw { bad ⟨.null, boundsFile, "/profile"⟩ "explicit input and bounds profiles must match"
      with code := "behavioral.profile", category := .unsupported }
  let b ← BehavioralSource.bounds boundsFile boundsText
  let b := { b with objects := objects.getD b.objects, bitwidth := bitwidth.getD b.bitwidth }
  BehavioralSource.completeScopes boundsFile r.model.structural b
  let inspected ← BehavioralSource.inspectRequest r (text.utf8ByteSize + 1)
  let fuel := inspected.depth + 1
  let out ← MonadAttach.attach (Backend.Alloy.Behavioral.Full.compile r b fuel)
    |>.mapError (BehavioralSource.encodingDiagnostic boundsFile)
  let rendered ← Backend.Alloy.Temporal.Text.render out.val.module (BehavioralSource.names r.model.structural)
    |>.mapError fun _ => { code := "compiler.render", phase := "serialization", category := .operational, message := "generated temporal text failed checked reconstruction" : Diagnostic }
  return ⟨k, ⟨r, b, fuel, out.val, rendered.text, ← encode r (text.utf8ByteSize + 1) input.warnings input.profile, input.warnings, out.property⟩⟩

end ClaferCompiler.Driver.ExplicitCore
