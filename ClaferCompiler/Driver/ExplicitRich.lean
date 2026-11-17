module

public import ClaferCompiler.Driver.ExplicitCore

@[expose] public section
namespace ClaferCompiler.Driver.ExplicitRich
open Lean Decode Frontend.Behavioral IR.Behavioral
open Values

/-- Resolved operands accompany the preserved operation. A future rich consumer
can select an operation without recovering it from its expanded formula. -/
def typeJson (m : IR.Structural.Core k) : Ty k → Json
  | .objects d => toJson [toJson "objects", toJson (m.get d).id]
  | .integers => toJson [toJson "integers"] | .empty => toJson [toJson "empty"]
  | .mixed ds => toJson [toJson "mixed", toJson (ds.map fun d => (m.get d).id)]

def valueJson (m : IR.Structural.Core k) (fuel : Nat) {n : Nat} : Value k n → Except Diagnostic Json
  | .collection ty a => do return toJson [toJson "collection", typeJson m ty,
      (← (BehavioralSyntax.encode m fuel).collection a).json]
  | .integer a => do return toJson [toJson "integer", (← (BehavioralSyntax.encode m fuel).integer a).json]
  | .formula a => do return toJson [toJson "formula", (← (BehavioralSyntax.encode m fuel).formula a).json]
  | .chain a => do
      let pass := BehavioralSyntax.encode m fuel
      let links ← a.links.mapM fun link => do
        let guard ← link.guard.mapM fun f => (pass.formula f).map (·.json)
        return Json.mkObj [("source", (← pass.formula link.source).json),
          ("guard", guard.getD Json.null),
          ("arrow", toJson (match link.arrow with | .immediate => "-->" | .eventual => "-->>"))]
      return toJson [toJson "transition", toJson links, (← pass.formula a.target).json]

def spelling : Expr → List String
  | .name t => ["name", t.text] | .integer _ z => ["integer", toString z]
  | .parens .. => ["parens"] | .unary op .. => ["unary", op.text]
  | .binary op .. => ["binary", op.text]
  | .quantified q disjoint names .. => ["quantified", q.text,
      if disjoint.isSome then "disjoint" else "shared"] ++ names.map (·.text)
  | .letSet _ name .. => ["let", name.text]
  | .conditional .. => ["conditional"] | .transition arrow .. => ["transition", arrow.text]
  | .pattern kind _ _ scope _ _ _ => ["pattern", kind.text, (scope.map (·.text)).getD "suffix"]

-- [impl->req~compiler-rich-core-explicit~1]
/-- The existing certified resolver supplies every node's value. Binding and
navigation contexts follow that resolver; ignored empty-navigation tails are
marked explicitly instead of resolving names that the language never consults. -/
def expression (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (allocation : Nat) : Nat → {n : Nat} → Context k n → Option (Value k n) → Expr → Except Diagnostic Json :=
  Nat.rec (fun {_} _ _ e => .error (Diagnostic.ofSource (Expressions.failure doc e "behavioral.expression-budget")))
    (fun fuel next {_} context cursor e => do
      let synth := fun {n} (ctx : Context k n) cur a =>
        Expressions.synthAt doc v owner allocation ctx cur a |>.mapError Diagnostic.ofSource
      let result ← synth context cursor e
      let error := fun msg => Diagnostic.ofSource (Expressions.failure doc e msg)
      let children ← match e with
        | .name _ | .integer _ _ => pure []
        | .parens a _ => do pure [← next context cursor a]
        | .unary op a _ => do
          if op.text == "sum" || op.text == "product" then
            let some operands := Expressions.operandsAt (fuel + 1) a
              | throw (error "behavioral.expression-budget")
            operands.val.mapM (next context cursor)
          else pure [← next context cursor a]
        | .binary op a b _ => do
          if op.text == "." then
            match Expressions.emptyNavigationAt (fuel + 1) e with
            | some (.isTrue _) => pure [Json.mkObj [("ignored", toJson "literal-empty-navigation")]]
            | _ => do
              let left ← synth context cursor a
              pure [← next context cursor a, ← next context (some left) b]
          else pure [← next context cursor a, ← next context cursor b]
        | .quantified op _ names domain body _ => do
          let domainValue ← synth context cursor domain
          let heads ← Values.heads domainValue |>.mapError error
          let plan ← Binders.prepare context op names heads.1 |>.mapError Diagnostic.ofSource
          pure [← next context cursor domain, ← next plan.bodyContext none body]
        | .letSet _ binder domain body _ => do
          let domainValue ← synth context cursor domain
          let heads ← Values.heads domainValue |>.mapError error
          pure [← next context cursor domain, ← next (Expressions.push context binder heads.1) none body]
        | .conditional _ c a b _ => do
          pure [← next context cursor c, ← next context cursor a, ← next context cursor b]
        | .transition _ a guard b _ => do
          let guard ← guard.mapM (next context cursor)
          pure [← next context cursor a, guard.getD Json.null, ← next context cursor b]
        | .pattern _ a b _ c d _ => do
          let optional := fun x => (x.mapM (next context cursor)).map (·.getD Json.null)
          pure [← next context cursor a, ← optional b, ← optional c, ← optional d]
      return Json.mkObj [("operation", toJson (spelling e)),
        ("source", sourceSpanJson e.span), ("owner", toJson (v.core.structural.get owner).id),
        ("bindings", toJson (context.toList.map fun slot => slot.map (fun (name, ty) =>
          Json.mkObj [("name", toJson name.text), ("type", typeJson v.core.structural ty)]) |>.getD Json.null)),
        ("resolved", ← valueJson v.core.structural allocation result), ("children", toJson children)])

def clockName : Initializers.Clock → String
  | .instanceBirth => "instance-birth" | .parentBirth => "parent-birth" | .globalZero => "global-zero"

-- [impl->req~compiler-rich-core-explicit~1]
def encode (p : ParsedModel) (allocation : Nat) (legacy : Bool := false) : Except Diagnostic Json := do
  let e := p.elaborated
  let d := e.declarations
  let v := d.resolved.admitted
  let m := v.core.structural
  let properties ← (properties d).mapM fun prop => do
    return Json.mkObj [("kind", toJson (match prop.kind with | .constraint => "constraint" | .assertion => "assertion")),
      ("expression", ← expression p.source v prop.owner allocation allocation #v[] none prop.expression)]
  let headers ← e.headers.mapM fun prop => do
    if prop.kind == .transition then
      return Json.mkObj [("kind", toJson "transition"), ("declaration", toJson (m.get prop.declaration).id),
        ("expression", ← expression p.source v prop.owner allocation allocation #v[] none prop.expression)]
    else
      let some header := d.resolved.candidate.paths[prop.declaration].bind (headerAt d.expanded)
        | throw { code := "explicit.initializer-origin", phase := "serialization", message := "missing initializer origin" : Diagnostic }
      let some (op, rhs) := header.initializer
        | throw { code := "explicit.initializer-origin", phase := "serialization", message := "missing initializer syntax" : Diagnostic }
      let value ← Expressions.synthAt p.source v prop.owner allocation #v[] none rhs |>.mapError Diagnostic.ofSource
      let target ← Values.target v value |>.mapError fun msg => Diagnostic.ofSource (Expressions.failure p.source rhs msg)
      let heads ← Values.heads target |>.mapError fun msg => Diagnostic.ofSource (Expressions.failure p.source rhs msg)
      let clock ← classifyInitializer d prop header op heads.2 |>.mapError Diagnostic.ofSource
      return Json.mkObj [("kind", toJson "initializer"), ("operator", toJson op.text),
        ("declaration", toJson (m.get prop.declaration).id), ("rhsOwner", toJson (m.get prop.owner).id),
        ("clock", toJson (clock.val.map clockName |>.getD "every-live")),
        ("temporal", toJson p.source.temporal),
        ("rhs", ← expression p.source v prop.owner allocation allocation #v[] none rhs)]
  let enums ← p.source.elements.filterMap (fun elem => match elem with
    | .enumeration name literals _ => some (name, literals) | _ => none) |>.mapM fun (name, literals) => do
      let resolve := fun name => do
        let some row := m.declarations.toList.find? (fun row => row.name == name)
          | throw { code := "explicit.enum-origin", phase := "serialization", message := "missing enum origin" : Diagnostic }
        return Json.mkObj [("name", toJson name), ("id", toJson row.id)]
      return Json.mkObj [("family", ← resolve name.text), ("literals", toJson (← literals.mapM fun l => resolve l.text))]
  let core ← ExplicitCore.encode ⟨e.model, .run []⟩ allocation p.warnings legacy
  return Json.mkObj [("version", toJson (if legacy then "clafer-explicit-rich/1" else "clafer-explicit-rich/2")),
    ("profile", toJson IR.BehavioralStructural.richProfile),
    ("source", Json.mkObj [("file", toJson p.source.file), ("text", toJson p.source.source)]),
    ("enumerations", toJson enums), ("properties", toJson properties), ("headers", toJson headers),
    ("lowered", core), ("warnings", toJson (p.warnings.map BehavioralSource.warningJson))]

/-- Rich replay checks every resolved annotation and explicit clock against the
single source elaboration. It never trusts a stale edited lowering or metadata. -/
-- [impl->req~compiler-rich-core-explicit~1]
def decode (file text : String) : Except Diagnostic ParsedModel := do
  let n ← parse file text true
  let schema ← string (← field n "version")
  unless schema == "clafer-explicit-rich/1" || schema == "clafer-explicit-rich/2" do
    throw { bad n "unsupported explicit version" with code := "explicit.version", category := .unsupported }
  version n "profile" IR.BehavioralStructural.richProfile "behavioral.profile"
  closed n ["version", "profile", "source", "enumerations", "properties", "headers", "lowered", "warnings"]
  let origin ← field n "source"
  closed origin ["file", "text"]
  let source ← string (← field origin "text")
  let p ← parseAndElaborate IR.BehavioralStructural.richProfile (← string (← field origin "file")) source
    |>.mapError Diagnostic.ofSource
  let canonical ← encode p (BehavioralSource.budget source .model) (schema == "clafer-explicit-rich/1")
  unless canonical == n.value do
    throw (bad n "rich metadata or lowering differs from resolved source; re-export the edited source")
  return p

end ClaferCompiler.Driver.ExplicitRich
