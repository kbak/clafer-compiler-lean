module

public import ClaferCompiler.Driver.BehavioralTrace
public import ClaferCompiler.SemanticsBridge.Behavioral.Verification

@[expose] public section
namespace ClaferCompiler.Tests.TemporalComparison
open Lean

def outcome : Clafer.Behavioral.Verification.Result → String
  | .satisfied => "satisfied" | .violated => "violated"
  | .malformed => "malformed" | .unsupported => "unsupported"

-- [utest->req~compiler-temporal-comparison~1]
-- [utest->req~compiler-temporal-decode~1]
def evaluate (doc : Driver.Behavioral.Input k) (l : IR.Behavioral.Lasso k o (last + 1)) : Json := Id.run do
  let v := doc.admitted
  let model := SemanticsBridge.Structural.interpret v.document.core
  let L := SemanticsBridge.Behavioral.Verification.sourceLasso l
  let structural := Clafer.Behavioral.Verification.checkAt model
    (SemanticsBridge.Structural.certificate v.document.certificate) L
    (some (Clafer.Behavioral.FiniteAdapter.sets model L)) .truth (.closed l.identities.root) 0
  let values := v.document.attachments.attach.map fun a =>
    match h : a.val.body with
    | .formula f => (a.val.id, SemanticsBridge.Behavioral.Verification.attached
        v.document.core l (Backend.Alloy.Behavioral.owner v.structural.toLayout a.val)
        f doc.fuel (doc.enough a.val a.property f h))
    | .unsupported _ => (a.val.id, false)
  let status := if structural == .satisfied && !(values.all Prod.snd) then "violated" else outcome structural
  return Json.mkObj [("version", toJson "clafer-behavioral-check/1"),
    ("status", toJson status), ("structural", toJson (outcome structural)),
    ("attachments", toJson (values.map fun (id, ok) => Json.mkObj [("id", toJson id), ("satisfied", toJson ok)])),
    ("trace", Driver.BehavioralTrace.json v.document.core l)]

-- [utest->req~compiler-behavioral-cli~1]
def run (args : List String) : IO Unit := do
  let [inputPath, tracePath] := args | throw (IO.userError "expected IR and Analyzer trace")
  let input ← IO.FS.readFile inputPath
  let text ← IO.FS.readFile tracePath
  let result : Except Driver.Diagnostic Json := do
    let ⟨_, doc⟩ ← Driver.Behavioral.document "input.json" input
    let ⟨_, steps, l⟩ ← Driver.BehavioralTrace.decode doc.admitted.structural.toLayout "trace.json" text
    match steps, l with
    | 0, l => False.elim (Nat.not_lt_zero _ l.loop.isLt)
    | _ + 1, l => return evaluate doc l
  IO.println (match result with
    | .ok value => value
    | .error d => Json.mkObj [("status", toJson (if d.category.exitCode == 3 then "unsupported" else "malformed")),
        ("diagnostic", d.json)]).compress

end ClaferCompiler.Tests.TemporalComparison
