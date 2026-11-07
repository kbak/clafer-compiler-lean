module

public import ClaferCompiler.Driver.Behavioral

@[expose] public section
namespace ClaferCompiler.Driver.BehavioralTrace
open Lean Decode
namespace B
abbrev Layout := IR.Structural.Layout
end B
open Backend.Alloy

/-- A decoder diagnostic concerns representation, never temporal satisfaction. -/
def badTrace (n : Node) (message : String) : Diagnostic :=
  { bad n message with code := "behavioral.trace", phase := "decode-trace" }

def unique [BEq α] (n : Node) (xs : List α) : Except Diagnostic Unit := do
  if xs.eraseDups.length != xs.length then throw (badTrace n "duplicate identity or tuple")

def label (labels : List String) (n : Node) : Except Diagnostic Nat := do
  let value ← string n
  let some i := labels.idxOf? value | throw (badTrace n "unknown atom")
  return i

def rows (labels : List String) (arity : Nat) (n : Node) : Except Diagnostic (List (List Nat)) := do
  let xs ← array (fun row => do
    let values ← array (label labels) row
    if values.size != arity then throw (badTrace row "invalid tuple arity")
    return values.toList) n
  unique n xs.toList
  return xs.toList

-- [impl->req~compiler-temporal-decode~1]
def target (v : IR.Structural.Layout k) (n : Node) : Except Diagnostic Temporal.Lasso := do
  closed n ["length", "loop", "inventory", "frames", "signatures", "fields"]
  let length ← natural (← field n "length")
  let loop ← natural (← field n "loop")
  let atomsNode ← field n "inventory"
  let atoms ← array string atomsNode
  unique atomsNode atoms.toList
  let labels := atoms.toList.mergeSort (· ≤ ·)
  let schema := Backend.Alloy.Behavioral.schema v
  let sigs := schema.declarations.signatures.zipIdx
  let fields := schema.declarations.fields.zipIdx
  let sigNames := sigs.map fun (_, i) => Behavioral.signatureName i
  let fieldNames := fields.map fun (f, i) => Behavioral.fieldName f.owner i
  let sigMeta ← field n "signatures"
  let fieldMeta ← field n "fields"
  closed sigMeta sigNames
  closed fieldMeta fieldNames
  for (s, i) in sigs do
    let entry ← field sigMeta (Behavioral.signatureName i)
    closed entry ["mutable", "parent", "abstract"]
    if (← boolean (← field entry "mutable")) != schema.mutableSignatures[i]?.getD false ||
        (← boolean (← field entry "abstract")) != s.isAbstract ||
        (← string (← field entry "parent")) != (s.parent.map Behavioral.signatureName |>.getD "univ") then
      throw (badTrace entry "signature metadata differs from the compiled schema")
  for (f, i) in fields do
    let entry ← field fieldMeta (Behavioral.fieldName f.owner i)
    closed entry ["mutable", "arity"]
    if (← boolean (← field entry "mutable")) != schema.mutableFields[i]?.getD false ||
        (← natural (← field entry "arity")) != 2 then
      throw (badTrace entry "field metadata differs from the compiled schema")
  let frames ← array (fun frame => do
    closed frame ["signatures", "fields"]
    let sn ← field frame "signatures"
    let fn ← field frame "fields"
    closed sn sigNames
    closed fn fieldNames
    let signatures ← sigNames.mapM fun name => do
      let rs ← rows labels 1 (← field sn name)
      return rs.flatten
    let relations ← fieldNames.mapM fun name => do rows labels 2 (← field fn name)
    if signatures.head? != some (List.range labels.length) then
      -- The inventory is exactly the object pool, independent of tuple order.
      if !(Backend.Alloy.Behavioral.sameSet (signatures.headD []) (List.range labels.length)) then
        throw (badTrace sn "inventory differs from the shared object pool")
    return { signatures, fields := relations : Backend.Alloy.Instance }) (← field n "frames")
  if h : frames.size = length ∧ 0 < length ∧ loop < length then
    return { inventory := List.range labels.length, frames := frames.toList, loop
             nonempty := by simpa using h.1 ▸ h.2.1
             loopValid := by simpa using h.1 ▸ h.2.2 }
  else throw (badTrace n "empty, truncated or invalid-loop trace")

-- [impl->req~compiler-temporal-decode~1]
def decode (v : IR.Structural.Layout k) (file text : String) :
    Except Diagnostic (Σ o steps, IR.Behavioral.Lasso k o steps) := do
  let n ← parse file text
  let t ← target v n
  Backend.Alloy.Behavioral.decode v t |>.mapError fun _ =>
    badTrace n "malformed trace tables or changing static identities"

def json (m : IR.Structural.Core k) (l : IR.Behavioral.Lasso k o steps) : Json :=
  Json.mkObj [
    ("version", toJson "clafer-behavioral-trace/1"), ("profile", toJson "behavioral-core/1"),
    ("root", toJson l.identities.ids[l.identities.root]), ("length", toJson steps),
    ("loop", toJson l.loop.val), ("integerObservations", toJson ([] : List Nat)),
    ("identities", toJson ((List.finRange o).map fun x => Json.mkObj [
      ("id", toJson l.identities.ids[x]),
      ("type", toJson (m.get l.identities.directType[x]).id),
      ("parent", toJson (l.identities.parent[x].map fun p => l.identities.ids[p]))])),
    ("frames", toJson (l.frames.toList.map fun frame => Json.mkObj [
      ("live", toJson (((List.finRange o).filter (frame.live[·])).map (l.identities.ids[·]))),
      ("references", toJson (frame.references.map fun (d, x, y) =>
        [ (m.get d).id, l.identities.ids[x], l.identities.ids[y] ]))]))]

end ClaferCompiler.Driver.BehavioralTrace
