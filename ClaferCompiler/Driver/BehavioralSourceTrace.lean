module

public import ClaferCompiler.Driver.BehavioralSource
public import ClaferCompiler.Driver.BehavioralTrace
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Representation

@[expose] public section
namespace ClaferCompiler.Driver.BehavioralSourceTrace
open Lean Decode Backend.Alloy

-- [impl->req~compiler-behavioral-integration~1]
def decode (v : IR.BehavioralStructural.Validated k) (file text : String) :
    Except Diagnostic (Σ o steps, Behavioral.Full.ObservedLasso k o steps) := do
  let n ← parse file text
  let t ← BehavioralTrace.targetSchema (Behavioral.Full.schema v) n
  Behavioral.Full.decode v t |>.mapError fun _ =>
    BehavioralTrace.badTrace n "malformed scalar trace or changing static identities"

/-- Scalar observations belong to fixed reference heads, including unused rows;
ordinary target identities are never conflated with integer values. -/
def json (m : IR.Structural.Core k) (l : Behavioral.Full.ObservedLasso k o steps) : Json :=
  let ids := l.objects.identities
  Json.mkObj [
    ("version", toJson "clafer-behavioral-trace/2"),
    ("profile", toJson IR.BehavioralStructural.profile),
    ("root", toJson ids.ids[ids.root]), ("length", toJson steps),
    ("loop", toJson l.objects.loop.val),
    ("identities", toJson ((List.finRange o).map fun x => Json.mkObj [
      ("id", toJson ids.ids[x]), ("type", toJson (m.get ids.directType[x]).id),
      ("parent", toJson (ids.parent[x].map fun p => ids.ids[p]))])),
    ("frames", toJson ((List.finRange steps).map fun i =>
      let frame := l.objects.frames[i]
      Json.mkObj [
        ("live", toJson (((List.finRange o).filter (frame.live[·])).map (ids.ids[·]))),
        ("references", toJson (frame.references.map fun (d, x, y) =>
          [(m.get d).id, ids.ids[x], ids.ids[y]])),
        ("values", toJson ((List.finRange o).map fun x =>
          Json.arr #[toJson ids.ids[x], toJson l.values[i][x]]))]))]

end ClaferCompiler.Driver.BehavioralSourceTrace
