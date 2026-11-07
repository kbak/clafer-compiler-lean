module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Structure
public import ClaferCompiler.Backend.Alloy.Behavioral.Representation
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full
open IR.BehavioralStructural

-- [impl->req~compiler-trace-assurance~1]
/-- Finite nonprimitive observations share the original occurrence inventory.
The scalar table assigns values to those occurrences; integer values are never
encoded as object labels. Unused scalar rows carry no source reference claim. -/
structure ObservedLasso (k o steps : Nat) where
  objects : IR.Behavioral.Lasso k o steps
  values : Vector (Vector Int o) steps

def ObservedLasso.valuesAt (l : ObservedLasso k o steps) (t : Nat) : Vector Int o :=
  l.values[l.objects.index t]

-- [impl->req~compiler-trace-assurance~1]
def encodeState (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (values : Vector Int o) : Alloy.Instance where
  signatures := ids.ids.toList :: (List.finRange k).map (fun d =>
    ((List.finRange o).filter (fun x => ids.directType[x] == d)).map (fun x => ids.ids[x]))
  fields := [(List.finRange o).flatMap (fun x => (ids.parent[x]).toList.map
      (fun p => [ids.ids[x], ids.ids[p]])),
    ((List.finRange o).filter (fun x => frame.live[x])).map
      (fun x => [ids.ids[ids.root], ids.ids[x]])] ++
    (List.finRange k).map (fun d => (frame.references.filter (fun r => r.1 == d)).map
      (fun r => [ids.ids[r.2.1], ids.ids[r.2.2]]))
  values := [(List.finRange o).map (fun x => (ids.ids[x], values[x]))]

def encode (l : ObservedLasso k o steps) : Temporal.Lasso where
  inventory := l.objects.identities.ids.toList
  frames := (List.finRange steps).map fun i =>
    encodeState l.objects.identities l.objects.frames[i] l.values[i]
  loop := l.objects.loop.val
  nonempty := by simp only [List.length_map, List.length_finRange]; exact Nat.zero_lt_of_lt l.objects.loop.isLt
  loopValid := by simp only [List.length_map, List.length_finRange]; exact l.objects.loop.isLt

def readType (state : Alloy.Instance) (label : Nat) : Except DecodeError (Fin k) :=
  match (List.finRange k).filter
      (fun d => (state.signatures[signatureId d]?.getD []).contains label) with
  | [d] => .ok d
  | _ => .error .malformedIdentities

def readIdentities (v : Validated k) (state : Alloy.Instance)
    (objects : Vector Nat o) : Except DecodeError (IR.Behavioral.Identities k o) := do
  let roots := state.signatures[signatureId v.core.structural.root]?.getD []
  let r ← match roots with
    | [x] => labelIndex objects x
    | _ => .error .missingRoot
  let types ← (List.finRange o).mapM fun x => readType state objects[x]
  let pairs ← (state.fields[0]?.getD []).mapM (readPair objects)
  let parents ← (List.finRange o).mapM (readParent pairs)
  if ht : types.length = o then
    if hp : parents.length = o then
      return { ids := objects, root := r
               directType := Vector.ofFn (fun i => types[i.val]'(by have := i.isLt; omega))
               parent := Vector.ofFn (fun i => parents[i.val]'(by have := i.isLt; omega)) }
    else throw .malformedIdentities
  else throw .malformedIdentities

def readFrame (ids : IR.Behavioral.Identities k o) (state : Alloy.Instance) :
    Except DecodeError (IR.Behavioral.Frame k o) := do
  let memberships ← (state.fields[1]?.getD []).mapM (readLive ids)
  let references ← (List.finRange k).flatMapM fun d => do
    let pairs ← (state.fields[2 + d.val]?.getD []).mapM (readPair ids.ids)
    return pairs.map fun (x, y) => (d, x, y)
  return ⟨Vector.ofFn (fun x => memberships.contains ids.ids[x]), references⟩

def readValues (ids : IR.Behavioral.Identities k o) (state : Alloy.Instance) :
    Except DecodeError (Vector Int o) := do
  let values ← (List.finRange o).mapM fun x =>
    match ((state.values[0]?.getD []).filter (fun row => row.1 == ids.ids[x])).map
        Prod.snd |>.eraseDups with
    | [z] => pure z
    | _ => throw DecodeError.malformedRelation
  if h : values.length = o then
    return Vector.ofFn fun i => values[i.val]'(by have := i.isLt; omega)
  else throw .malformedRelation

/-- Only signature zero has a scalar field. Other `values` slots have no
denotation in this schema and do not acquire a fictitious source observation. -/
def sameState (a b : Alloy.Instance) : Bool :=
  sameTables a.signatures b.signatures && sameTables a.fields b.fields &&
    sameTables [a.values[0]?.getD []] [b.values[0]?.getD []]

-- [impl->req~compiler-trace-assurance~1]
def decodeRaw (v : Validated k) (l : Temporal.Lasso) :
    Except DecodeError (Σ o steps, ObservedLasso k o steps) := do
  if !(l.frames.all (fun s => s.wellFormed (schema v).declarations)) then throw .malformedFrame
  let initial := l.frames[0]'(l.nonempty)
  let labels := initial.signatures[0]?.getD []
  let objects := Vector.ofFn (fun i : Fin labels.length => labels[i])
  let ids ← readIdentities v initial objects
  if !(l.frames.all fun s =>
      sameTables s.signatures initial.signatures &&
      sameRelation (s.fields[0]?.getD []) (initial.fields[0]?.getD [])) then
    throw .changingIdentity
  let frames ← l.frames.mapM (readFrame ids)
  let values ← l.frames.mapM (readValues ids)
  if hl : l.loop < frames.length then
    if hv : values.length = frames.length then
      return ⟨labels.length, frames.length,
        ⟨⟨ids, Vector.ofFn (fun i => frames[i]), ⟨l.loop, hl⟩⟩,
          Vector.ofFn (fun i => values[i.val]'(by have := i.isLt; omega))⟩⟩
    else throw .malformedFrame
  else throw .malformedFrame

def roundTripChecks (v : Validated k) (source : ObservedLasso k o steps) (target : Temporal.Lasso) : Bool :=
  target.frames.length == steps && target.loop == source.objects.loop.val &&
  decide (∀ x y : Fin o,
    source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y) &&
  decide (source.objects.identities.directType[source.objects.identities.root] = v.core.structural.root) &&
  decide (∀ x : Fin o, source.objects.identities.directType[x] = v.core.structural.root →
    x = source.objects.identities.root) &&
  (List.finRange steps).all fun i =>
    sameState (target.frames[i.val]?.getD ⟨[], [], []⟩)
      (encodeState source.objects.identities source.objects.frames[i] source.values[i])

-- [impl->req~compiler-trace-assurance~1]
/-- Checks finite table reflection and scalar values, independently of source
structure, source formulas and target facts. -/
def decode (v : Validated k) (target : Temporal.Lasso) :
    Except DecodeError (Σ o steps, ObservedLasso k o steps) := do
  let decoded ← decodeRaw v target
  if roundTripChecks v decoded.2.2 target then return decoded
  else throw .malformedFrame

end ClaferCompiler.Backend.Alloy.Behavioral.Full
