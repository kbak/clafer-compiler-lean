module

public import ClaferCompiler.Backend.Alloy.Behavioral.Compile
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral

-- [impl->req~compiler-trace-representation~1]
def encodeState (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) : Alloy.Instance where
  signatures := ids.ids.toList :: (Structural.order v).map (fun d =>
    ((List.finRange o).filter (fun x => IR.Behavioral.ancestor v.core ids.directType[x] d)).map
      (fun x => ids.ids[x]))
  fields := [(List.finRange o).flatMap (fun x => (ids.parent[x]).toList.map
      (fun p => [ids.ids[x], ids.ids[p]])),
    ((List.finRange o).filter (fun x => frame.live[x])).map
      (fun x => [ids.ids[ids.root], ids.ids[x]])] ++
    (List.finRange k).map (fun d => (frame.references.filter (fun r => r.1 == d)).map
      (fun r => [ids.ids[r.2.1], ids.ids[r.2.2]]))

def encode (v : IR.Structural.Layout k) (l : IR.Behavioral.Lasso k o steps) : Temporal.Lasso where
  inventory := l.identities.ids.toList
  frames := l.frames.toList.map (encodeState v l.identities)
  loop := l.loop.val
  nonempty := by simpa using (Nat.zero_lt_of_lt l.loop.isLt)
  loopValid := by simp [l.loop.isLt]

inductive DecodeError where
  | malformedFrame | missingRoot | malformedIdentities | changingIdentity | malformedRelation
  deriving DecidableEq, BEq

def labelIndex (objects : Vector Nat o) (label : Nat) : Except DecodeError (Fin o) :=
  match (List.finRange o).find? (fun i => objects[i] == label) with
  | some i => .ok i
  | none => .error .malformedRelation

def readPair (objects : Vector Nat o) (row : List Nat) :
    Except DecodeError (Fin o × Fin o) := do
  match row with
  | [x, y] => return (← labelIndex objects x, ← labelIndex objects y)
  | _ => throw .malformedRelation

def sameSet (a b : List Nat) : Bool := a.all b.contains && b.all a.contains
def sameRelation (a b : Alloy.Relation) : Bool := a.all b.contains && b.all a.contains

def typeCandidates (v : IR.Structural.Layout k) (state : Alloy.Instance) (label : Nat) : List (Fin k) :=
  (List.finRange k).filter fun d =>
    !(v.core.get d).isAbstract &&
    (state.signatures[Structural.signatureId v d]?.getD []).contains label &&
    (List.finRange k).all (fun e => e == d ||
      !(IR.Behavioral.ancestor v.core e d &&
        (state.signatures[Structural.signatureId v e]?.getD []).contains label))

def readType (v : IR.Structural.Layout k) (state : Alloy.Instance) (label : Nat) :
    Except DecodeError (Fin k) :=
  match typeCandidates v state label with
  | [d] => .ok d
  | _ => .error .malformedIdentities

def readParent (pairs : List (Fin o × Fin o)) (x : Fin o) :
    Except DecodeError (Option (Fin o)) :=
  match (pairs.filter fun p => p.1 == x).map Prod.snd with
  | [] => .ok none
  | [p] => .ok (some p)
  | _ => .error .malformedIdentities

def readIdentities (v : IR.Structural.Layout k) (state : Alloy.Instance)
    (objects : Vector Nat o) : Except DecodeError (IR.Behavioral.Identities k o) := do
  let roots := state.signatures[Structural.signatureId v v.core.root]?.getD []
  let r ← match roots with
    | [x] => labelIndex objects x
    | _ => .error .missingRoot
  let types ← (List.finRange o).mapM fun x => readType v state objects[x]
  let pairs ← (state.fields[0]?.getD []).mapM (readPair objects)
  let parents ← (List.finRange o).mapM (readParent pairs)
  -- Lengths are checked explicitly before building fixed-size runtime vectors.
  if ht : types.length = o then
    if hp : parents.length = o then
      return { ids := objects, root := r
               directType := Vector.ofFn (fun i => types[i.val]'(by have := i.isLt; omega))
               parent := Vector.ofFn (fun i => parents[i.val]'(by have := i.isLt; omega)) }
    else throw .malformedIdentities
  else throw .malformedIdentities

def readLive (ids : IR.Behavioral.Identities k o) (row : List Nat) : Except DecodeError Nat :=
  match row with
    | [r, x] => if r == ids.ids[ids.root] && ids.ids.toList.contains x then .ok x
        else .error DecodeError.malformedRelation
    | _ => .error DecodeError.malformedRelation

def readFrame (_v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (state : Alloy.Instance) : Except DecodeError (IR.Behavioral.Frame k o) := do
  let objects := ids.ids
  let memberships ← (state.fields[1]?.getD []).mapM (readLive ids)
  let references ← (List.finRange k).flatMapM fun d => do
    let pairs ← (state.fields[2 + d.val]?.getD []).mapM (readPair objects)
    return pairs.map fun (x, y) => (d, x, y)
  return ⟨Vector.ofFn (fun x => memberships.contains ids.ids[x]), references⟩

/-- Compare concrete finite tables extensionally, retaining all rows. -/
def sameTables [BEq α] (a b : List (List α)) : Bool :=
  a.length == b.length && (List.range a.length).all fun i =>
    let left := a[i]?.getD []
    let right := b[i]?.getD []
    left.all right.contains && right.all left.contains

def sameState (a b : Alloy.Instance) : Bool :=
  sameTables a.signatures b.signatures && sameTables a.fields b.fields

-- [impl->req~compiler-trace-representation~1]
/-- Decode through one pool and one static type/parent table for all frames.
Unused target inventory slots outside the object signature have no source role.
Multiplicity/temporal violations are retained for independent satisfaction. -/
def decodeRaw (v : IR.Structural.Layout k) (l : Temporal.Lasso) :
    Except DecodeError (Σ o steps, IR.Behavioral.Lasso k o steps) := do
  if !(l.frames.all (fun s => s.wellFormed (schema v).declarations)) then throw .malformedFrame
  let initial := l.frames[0]'(l.nonempty)
  let labels := initial.signatures[0]?.getD []
  let objects := Vector.ofFn (fun i : Fin labels.length => labels[i])
  let ids ← readIdentities v initial objects
  if !(l.frames.all fun s =>
      sameTables s.signatures initial.signatures &&
      sameRelation (s.fields[0]?.getD []) (initial.fields[0]?.getD [])) then
    throw .changingIdentity
  let frames ← l.frames.mapM (readFrame v ids)
  if hl : l.loop < frames.length then
    return ⟨labels.length, frames.length,
      ⟨ids, Vector.ofFn (fun i => frames[i]), ⟨l.loop, hl⟩⟩⟩
  else throw .malformedFrame

-- [impl->req~compiler-trace-representation~1]
/-- Reflection checks finite data only: no declaration, fact, temporal truth or
source validity is tested by re-encoding a decoded observation. -/
def roundTripChecks (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (target : Temporal.Lasso) : Bool :=
  target.frames.length == steps && target.loop == source.loop.val &&
  decide (∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y) &&
  decide (source.identities.directType[source.identities.root] = v.core.root) &&
  decide (∀ x : Fin o, source.identities.directType[x] = v.core.root → x = source.identities.root) &&
  (List.finRange steps).all fun i =>
    sameState (target.frames[i.val]?.getD ⟨[], [], []⟩)
      (encodeState v source.identities source.frames[i])

-- [impl->req~compiler-trace-representation~1]
def decode (v : IR.Structural.Layout k) (target : Temporal.Lasso) :
    Except DecodeError (Σ o steps, IR.Behavioral.Lasso k o steps) := do
  let decoded ← decodeRaw v target
  if roundTripChecks v decoded.2.2 target then return decoded
  else throw .malformedFrame

end ClaferCompiler.Backend.Alloy.Behavioral
