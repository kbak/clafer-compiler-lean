module

public import ClaferCompiler.Frontend.Defaults

@[expose] public section
namespace ClaferCompiler.Frontend.Resolution
open IR.Structural

def errorAt (t : Token) (code message : String)
    (category : Category := .malformed) (related : Array SourceSpan := #[]) : Diagnostic :=
  { code, message, category, related, phase := "resolve", primary := t.span,
    line := t.line, column := t.column }

def startToken (doc : Document) : Token :=
  ⟨"", ⟨doc.file, 0, 0⟩, 1, 1, 1⟩

/-- Finite worklist traversal using library iteration; independent source coverage
is checked below, including calls on manually constructed documents. -/
def inventory (doc : Document) : Except Diagnostic (Array Path) := Id.run do
  let initial := doc.elements.zipIdx |>.map (fun (e, k) => ([k], e))
  let (pending, paths) := Nat.repeat (fun (pending, paths) =>
    match pending with
    | [] => ([], paths)
    | (path, e) :: rest => match e with
      | .constraint _ _ => (rest, paths)
      | .declaration _ es _ =>
        ((es.zipIdx.map (fun (e, k) => (path ++ [k], e))) ++ rest, paths.push path))
    (doc.source.utf8ByteSize + 1) (initial, (#[] : Array Path))
  if !pending.isEmpty then
    return .error (errorAt (startToken doc) "resolve.inventory" "source inventory bound exhausted")
  return .ok paths

def header (doc : Document) (path : Path) : Header :=
  (headerAt doc path).getD { name := startToken doc }

def pathId (paths : Array Path) (path : Path) : Option Nat :=
  ((List.range paths.size).find? (fun i => paths[i]? == some path)).map (· + 1)

/-- Name lookup computes all equally near matches, never selects an ambiguous first. -/
def lookupName (doc : Document) (paths : Array Path) (context : Path)
    (super : Bool) (name : Name) (integerId : Nat) : Except Diagnostic Nat := do
  if integerName name.text then
    if super then throw (errorAt name "resolve.primitive-super" "a primitive cannot be a superclass" .unsupported)
    return integerId
  if reserved name.text then
    throw (errorAt name "resolve.reserved-target" "reserved name is not a declaration target" .unsupported)
  let candidates := (List.range paths.size).filter (fun i =>
    let h := header doc paths[i]!
    h.name.text == name.text && (!super || (h.abstractToken.isSome && paths[i]!.length == 1)))
  let best := candidates.foldl (fun acc i => max acc (proximity context paths[i]!)) 0
  let selected := candidates.filter (fun i => proximity context paths[i]! == best)
  match selected with
  | [i] => return i + 1
  | [] => throw (errorAt name "resolve.missing-name" "no declaration matches this name")
  | _ => throw (errorAt name "resolve.ambiguous-name" "several declarations match this name"
      .malformed (selected.toArray.map (fun i => (header doc paths[i]!).name.span)))

def ranks (rows : Array (Declaration Nat)) (super : Bool) : Array Nat :=
  Nat.repeat (fun old => rows.map (fun d =>
    match (if super then d.super else d.parent) with
    | none => 0 | some p => old[p]?.getD 0 + 1)) rows.size (Array.replicate rows.size 0)

/-- Bounded iteration stops only at an exact fixed point. The equality below
also covers cycles and exhausted budgets; later admission keeps rejecting them. -/
def repeatStable {α : Type} [DecidableEq α] (step : α → α) : Nat → α → α
  := Nat.rec (motive := fun _ => α → α) id fun _ recur value =>
    let next := step value
    if next = value then value else recur next

private theorem repeat_fixed {α : Type} (step : α → α) (value : α)
    (fixed : step value = value) (k : Nat) : Nat.repeat step k value = value := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.repeat, ih, fixed]

private theorem repeat_apply {α : Type} (step : α → α) (k : Nat) (value : α) :
    Nat.repeat step k (step value) = step (Nat.repeat step k value) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.repeat, ih]

private theorem repeatStable_eq {α : Type} [DecidableEq α] (step : α → α) (k : Nat) (value : α) :
    repeatStable step k value = Nat.repeat step k value := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    change (if step value = value then value else repeatStable step k (step value)) = _
    split
    · rename_i h
      exact (repeat_fixed step value h (k + 1)).symm
    · rw [ih, repeat_apply]
      rfl

def realizationStep (rows : Array (Declaration Nat)) (old : Array Nat) : Array Nat :=
  rows.mapIdx (fun i d =>
    let fromParent := d.parent.map (fun p => old[p]?.getD 0 + 1) |>.getD 0
    rows.foldl (fun value child =>
      if child.super == some i then max value (old[child.id]?.getD 0 + 1) else value) fromParent)

def realizationRanks (rows : Array (Declaration Nat)) : Array Nat :=
  Nat.repeat (realizationStep rows) rows.size (Array.replicate rows.size 0)

def realizationRanksStable (rows : Array (Declaration Nat)) : Array Nat :=
  repeatStable (realizationStep rows) rows.size (Array.replicate rows.size 0)

@[csimp] theorem realizationRanks_eq_stable : realizationRanks = realizationRanksStable := by
  funext rows
  exact (repeatStable_eq _ _ _).symm

def prepare (doc : Document) : Except Diagnostic
    (Raw × Array (Option Path) × Array Group × Array Nat) := do
  let paths ← inventory doc
  for i in [:paths.size] do
    let h := header doc paths[i]!
    if reserved h.name.text then
      throw (errorAt h.name "resolve.reserved-name" "reserved names cannot declare user types" .unsupported)
    if h.abstractToken.isSome && paths[i]!.length != 1 then
      throw (errorAt h.name "resolve.nested-abstract" "explicit nested abstract types are unsupported" .unsupported)
    for j in [:i] do
      if paths[j]!.dropLast == paths[i]!.dropLast && (header doc paths[j]!).name.text == h.name.text then
        throw (errorAt h.name "resolve.duplicate-name" "duplicate declaration in the same scope"
          .malformed #[(header doc paths[j]!).name.span])
  let hasInteger := paths.any (fun p =>
    ((header doc p).reference.map (fun r => integerName r.2.text)).getD false) ||
    constraintHere doc.elements || paths.any (fun p => constraintHere ((childrenAt doc p).getD []))
  let integerId := paths.size + 1
  let mut rows : Array (Declaration Nat) := #[{
    id := 0, name := "Sing", origin := .syntheticRoot
    localBounds := ⟨1, .finite 1⟩ }]
  for path in paths do
    let h := header doc path
    let parent ← if path.length == 1 then
        pure (if h.abstractToken.isSome then none else some 0)
      else match pathId paths path.dropLast with
        | some p => pure (some p)
        | none => throw (errorAt h.name "resolve.parent" "missing containment parent")
    let super ← (h.super.orElse (fun _ => if h.useToken.isSome then some h.name else none)).mapM
      (fun name => lookupName doc paths path.dropLast true name integerId)
    let reference ← match h.reference with
      | none => pure Reference.basic
      | some (arrow, name) => do
        let target ← lookupName doc paths path false name integerId
        if arrow.text == "->" then pure (.set target) else pure (.bag target)
    rows := rows.push {
      id := rows.size, name := h.name.text, parent, super, reference
      isAbstract := h.abstractToken.isSome,
      source := (nodeAt doc path).map Element.span,
      authored := some ⟨h.abstractToken.isSome, h.cardinality.map cardBounds,
        h.group.map (fun g => (authoredGroup g).range)⟩ }
  if hasInteger then
    rows := rows.push {
      id := integerId, name := "int", origin := .integer
      parent := some 0, localBounds := {} }
  let parentRanks := ranks rows false
  let superRanks := ranks rows true
  for d in rows do
    if let some s := d.super then
      if superRanks[s]?.getD 0 >= superRanks[d.id]?.getD 0 then
        throw (errorAt (header doc (paths[d.id - 1]?.getD [])).name
          "resolve.inheritance-cycle" "inheritance cycle")
      if d.reference != .basic then
        throw (errorAt (header doc (paths[d.id - 1]?.getD [])).name
          "resolve.reference-inheritance" "reference inheritance is unsupported" .unsupported)
    if d.isAbstract && d.reference != .basic then
      throw (errorAt (header doc (paths[d.id - 1]?.getD [])).name
        "resolve.abstract-reference" "parentless abstract references are unsupported" .unsupported)
  let groups := Nat.repeat (fun old => rows.map (fun d =>
    let authored := paths[d.id - 1]?.bind (fun p => if d.id == 0 then none else (header doc p).group)
    (authored.map authoredGroup).getD
      ((d.super.bind (fun s => old[s]?)).getD (.bounds {})))) rows.size
      (Array.replicate rows.size (Group.bounds {}))
  let effective := Nat.repeat (fun old => rows.map (fun d =>
    d.isAbstract || ((d.parent.bind (fun p => old[p]?)).getD false))) rows.size (rows.map (·.isAbstract))
  rows := rows.map (fun d => { d with
    isAbstract := effective[d.id]?.getD false
    groupBounds := (groups[d.id]?.getD (.bounds {})).range
    localBounds := if d.origin == .integer then {} else (d.authored.bind (·.localBounds)).getD
      ((d.parent.bind (fun p => groups[p]?)).map Group.childDefault |>.getD ⟨1, .finite 1⟩) })
  let realized := realizationRanks rows
  for d in rows do
    if let some s := d.super then
      if realized[d.id]?.getD 0 >= realized[s]?.getD 0 then
        throw (errorAt (header doc (paths[d.id - 1]?.getD [])).name
          "resolve.realization-cycle" "recursive inherited realization is unsupported" .unsupported)
  let sourcePaths := #[none] ++ paths.map some ++ (if hasInteger then #[none] else #[])
  return (⟨rows, 0, parentRanks, superRanks, Array.replicate rows.size false⟩, sourcePaths, groups, realized)

/-- Reuse the accepted ID-to-Fin resolver without imposing M1's feature guard. -/
def bindCandidate (r : Raw) (paths : Array (Option Path)) (groups : Array Group)
    (realized : Array Nat) : Except IR.Structural.Diagnostic (Candidate r.declarations.size) := do
  let rows := r.declarations.toVector
  let root ← match lookup rows r.root with
    | some i => pure i | none => throw ⟨.malformed, "resolve.root", "", none⟩
  if hp : r.parentRanks.size = r.declarations.size then
    if hs : r.superRanks.size = r.declarations.size then
      if hu : r.unused.size = r.declarations.size then
        if hx : paths.size = r.declarations.size then
          if hg : groups.size = r.declarations.size then
            if hr : realized.size = r.declarations.size then
              let declarations ← (Vector.ofFn (fun i : Fin r.declarations.size => i)).mapM
                (resolveDeclaration rows)
              return ⟨⟨declarations, root⟩,
                ⟨⟨r.parentRanks, hp⟩, ⟨r.superRanks, hs⟩, ⟨r.unused, hu⟩⟩,
                ⟨paths, hx⟩, ⟨groups, hg⟩, ⟨realized, hr⟩⟩
  throw ⟨.malformed, "resolve.table-shape", "", none⟩

/-- Successful results carry a proof of independently stated source elaboration. -/
def elaborate (doc : Document) : Except Diagnostic (Elaborated doc) := do
  let (raw, paths, groups, realized) ← prepare doc
  let c ← (bindCandidate raw paths groups realized).mapError
    (fun e => errorAt (startToken doc) e.code "invalid resolved table")
  if h : Elaboration doc c then
    return ⟨_, c, h⟩
  else throw (errorAt (startToken doc) "resolve.correspondence" "declarative elaboration validation failed")

/-- Authored constraint lists retain their original owner and order, including
empty bodies. Inherited declarations share their original occurrences. -/
def constraints (doc : Document) (c : Candidate n) (i : Fin n) : List (List Expr × SourceSpan) :=
  let es := if i == c.core.root then doc.elements
    else (c.paths[i].bind (childrenAt doc)).getD []
  es.filterMap (fun e => match e with | .constraint bodies span => some (bodies, span) | _ => none)

/-- Explicit effective-only M1 projection. Parentless local slots have no parent
fiber and are normalized to unrestricted; authored records remain unchanged. -/
def m1Core (c : Candidate n) : Core n :=
  { c.core with declarations := c.core.declarations.map (fun d =>
      if d.parent.isNone && d.isAbstract then { d with localBounds := {} } else d) }

def toM1 (doc : Document) (e : Elaborated doc) : Except Diagnostic (Validated e.count) := do
  let c := e.candidate
  if (List.finRange e.count).any (fun i => !(constraints doc c i).isEmpty) then
    throw (errorAt (startToken doc) "resolve.m1-constraints" "M1 cannot discard source constraints" .unsupported)
  (validate (m1Core c) c.certificate).mapError
    (fun err => errorAt (startToken doc) err.code "resolved structure is outside M1" err.category)

end ClaferCompiler.Frontend.Resolution
