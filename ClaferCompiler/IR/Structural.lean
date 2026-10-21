module

public import Std

@[expose] public section
namespace ClaferCompiler.IR.Structural

/-- IDs are input identities, never names or array positions. -/
abbrev DeclId := Nat

inductive Upper where
  | finite (value : Nat) | unbounded
  deriving DecidableEq, Repr

structure Bounds where
  lower : Nat := 0
  upper : Upper := .unbounded
  deriving DecidableEq, Repr

def Bounds.Valid (b : Bounds) : Prop :=
  match b.upper with | .finite n => b.lower ≤ n | .unbounded => True

instance (b : Bounds) : Decidable b.Valid := by
  unfold Bounds.Valid
  cases b.upper <;> infer_instance

inductive Origin where
  | syntheticRoot | user | integer | string | boolean
  deriving DecidableEq, Repr

inductive Reference (α : Type) where
  | basic | set (target : α) | bag (target : α)
  deriving DecidableEq, Repr

def Reference.target : Reference α → Option α
  | .basic => none | .set t | .bag t => some t

structure SourceSpan where
  file : String
  startByte : Nat
  endByte : Nat
  deriving DecidableEq, Repr

/-- Optional authored data is metadata, not a defaulting or elaboration claim. -/
structure Authored where
  isAbstract : Bool
  localBounds : Option Bounds
  groupBounds : Option Bounds
  deriving DecidableEq, Repr

structure Declaration (α : Type) where
  id : DeclId
  name : String
  origin : Origin := .user
  parent : Option α := none
  super : Option α := none
  reference : Reference α := .basic
  isAbstract : Bool := false
  localBounds : Bounds := {}
  groupBounds : Bounds := {}
  source : Option SourceSpan := none
  authored : Option Authored := none
  deriving DecidableEq, Repr

/-- Only these auxiliary fields certify acyclicity and unused abstract chains.
They are checked input data; they do not assert candidate satisfaction. -/
structure Certificate (n : Nat) where
  parentRank : Vector Nat n
  superRank : Vector Nat n
  unused : Vector Bool n
  deriving DecidableEq, Repr

structure Core (n : Nat) where
  declarations : Vector (Declaration (Fin n)) n
  root : Fin n
  deriving DecidableEq, Repr

def Core.get (m : Core n) (d : Fin n) := m.declarations[d]

/-- Finite decidable guards, linked to upstream predicates by the proof bridge. -/
def coreChecks (m : Core n) (k : Certificate n) : Prop :=
  (∀ d e, (m.get d).id = (m.get e).id → d = e) ∧
  (∀ d, (m.get d).origin = .syntheticRoot ↔ d = m.root) ∧
  ((m.get m.root).parent = none ∧ (m.get m.root).reference = .basic ∧
    (m.get m.root).super = none ∧ (m.get m.root).isAbstract = false) ∧
  (∀ d p, (m.get d).parent = some p → k.parentRank[p] < k.parentRank[d]) ∧
  (∀ d p, (m.get d).super = some p → k.superRank[p] < k.superRank[d]) ∧
  (∀ d, (m.get d).localBounds.Valid ∧ (m.get d).groupBounds.Valid) ∧
  (∀ d, (m.get d).parent = none → d ≠ m.root → (m.get d).isAbstract = true)

def supportChecks (m : Core n) (k : Certificate n) : Prop :=
  (∀ d, (m.get d).origin = .syntheticRoot ∨ (m.get d).origin = .user) ∧
  (∀ d, (m.get d).isAbstract = true →
    (m.get d).parent = none ∧ (m.get d).reference = .basic ∧
    (∀ c, (m.get c).parent ≠ some d) ∧ (m.get d).groupBounds = {} ∧
    ((m.get d).localBounds = {} ∨
      ((m.get d).localBounds = ⟨0, .finite 0⟩ ∧ k.unused[d] = true))) ∧
  (∀ d s, (m.get d).super = some s →
    (m.get s).isAbstract = true ∧ (m.get d).reference = .basic) ∧
  (∀ d t, (m.get d).reference.target = some t → (m.get t).origin = .user) ∧
  (∀ d, 0 < (m.get d).groupBounds.lower → ∃ c, (m.get c).parent = some d) ∧
  (∀ d, k.unused[d] = true → (m.get d).isAbstract = true) ∧
  (∀ d s, (m.get d).super = some s → k.unused[s] = true → k.unused[d] = true)

instance (m : Core n) (k : Certificate n) : Decidable (coreChecks m k) := by
  unfold coreChecks
  infer_instance

instance (m : Core n) (k : Certificate n) : Decidable (supportChecks m k) := by
  unfold supportChecks
  infer_instance

inductive Category where
  | malformed | unsupported
  deriving DecidableEq, Repr

structure Diagnostic where
  category : Category
  code : String
  pointer : String := ""
  declaration : Option DeclId := none
  deriving DecidableEq, Repr

structure Validated (n : Nat) where
  core : Core n
  certificate : Certificate n
  coreChecked : coreChecks core certificate
  supportChecked : supportChecks core certificate

/-- Checked allocation shape shared by the M1 and inherited backends.
It carries no M1 support assertion and is not an admission profile. -/
structure Layout (n : Nat) where
  core : Core n
  certificate : Certificate n
  coreChecked : coreChecks core certificate
  rootNotSuper : ∀ d, (core.get d).super ≠ some core.root

def Validated.toLayout (v : Validated n) : Layout n where
  core := v.core
  certificate := v.certificate
  coreChecked := v.coreChecked
  rootNotSuper := by
    intro d hd
    have ha := (v.supportChecked.2.2.1 d v.core.root hd).1
    have hr := v.coreChecked.2.2.1.2.2.2
    simp [hr] at ha

instance : CoeOut (Validated n) (Layout n) := ⟨Validated.toLayout⟩

/-- Error priority is core before support; success retains the exact input table. -/
def validate (m : Core n) (k : Certificate n) : Except Diagnostic (Validated n) :=
  if hc : coreChecks m k then
    if hs : supportChecks m k then .ok ⟨m, k, hc, hs⟩
    else .error ⟨.unsupported, "ir.unsupported-or-invalid-certificate", "", none⟩
  else .error ⟨.malformed, "ir.invalid-core-or-ranks", "", none⟩

/-- Declaration lookup is finite and deterministic. Duplicate IDs are separately rejected. -/
def lookup (rows : Vector (Declaration α) n) (id : DeclId) : Option (Fin n) :=
  (List.finRange n).find? (fun i => rows[i].id == id)

/-- Distinct reference head identities survive even at equal owner/target endpoints.
These are representation data only; candidate satisfaction/decoding belongs to #12. -/
structure ReferenceOccurrence where
  declaration : DeclId
  head : Nat
  owner : Nat
  target : Nat
  deriving DecidableEq, Repr

structure Raw where
  declarations : Array (Declaration DeclId)
  root : DeclId
  parentRanks : Array Nat
  superRanks : Array Nat
  unused : Array Bool
  deriving DecidableEq, Repr

def Reference.mapIds (f : α → β) : Reference α → Reference β
  | .basic => .basic | .set t => .set (f t) | .bag t => .bag (f t)

def Declaration.withEdges (d : Declaration α) (parent super : Option β)
    (reference : Reference β) : Declaration β where
  id := d.id
  name := d.name
  origin := d.origin
  parent := parent
  super := super
  reference := reference
  isAbstract := d.isAbstract
  localBounds := d.localBounds
  groupBounds := d.groupBounds
  source := d.source
  authored := d.authored

def Declaration.mapIds (d : Declaration α) (f : α → β) : Declaration β :=
  d.withEdges (d.parent.map f) (d.super.map f) (d.reference.mapIds f)

def resolveId (rows : Vector (Declaration DeclId) n) (index : Fin n) (id : DeclId) :
    Except Diagnostic (Fin n) :=
  match lookup rows id with
  | some i => .ok i
  | none => .error ⟨.malformed, "ir.dangling-id", "/declarations/" ++ toString index.val,
      some rows[index].id⟩

def resolveReference (rows : Vector (Declaration DeclId) n) (index : Fin n) :
    Reference DeclId → Except Diagnostic (Reference (Fin n))
  | .basic => .ok .basic
  | .set t => Reference.set <$> resolveId rows index t
  | .bag t => Reference.bag <$> resolveId rows index t

/-- Resolve by IDs, preserving order, names, provenance and every semantic field. -/
def resolveDeclaration (rows : Vector (Declaration DeclId) n) (index : Fin n) :
    Except Diagnostic (Declaration (Fin n)) := do
  let d := rows[index]
  let parent ← d.parent.mapM (resolveId rows index)
  let super ← d.super.mapM (resolveId rows index)
  let reference ← resolveReference rows index d.reference
  return d.withEdges parent super reference

/-- Native input boundary; no source parsing, defaulting, solver, or Haskell dependency. -/
def resolveRaw (r : Raw) :
    Except Diagnostic (Core r.declarations.size × Certificate r.declarations.size) := do
  let rows := r.declarations.toVector
  if !(r.declarations.toList.map (·.id)).Nodup then
    throw ⟨.malformed, "ir.duplicate-id", "/declarations", none⟩
  for d in r.declarations do
    if let some s := d.source then
      if s.endByte < s.startByte then
        throw ⟨.malformed, "ir.invalid-span", "/declarations", some d.id⟩
  let root ← match lookup rows r.root with
    | some i => pure i
    | none => throw ⟨.malformed, "ir.missing-root", "/root", some r.root⟩
  if hp : r.parentRanks.size = r.declarations.size then
    if hs : r.superRanks.size = r.declarations.size then
      if hu : r.unused.size = r.declarations.size then
        let declarations ← (Vector.ofFn (fun i : Fin r.declarations.size => i)).mapM
          (resolveDeclaration rows)
        return (⟨declarations, root⟩,
          ⟨⟨r.parentRanks, hp⟩, ⟨r.superRanks, hs⟩, ⟨r.unused, hu⟩⟩)
      else throw ⟨.malformed, "ir.certificate-length", "/unused", none⟩
    else throw ⟨.malformed, "ir.certificate-length", "/superRanks", none⟩
  else throw ⟨.malformed, "ir.certificate-length", "/parentRanks", none⟩

/-- The existing M1 entry point retains both core and support checks. -/
def validateRaw (r : Raw) : Except Diagnostic (Validated r.declarations.size) := do
  let (m, k) ← resolveRaw r
  validate m k

/-- Version/profile selection is explicit; this is not an input-format detector. -/
def validateDocument (version profile : String) (r : Raw) :
    Except Diagnostic (Validated r.declarations.size) :=
  if version != "clafer-ir/1" then
    .error ⟨.unsupported, "ir.version", "/version", none⟩
  else if profile != "m1-effective" then
    .error ⟨.unsupported, "ir.profile", "/profile", none⟩
  else validateRaw r

end ClaferCompiler.IR.Structural
