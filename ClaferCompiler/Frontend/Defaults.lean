module

public import ClaferCompiler.Frontend.Surface

@[expose] public section
namespace ClaferCompiler.Frontend.Resolution
open IR.Structural

/-- Executable provenance; interpreted directly into upstream GroupCard. -/
inductive Group where
  | bounds (range : Bounds) | xor | or | mux | opt
  deriving DecidableEq, Repr

def Group.range : Group → Bounds
  | .bounds r => r | .xor => ⟨1, .finite 1⟩ | .or => ⟨1, .unbounded⟩
  | .mux => ⟨0, .finite 1⟩ | .opt => {}

def Group.childDefault : Group → Bounds
  | .bounds _ => ⟨1, .finite 1⟩ | _ => ⟨0, .finite 1⟩

def cardBounds (c : Cardinality) : Bounds :=
  ⟨c.lower, c.upper.map Upper.finite |>.getD .unbounded⟩

def authoredGroup (c : Cardinality) : Group :=
  match c.tokens[0]?.map (·.text) with
  | some "xor" => .xor | some "or" => .or | some "mux" => .mux
  | some "opt" => .opt | _ => .bounds (cardBounds c)

/-- Source paths index *elements*, including constraint positions. -/
abbrev Path := List Nat

def children : Element → List Element
  | .declaration _ es _ => es | .constraint _ _ => []

def childrenAt (doc : Document) (path : Path) : Option (List Element) :=
  path.foldl (fun es k => do pure (children (← (← es)[k]?))) (some doc.elements)

def nodeAt (doc : Document) (path : Path) : Option Element := do
  let k ← path.getLast?
  (← childrenAt doc path.dropLast)[k]?

def headerAt (doc : Document) (path : Path) : Option Header := do
  match ← nodeAt doc path with
  | .declaration h _ _ => some h | _ => none

/-- Lexical proximity of a declaration to a type-name occurrence. Zero is global.
An enclosing body's declarations take priority over more distant/global names. -/
def proximity (context target : Path) : Nat :=
  if target.dropLast.isPrefixOf context then target.length else 0

structure Candidate (n : Nat) where
  core : Core n
  certificate : Certificate n
  paths : Vector (Option Path) n
  groups : Vector Group n
  realizationRank : Vector Nat n

def Candidate.header (c : Candidate n) (doc : Document) (i : Fin n) : Option Header :=
  c.paths[i].bind (headerAt doc)

def reserved (s : String) : Bool :=
  ["Sing", "root", "this", "parent", "dref", "int", "integer", "string", "real",
    "double", "bool", "boolean"].contains s

def integerName (s : String) : Bool := s == "int" || s == "integer"

/-- Super lookup selects explicit parentless types. References use lexical scopes
and then unique global names. Primitive aliases have a separate origin rule. -/
def eligible (doc : Document) (c : Candidate n) (super : Bool)
    (name : String) (j : Fin n) : Prop :=
  match c.header doc j with
  | some h => h.name.text = name ∧
    (super = true → h.abstractToken.isSome = true ∧
      (c.paths[j].getD []).length = 1)
  | none => False

instance (doc : Document) (c : Candidate n) (s : Bool) (name : String) (j : Fin n) :
    Decidable (eligible doc c s name j) := by unfold eligible; split <;> infer_instance

/-- A unique best visible declaration. This relation does not call the resolver. -/
def Resolves (doc : Document) (c : Candidate n) (context : Path) (super : Bool)
    (name : String) (j : Fin n) : Prop :=
  if integerName name then super = false ∧ (c.core.get j).origin = .integer
  else eligible doc c super name j ∧
    ∀ k : Fin n, eligible doc c super name k →
      proximity context (c.paths[k].getD []) ≤ proximity context (c.paths[j].getD []) ∧
      (proximity context (c.paths[k].getD []) = proximity context (c.paths[j].getD []) → k = j)

instance (doc : Document) (c : Candidate n) (p : Path) (s : Bool) (name : String) (j : Fin n) :
    Decidable (Resolves doc c p s name j) := by unfold Resolves; infer_instance

/-- Local source coverage closes over every declaration child; constraints remain
in the original document and are accessed by their owner path, never erased. -/
def isDeclaration : Element → Bool
  | .declaration _ _ _ => true | _ => false

def CoversChildren (doc : Document) (c : Candidate n) (path : Path) : Prop :=
  ∀ k : Fin ((childrenAt doc path).getD []).length,
    isDeclaration (((childrenAt doc path).getD [])[k]) = true →
      ∃ i : Fin n, c.paths[i] = some (path ++ [k.val])

instance (doc : Document) (c : Candidate n) (p : Path) : Decidable (CoversChildren doc c p) := by
  unfold CoversChildren
  infer_instance

def SuperRule (doc : Document) (c : Candidate n) (path : Path)
    (name : Option Name) (target : Option (Fin n)) : Prop :=
  match name, target with
  | none, none => True
  | some name, some j => Resolves doc c path.dropLast true name.text j
  | _, _ => False

instance (doc : Document) (c : Candidate n) (p : Path) (name : Option Name) (j : Option (Fin n)) :
    Decidable (SuperRule doc c p name j) := by
  unfold SuperRule
  split <;> infer_instance

def ReferenceRule (doc : Document) (c : Candidate n) (path : Path)
    (source : Option (Token × Name)) (target : Reference (Fin n)) : Prop :=
  match source, target with
  | none, .basic => True
  | some (arrow, name), .set j => arrow.text = "->" ∧ Resolves doc c path false name.text j
  | some (arrow, name), .bag j => arrow.text = "->>" ∧ Resolves doc c path false name.text j
  | _, _ => False

instance (doc : Document) (c : Candidate n) (p : Path) (source : Option (Token × Name))
    (target : Reference (Fin n)) : Decidable (ReferenceRule doc c p source target) := by
  unfold ReferenceRule
  split <;> infer_instance

def SourceRow (doc : Document) (c : Candidate n) (i : Fin n) : Prop :=
  match c.paths[i], c.header doc i with
  | some path, some h =>
    let d := c.core.get i
    let parent := d.parent.map c.core.get
    let super := d.super.map (fun j => c.groups[j])
    d.origin = .user ∧ path ≠ [] ∧ reserved h.name.text = false ∧
    d.name = h.name.text ∧ d.source = (nodeAt doc path).map Element.span ∧
    d.authored = some ⟨h.abstractToken.isSome, h.cardinality.map cardBounds,
      h.group.map (fun g => (authoredGroup g).range)⟩ ∧
    (if path.length = 1 then
      d.parent = (if h.abstractToken.isSome then none else some c.core.root)
     else ∃ p : Fin n, d.parent = some p ∧ c.paths[p] = some path.dropLast ∧ h.abstractToken.isSome = false) ∧
    SuperRule doc c path (h.super.orElse (fun _ => if h.useToken.isSome then some h.name else none)) d.super ∧
    ReferenceRule doc c path h.reference d.reference ∧
    c.groups[i] = (h.group.map authoredGroup).getD (super.getD (.bounds {})) ∧
    d.groupBounds = c.groups[i].range ∧
    d.localBounds = (h.cardinality.map cardBounds).getD
      ((d.parent.map (fun p => c.groups[p].childDefault)).getD ⟨1, .finite 1⟩) ∧
    d.isAbstract = (h.abstractToken.isSome || (parent.map (·.isAbstract)).getD false) ∧
    CoversChildren doc c path
  | _, _ => False

instance (doc : Document) (c : Candidate n) (i : Fin n) : Decidable (SourceRow doc c i) := by
  unfold SourceRow
  split <;> infer_instance

def PathOrder (c : Candidate n) (i j : Fin n) : Prop :=
  match c.paths[i], c.paths[j] with
  | some p, some q => (p = q → i = j) ∧ (i.val < j.val → compare p q = .lt) ∧
    (p.dropLast = q.dropLast → (c.core.get i).name = (c.core.get j).name → i = j)
  | _, _ => True

instance (c : Candidate n) (i j : Fin n) : Decidable (PathOrder c i j) := by
  unfold PathOrder
  split <;> infer_instance

def explicitAbstract (doc : Document) (c : Candidate n) (i : Fin n) : Bool :=
  ((c.header doc i).map (fun h => h.abstractToken.isSome)).getD false

/-- Structural admission for the selected richer frontend, without M1's leaf guard. -/
def StructuralChecks (doc : Document) (c : Candidate n) : Prop :=
  (∀ d : Fin n, (c.core.get d).origin = .syntheticRoot ∨
    (c.core.get d).origin = .user ∨ (c.core.get d).origin = .integer) ∧
  (∀ d : Fin n, (c.core.get d).origin = .integer →
    (c.core.get d).parent = some c.core.root ∧ (c.core.get d).reference = .basic ∧
    (c.core.get d).super = none ∧ (c.core.get d).name = "int") ∧
  (∀ d e : Fin n, (c.core.get d).origin = .integer → (c.core.get e).origin = .integer → d = e) ∧
  (∀ d p : Fin n, (c.core.get d).parent = some p → (c.core.get d).isAbstract = true →
    (c.core.get p).isAbstract = true) ∧
  (∀ d : Fin n, explicitAbstract doc c d = true →
    (c.core.get d).isAbstract = true ∧ (c.core.get d).parent = none) ∧
  (∀ d : Fin n, (c.core.get d).parent = none → (c.core.get d).isAbstract = true →
    explicitAbstract doc c d = true) ∧
  (∀ d s : Fin n, (c.core.get d).super = some s → explicitAbstract doc c s = true)

instance (doc : Document) (c : Candidate n) : Decidable (StructuralChecks doc c) := by
  unfold StructuralChecks
  infer_instance

/-- Declarative source-to-table contract, independent of candidate construction.
It specifies coverage, identity, nearest unique lookup, edges, provenance, defaults,
and selected structural admission. No satisfaction predicate occurs here. -/
def Elaboration (doc : Document) (c : Candidate n) : Prop :=
  coreChecks c.core c.certificate ∧
  c.core.root.val = 0 ∧
  (∀ i : Fin n, (c.core.get i).id = i.val) ∧
  CoversChildren doc c [] ∧
  (∀ i : Fin n, if i = c.core.root then
    c.paths[i] = none ∧ (c.core.get i).name = "Sing" ∧
      c.groups[i] = .bounds {} ∧ (c.core.get i).groupBounds = {} ∧
      (c.core.get i).localBounds = ⟨1, .finite 1⟩
   else if (c.core.get i).origin = .integer then
    c.paths[i] = none ∧ (c.core.get i).name = "int" ∧
      (c.core.get i).parent = some c.core.root ∧ (c.core.get i).super = none ∧
      (c.core.get i).reference = .basic ∧ (c.core.get i).isAbstract = false ∧
      c.groups[i] = .bounds {} ∧ (c.core.get i).groupBounds = {} ∧
      (c.core.get i).localBounds = ⟨1, .finite 1⟩ ∧ i.val + 1 = n ∧
      (∃ j : Fin n, (c.core.get j).reference.target = some i)
   else SourceRow doc c i) ∧
  (∀ i j : Fin n, PathOrder c i j) ∧
  (∀ i s : Fin n, (c.core.get i).super = some s →
    (c.core.get s).isAbstract = true ∧ (c.core.get s).parent = none ∧
    (c.core.get s).reference = .basic ∧ (c.core.get i).reference = .basic ∧
    c.realizationRank[i] < c.realizationRank[s]) ∧
  (∀ i t : Fin n, (c.core.get i).reference.target = some t →
    (c.core.get i).parent.isSome = true ∧
    ((c.core.get t).origin = .user ∨ (c.core.get t).origin = .integer)) ∧
  (∀ i p : Fin n, (c.core.get i).parent = some p →
    c.realizationRank[p] < c.realizationRank[i]) ∧ StructuralChecks doc c

instance (doc : Document) (c : Candidate n) : Decidable (Elaboration doc c) := by
  unfold Elaboration
  infer_instance

structure Elaborated (doc : Document) where
  count : Nat
  candidate : Candidate count
  correspondence : Elaboration doc candidate

end ClaferCompiler.Frontend.Resolution
