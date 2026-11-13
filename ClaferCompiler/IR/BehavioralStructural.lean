module

public import ClaferCompiler.Frontend.Defaults

@[expose] public section
namespace ClaferCompiler.IR.BehavioralStructural
open Structural

-- [impl->req~compiler-behavioral-structural-bridge~1]
def profile : String := "behavioral-0.5.8/v1"

/-- Declared references stay declared: inherited references are views of their
original owner. Authored abstractness and group provenance are retained separately. -/
structure Core (n : Nat) where
  structural : Structural.Core n
  authoredAbstract : Vector Bool n
  groups : Vector Frontend.Resolution.Group n

/-- Derived finite lookup tables. Their recursive equations are checked, so
neither a missing ancestor nor a fabricated reference owner can be trusted. -/
structure Analysis (n : Nat) where
  ancestors : Vector (List (Fin n)) n
  referenceOwners : Vector (Option (Fin n)) n

def analysisStep (m : Core n) (a : Analysis n) : Analysis n where
  ancestors := Vector.ofFn fun d => d ::
    ((m.structural.get d).super.map (fun s => a.ancestors[s])).getD []
  referenceOwners := Vector.ofFn fun d =>
    if (m.structural.get d).reference = .basic then
      (m.structural.get d).super.bind (fun s => a.referenceOwners[s])
    else some d

def analyze (m : Core n) : Analysis n :=
  Nat.repeat (analysisStep m) n
    ⟨Vector.replicate n [], Vector.replicate n none⟩

def Analysis.Valid (m : Core n) (a : Analysis n) : Prop :=
  (∀ d, a.ancestors[d] = d ::
    ((m.structural.get d).super.map (fun s => a.ancestors[s])).getD []) ∧
  (∀ d, a.referenceOwners[d] =
    if (m.structural.get d).reference = .basic then
      (m.structural.get d).super.bind (fun s => a.referenceOwners[s])
    else some d)

instance (m : Core n) (a : Analysis n) : Decidable (a.Valid m) := by
  unfold Analysis.Valid; infer_instance

def canExtend : Reference α → Reference α → Prop
  | .set _, _ | .bag _, .bag _ | .bag _, .basic | .basic, .basic => True
  | _, _ => False

instance (a b : Reference α) : Decidable (canExtend a b) := by
  cases a <;> cases b <;> unfold canExtend <;> infer_instance

/-- This profile extends structural admission, not M1 or the static selected
realization guard. In particular it permits concrete supers and nested abstracts. -/
def checks (m : Core n) (k : Certificate n) (a : Analysis n) : Prop :=
  coreChecks m.structural k ∧ a.Valid m ∧
  m.authoredAbstract[m.structural.root] = false ∧
  (∀ d, m.authoredAbstract[d] = true → (m.structural.get d).isAbstract = true) ∧
  (∀ d, (m.structural.get d).parent = none → d ≠ m.structural.root →
    m.authoredAbstract[d] = true) ∧
  (∀ d, (m.structural.get d).origin = .integer →
    (m.structural.get d).parent = some m.structural.root ∧
    (m.structural.get d).reference = .basic ∧ (m.structural.get d).super = none) ∧
  (∀ d e, (m.structural.get d).origin = .integer →
    (m.structural.get e).origin = .integer → d = e) ∧
  (∀ d s p, (m.structural.get d).super = some s →
    (m.structural.get s).parent = some p →
    ∃ q, (m.structural.get d).parent = some q ∧ p ∈ a.ancestors[q]) ∧
  (∀ d s o x y, (m.structural.get d).super = some s →
    a.referenceOwners[s] = some o →
    (m.structural.get d).reference.target = some x →
    (m.structural.get o).reference.target = some y →
    y ∈ a.ancestors[x] ∧ canExtend (m.structural.get d).reference (m.structural.get o).reference) ∧
  (∀ d, m.groups[d].range = (m.structural.get d).groupBounds)

def supported (m : Core n) : Prop := ∀ d,
  (m.structural.get d).origin = .syntheticRoot ∨
  (m.structural.get d).origin = .user ∨ (m.structural.get d).origin = .integer

set_option synthInstance.maxSize 1024 in
instance (m : Core n) (k : Certificate n) (a : Analysis n) : Decidable (checks m k a) := by
  unfold checks; infer_instance

instance (m : Core n) : Decidable (supported m) := by unfold supported; infer_instance

structure Validated (n : Nat) where
  core : Core n
  certificate : Certificate n
  analysis : Analysis n
  checked : checks core certificate analysis
  support : supported core

/-- Own and inherited child declarations. Group evaluation takes the union of
their head fibers; it must not sum fiber sizes or count reference targets. -/
def childDeclarations (v : Validated n) (d : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun c =>
    ((v.core.structural.get c).parent.map (fun p => decide (p ∈ v.analysis.ancestors[d]))).getD false

def validate (selectedProfile : String) (m : Core n) (k : Certificate n) :
    Except Diagnostic (Validated n) :=
  if selectedProfile ≠ profile then
    .error ⟨.unsupported, "behavioral.profile", "", none⟩
  else if hs : supported m then
    let a := analyze m
    if hc : checks m k a then .ok ⟨m, k, a, hc, hs⟩
    else .error ⟨.malformed, "behavioral.structural-admission", "", none⟩
  else .error ⟨.unsupported, "behavioral.primitive-domain", "", none⟩

structure Raw where
  structural : Structural.Raw
  authoredAbstract : Array Bool
  groups : Array Frontend.Resolution.Group

def validateRaw (selectedProfile : String) (r : Raw) :
    Except Diagnostic (Validated r.structural.declarations.size) := do
  let (m, k) ← Structural.resolveRaw r.structural
  if ha : r.authoredAbstract.size = r.structural.declarations.size then
    if hg : r.groups.size = r.structural.declarations.size then
      validate selectedProfile ⟨m, ⟨r.authoredAbstract, ha⟩, ⟨r.groups, hg⟩⟩ k
    else .error ⟨.malformed, "behavioral.group-length", "/groups", none⟩
  else .error ⟨.malformed, "behavioral.abstract-length", "/authoredAbstract", none⟩

end ClaferCompiler.IR.BehavioralStructural
