module

public import ClaferCompiler.IR.Structural

@[expose] public section
/-! [impl->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.IR.Inherited
open Structural

/-- Authored abstractness is semantic input, separate from the effective flag.
No contextual declaration copies are added to the original table. -/
structure Core (n : Nat) where
  structural : Structural.Core n
  explicitAbstract : Vector Bool n
  realizationRank : Vector Nat n

/-- Selected inherited-domain guards. Ranks certify syntax, never source truth.
Only the integer primitive and direct user/integer references are admitted. -/
def checks (m : Core n) : Prop :=
  (∀ d, m.explicitAbstract[d] = true →
    (m.structural.get d).isAbstract = true ∧ (m.structural.get d).parent = none) ∧
  (∀ d, (m.structural.get d).parent = none → (m.structural.get d).isAbstract = true →
    m.explicitAbstract[d] = true) ∧
  (∀ d c, (m.structural.get d).super = some c →
    m.explicitAbstract[c] = true ∧ (m.structural.get c).reference = .basic ∧
      (m.structural.get d).reference = .basic) ∧
  (∀ d t, (m.structural.get d).reference.target = some t →
    (m.structural.get d).parent.isSome = true ∧
      ((m.structural.get t).origin = .user ∨ (m.structural.get t).origin = .integer)) ∧
  (∀ d c, m.explicitAbstract[d] = true → (m.structural.get c).super = some d →
    m.realizationRank[c] < m.realizationRank[d]) ∧
  (∀ d p, m.explicitAbstract[d] = false → (m.structural.get d).parent = some p →
    m.realizationRank[p] < m.realizationRank[d]) ∧
  (∀ d, (m.structural.get d).origin = .syntheticRoot ∨
    (m.structural.get d).origin = .user ∨ (m.structural.get d).origin = .integer) ∧
  (∀ d, (m.structural.get d).origin = .integer →
    (m.structural.get d).parent = some m.structural.root ∧
    (m.structural.get d).reference = .basic ∧ (m.structural.get d).super = none) ∧
  (∀ d e, (m.structural.get d).origin = .integer →
    (m.structural.get e).origin = .integer → d = e) ∧
  (∀ d p, (m.structural.get d).parent = some p →
    (m.structural.get d).isAbstract = true → (m.structural.get p).isAbstract = true)

set_option synthInstance.maxSize 512 in
instance (m : Core n) : Decidable (checks m) := by unfold checks; infer_instance

structure Validated (n : Nat) where
  core : Core n
  certificate : Structural.Certificate n
  coreChecked : Structural.coreChecks core.structural certificate
  selectedChecked : checks core

def validate (m : Core n) (k : Structural.Certificate n) : Except Diagnostic (Validated n) :=
  if hc : Structural.coreChecks m.structural k then
    if hs : checks m then .ok ⟨m, k, hc, hs⟩
    else .error ⟨.unsupported, "ir.inherited-domain-or-ranks", "", none⟩
  else .error ⟨.malformed, "ir.invalid-core-or-ranks", "", none⟩

/-- Allocation projection: explicit families keep cover; groups are emitted
separately over inherited inventories. All identity and relation fields survive. -/
def Core.layoutCore (m : Core n) : Structural.Core n where
  declarations := Vector.ofFn fun d =>
    { m.structural.get d with isAbstract := m.explicitAbstract[d], groupBounds := {} }
  root := m.structural.root

@[simp] theorem layout_get (m : Core n) (d : Fin n) :
    m.layoutCore.get d =
      { m.structural.get d with isAbstract := m.explicitAbstract[d], groupBounds := {} } := by
  simp [Core.layoutCore, Structural.Core.get]

@[simp] theorem layout_root (m : Core n) : m.layoutCore.root = m.structural.root := rfl

def Validated.layout (v : Validated n) : Structural.Layout n where
  core := v.core.layoutCore
  certificate := v.certificate
  coreChecked := by
    rcases v.coreChecked with ⟨ids, origins, root, parents, supers, bounds, parentless⟩
    refine ⟨by simpa using ids, by simpa only [layout_root, layout_get] using origins, ?_,
      by simpa using parents, by simpa using supers, ?_, ?_⟩
    · have he : v.core.explicitAbstract[v.core.structural.root] = false := by
        cases h : v.core.explicitAbstract[v.core.structural.root] with
        | false => rfl
        | true => have ha := (v.selectedChecked.1 _ h).1; simp [root.2.2.2] at ha
      simpa only [layout_root, layout_get] using And.intro root.1 (And.intro root.2.1 (And.intro root.2.2.1 he))
    · intro d
      simpa [Bounds.Valid] using (bounds d).1
    · intro d hp hd
      simp only [layout_get] at hp ⊢
      apply v.selectedChecked.2.1 d
      · simpa using hp
      · exact parentless d (by simpa using hp) hd
  rootNotSuper := by
    intro d hd
    have hs : (v.core.structural.get d).super = some v.core.structural.root := by
      simpa only [layout_root, layout_get] using hd
    have ha := (v.selectedChecked.1 _ (v.selectedChecked.2.2.1 d _ hs).1).1
    simp [v.coreChecked.2.2.1.2.2.2] at ha

/-- Separate opt-in API: authored flags and realization ranks are mandatory. -/
structure Raw where
  structural : Structural.Raw
  explicitAbstract : Array Bool
  realizationRanks : Array Nat
  deriving Repr

def validateRaw (r : Raw) : Except Diagnostic (Validated r.structural.declarations.size) := do
  let (m, k) ← Structural.resolveRaw r.structural
  if he : r.explicitAbstract.size = r.structural.declarations.size then
    if hr : r.realizationRanks.size = r.structural.declarations.size then
      validate ⟨m, ⟨r.explicitAbstract, he⟩, ⟨r.realizationRanks, hr⟩⟩ k
    else .error ⟨.malformed, "ir.realization-rank-length", "/realizationRanks", none⟩
  else .error ⟨.malformed, "ir.explicit-abstract-length", "/explicitAbstract", none⟩

end ClaferCompiler.IR.Inherited
