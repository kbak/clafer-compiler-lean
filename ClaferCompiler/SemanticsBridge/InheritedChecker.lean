module

public import ClaferCompiler.SemanticsBridge.Inherited
public import Clafer.Verification.Finite

@[expose] public section
/-! [impl->req~compiler-pipeline-correctness~1]
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Verification.Inherited
open Clafer.Semantics Clafer.Verification DPGraph.Predicates

instance (v : IR.Inherited.Validated n) (c : Candidate n) (d : Fin n)
    (p x : Fin c.size) : Decidable (Clafer.Compile.Groups.ChildObjects
      (SemanticsBridge.Inherited.interpret v.core).family (realize c) d p x) := by
  unfold Clafer.Compile.Groups.ChildObjects
  change Decidable (∃ a, (SemanticsBridge.Inherited.interpret v.core).toEffectiveCore.Ancestor d a ∧
    ∃ e, (v.core.structural.get e).parent = some a ∧ c.contains e p x = true)
  infer_instance

/-- The original finite semantic clauses are reusable; the public guarded M1
`check` is never invoked here. Inherited groups count their actual ancestor
inventory in the common object carrier, preserving shared object identity. -/
def groupChecks (v : IR.Inherited.Validated n) (c : Candidate n) : Prop :=
  ∀ d, v.core.explicitAbstract[d] = false → ∀ p, c.head d p = true →
    CountInRange (SemanticsBridge.Structural.bounds (v.core.structural.get d).groupBounds)
      (Fintype.card {x : Fin c.size //
        Clafer.Compile.Groups.ChildObjects
          (SemanticsBridge.Inherited.interpret v.core).family (realize c) d p x})

instance (v : IR.Inherited.Validated n) (c : Candidate n) : Decidable (groupChecks v c) := by
  unfold groupChecks
  infer_instance

/-- Move guards before the remaining finite quantifiers. This is the same key
property, but empty containment/dereference fibers do not enumerate four full
copies of the ambient universe. -/
def keys (m : EffectiveCore n) (c : Candidate n) : Prop :=
  ∀ d, (m.family.reference d).kind = .referenceSet → ∀ p x, c.contains d p x = true →
    ∀ t, c.deref d x t = true → ∀ y, c.contains d p y = true → c.deref d y t = true → x = y

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (keys m c) := by
  unfold keys
  infer_instance

theorem keys_iff (m : EffectiveCore n) (c : Candidate n) : keys m c ↔ (realize c).Keys m := by
  constructor
  · intro h d hd p t x y hpx hxt hpy hyt
    exact h d hd p x hpx t hxt y hpy hyt
  · intro h d hd p x hpx t hxt y hpy hyt
    exact h d hd p t x y hpx hxt hpy hyt

def baseChecks (m : EffectiveCore n) (c : Candidate n) : Prop :=
  (realize c).Typed m ∧ (realize c).Rooted m ∧ (realize c).Inherits m ∧
  (realize c).Abstracts m ∧ (realize c).Parents m ∧ (realize c).References m ∧
  keys m c ∧ multiplicityChecks m c ∧ Clafer.Verification.groupChecks m c ∧
  (realize c).DeclarationDisjoint m

instance (m : EffectiveCore n) (c : Candidate n) : Decidable (baseChecks m c) := by
  unfold baseChecks
  infer_instance

theorem baseChecks_iff (m : EffectiveCore n) (c : Candidate n) :
    baseChecks m c ↔ Clafer.Verification.Checks m c := by
  simp only [baseChecks, Clafer.Verification.Checks, keys_iff]

def Checks (v : IR.Inherited.Validated n) (c : Candidate n) : Prop :=
  baseChecks (SemanticsBridge.Structural.interpret v.core.layoutCore) c ∧ groupChecks v c

instance (v : IR.Inherited.Validated n) (c : Candidate n) : Decidable (Checks v c) := by
  unfold Checks
  infer_instance

def check (v : IR.Inherited.Validated n) (c : Candidate n) : Bool := decide (Checks v c)

/-- New evaluator justification for selected inherited finite observations.
It does not assert that a finite carrier contains all mathematical integers or
satisfies authored constraints. Those require their separate pipeline bridge. -/
theorem check_correct (v : IR.Inherited.Validated n) (c : Candidate n) :
    check v c = true ↔ Clafer.Semantics.Realization.Satisfies
      (SemanticsBridge.Inherited.interpret v.core) (Clafer.Verification.realize c) := by
  rw [check, decide_eq_true_eq, Checks, baseChecks_iff, Clafer.Verification.checks_iff,
    SemanticsBridge.Inherited.satisfies_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h d hd p
    exact (inRange_card _ _).mpr (h d hd p.val p.property)
  · intro h d hd p hp
    exact (inRange_card _ _).mp (h d hd ⟨p,hp⟩)

end ClaferCompiler.Verification.Inherited
