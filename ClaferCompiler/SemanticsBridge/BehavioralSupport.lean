module

public import ClaferCompiler.IR.BehavioralSupport
public import ClaferCompiler.SemanticsBridge.BehavioralStructural
public import ClaferCompiler.SemanticsBridge.Expr
public import Clafer.Behavioral.StructuralBinding

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.BehavioralSupport
open IR.BehavioralStructural IR.BehavioralSupport
open Clafer.Behavioral

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem role_iff (v : Validated k) (d a b : Fin k) (kind : IR.Expr.MapKind) :
    role v d a b kind ↔ StructuralBinding.Role (BehavioralStructural.interpret v.core)
      d a b (Expr.mapKind kind) := by
  have ranks := v.checked.1.2.2.2.2.1
  have paths := v.checked.2.1
  have ancestor (x y : Fin k) : y ∈ v.analysis.ancestors[x] ↔
      (BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor x y :=
    ⟨BehavioralStructural.ancestor_sound paths ranks, BehavioralStructural.ancestor_complete paths⟩
  have owner (x y : Fin k) : v.analysis.referenceOwners[x] = some y ↔
      InheritedReference.Owner (BehavioralStructural.interpret v.core).family x y :=
    ⟨BehavioralStructural.owner_sound paths ranks, BehavioralStructural.owner_complete paths⟩
  cases kind <;> simp only [role, StructuralBinding.Role, Expr.mapKind,
    ← ancestor, ← owner]
  all_goals simp only [BehavioralStructural.interpret, Structural.interpret, Structural.reference_target]

universe u
variable (v : Validated k) (s : IR.Expr.Support n m) (checked : Checked v s)
  {U : Type u} (τ : Trace (Fin k) U) (t : Nat)
  (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret v.core) τ)

/-- The runtime checks supply endpoint typing through the accepted upstream
constructor. Source state validity is an explicit premise, never assumed target truth. -/
def resolution : StructuralBinding.Resolution (BehavioralStructural.interpret v.core)
    τ t (Expr.support s) :=
  StructuralBinding.Resolution.ofRoles _ τ t valid
    (fun x => checked.binding.classes[x]) (fun e => checked.binding.owners[e])
    (fun x => congrArg Clafer.DeclId.mk (checked.valid.1 x))
    (fun e => congrArg Clafer.DeclId.mk (checked.valid.2.2 e).1)
    (fun e => (role_iff v _ _ _ _).mp (checked.valid.2.2 e).2)

/-- Shared reference occurrences retain the full intermediate-head link carrier.
This is stronger than equality of a relation with duplicate endpoints erased. -/
theorem coherent (R : Clafer.Constraints.IntegerRealization U)
    (integers : ∀ x, (Expr.support s).integer x = true →
      (τ.raw (BehavioralStructural.interpret v.core).toEffectiveCore t).head checked.binding.classes[x] = R.domain) :
    ((resolution v s checked τ t valid).binding
      (BehavioralStructural.validated_wellFormed v).ids R integers).Coherent :=
  (resolution v s checked τ t valid).coherent
    (BehavioralStructural.validated_wellFormed v).ids R integers

def navigation : Navigation k → Step (Fin k)
  | .parent => .parent
  | .child d => .child d
  | .dereference r => .deref r.head

theorem referenceView_sound {d : Fin k} {r : ReferenceView k}
    (h : referenceView v d = some r) :
    r.head = d ∧
    InheritedReference.Owner (BehavioralStructural.interpret v.core).family d r.owner ∧
    ((BehavioralStructural.interpret v.core).family.reference r.owner).target = some r.target := by
  unfold referenceView at h
  cases ho : v.analysis.referenceOwners[d] with
  | none => simp [ho] at h
  | some o =>
    cases ht : (v.core.structural.get o).reference.target with
    | none => simp [ho, ht] at h
    | some target =>
      have he : (ReferenceView.mk d o target) = r := by simpa [ho, ht] using h
      subst r
      exact ⟨rfl, BehavioralStructural.owner_sound v.checked.2.1 v.checked.1.2.2.2.2.1 ho,
        by simpa [BehavioralStructural.interpret, Structural.interpret] using ht⟩

include valid in
/-- Current dereference is over the inherited owner while captured head identity
stays fixed. Target liveness and assignment coherence come from source validity. -/
theorem current_target_live {d : Fin k} {r : ReferenceView k} {x y : U}
    (resolved : referenceView v d = some r)
    (link : InheritedReference.deref (BehavioralStructural.interpret v.core).family
      (τ.raw (BehavioralStructural.interpret v.core).toEffectiveCore t) r.head x y) :
    y ∈ τ.live t := by
  have _ := referenceView_sound v resolved
  exact valid.target_live link

/-- Existing checked static expressions reuse the full occurrence-preserving
binding. The common domain requires live `this` and singleton-compatible locals;
arbitrary captured sets use the accepted behavioral set evaluator below. -/
theorem static_agreement (R : Clafer.Constraints.IntegerRealization U)
    (integers : ∀ x, (Expr.support s).integer x = true →
      (τ.raw (BehavioralStructural.interpret v.core).toEffectiveCore t).head checked.binding.classes[x] = R.domain)
    {Γ ty} (e : IR.Expr.Checked s Γ ty) (ρ : Environment U (Γ.map (Expr.binder s)).length)
    (σ : Clafer.Constraints.Environment (Expr.support s) U (Γ.map (Expr.binder s)))
    (same : CapturedStatic.Compatible ρ σ) (present : ρ.this ∈ τ.live t) :
    CapturedStatic.eval (τ.live t)
      ((resolution v s checked τ t valid).binding (BehavioralStructural.validated_wellFormed v).ids R integers)
      (Expr.interpret s e.term.raw e.typed) ρ =
    (Expr.interpret s e.term.raw e.typed).denote
      ((resolution v s checked τ t valid).binding (BehavioralStructural.validated_wellFormed v).ids R integers) σ :=
  (resolution v s checked τ t valid).static_agreement
    (BehavioralStructural.validated_wellFormed v).ids R integers _ ρ σ same present

theorem actual_parent {locals : Nat} (ρ : Environment U locals) (p : U) :
    p ∈ Structural.eval (BehavioralStructural.interpret v.core) τ
      (.thisStep (navigation .parent)) ρ t ↔
      τ.identities.parent ρ.this = some p ∧ p ∈ τ.live t :=
  Structural.direct_parent _ _ _ _ _

include valid in
theorem finite_captured_targets {locals : Nat} (ρ : Environment U locals)
    {heads : Set U} (finite : heads.Finite) (d : Fin k) :
    (Structural.eval (BehavioralStructural.interpret v.core) τ
      (.step (.deref d) (.var 0)) (ρ.push heads) t).Finite :=
  Structural.finite_captured_deref _ _ valid _ finite _ _

end ClaferCompiler.SemanticsBridge.BehavioralSupport
