module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionStructure
public import Clafer.Behavioral.StructuralObservation

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural

theorem primitive_target_none (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) :
    (v.core.structural.get p).reference.target = none := by
  rw [(v.checked.2.2.2.2.2.1 p primitive).2.1]
  rfl

theorem integerDeclaration_eq (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (d : Fin k) :
    integerDeclaration v d = true ↔ d = p := by
  constructor
  · intro hd
    have hd : (v.core.structural.get d).origin = .integer := by
      simpa [integerDeclaration] using hd
    exact v.checked.2.2.2.2.2.2.1 d p hd primitive
  · rintro rfl
    simp [integerDeclaration, primitive]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The object table typing premise is obtained from generated reference facts.
All added scalar links have their exact mathematical target in the completed
primitive extent, independently of the selected target bitwidth. -/
theorem complete_reference_typed (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat)
    (objects : ∀ d x y, (d, x, y) ∈ (l.objects.at t).references →
      ∃ c, (v.core.structural.get d).reference.target = some c ∧
        integerDeclaration v c = false ∧
        x ∈ ((SemanticsBridge.Behavioral.trace l.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ∧
        y ∈ ((SemanticsBridge.Behavioral.trace l.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c) :
    ∀ d x y, (completeTrace v p l).deref t d x y →
      x ∈ ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ∧
      ∃ c, ((SemanticsBridge.BehavioralStructural.interpret v.core).family.reference d).target = some c ∧
        y ∈ ((completeTrace v p l).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c := by
  intro d x y link
  cases x with
  | inr z => exact (completeDeref_integer_source v p l t d z y link).elim
  | inl x =>
    cases y with
    | inl y =>
      obtain ⟨c, hr, _, hx, hy⟩ := objects d x y link
      exact ⟨hx, c, by simpa [SemanticsBridge.BehavioralStructural.interpret,
        SemanticsBridge.Structural.interpret] using hr, hy⟩
    | inr z =>
      obtain ⟨hr, live, ancestor, _⟩ := (completeDeref_integer v p l t d x z).mp link
      exact ⟨⟨live, ancestor⟩, p, by simpa [SemanticsBridge.BehavioralStructural.interpret,
        SemanticsBridge.Structural.interpret] using hr,
        (completeHead_integer v p primitive l t p z).mpr rfl⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem complete_references (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat)
    (typed : ∀ d x y, (d, x, y) ∈ (l.objects.at t).references →
      ∃ c, (v.core.structural.get d).reference.target = some c ∧ integerDeclaration v c = false)
    (objects : ∀ d c, (v.core.structural.get d).reference.target = some c →
      integerDeclaration v c = false → ∀ x,
      x ∈ ((SemanticsBridge.Behavioral.trace l.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d →
      ∃! y, (d, x, y) ∈ (l.objects.at t).references) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).References
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore := by
  intro d c hr x hx
  have hr : (v.core.structural.get d).reference.target = some c := by
    simpa [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret] using hr
  cases x with
  | inr z =>
    have eq := (completeHead_integer v p primitive l t d z).mp hx
    subst d
    rw [primitive_target_none v p primitive] at hr
    contradiction
  | inl x =>
    by_cases cp : c = p
    · subst c
      refine ⟨Sum.inr (l.valuesAt t)[x], ⟨hr, hx.1, hx.2, rfl⟩, ?_⟩
      intro y hy
      cases y with
      | inl y =>
        obtain ⟨c, target, ordinary⟩ := typed d x y hy
        have eq : c = p := Option.some.inj (target.symm.trans hr)
        subst c
        have conflict := (integerDeclaration_eq v p primitive p).mpr rfl
        rw [ordinary] at conflict
        contradiction
      | inr z => exact congrArg Sum.inr hy.2.2.2.symm
    · have ordinary : integerDeclaration v c = false := by
        apply Bool.eq_false_iff.mpr
        exact fun h => cp ((integerDeclaration_eq v p primitive c).mp h)
      obtain ⟨y, hy, unique⟩ := objects d c hr ordinary x hx
      refine ⟨Sum.inl y, hy, ?_⟩
      intro z hz
      cases z with
      | inl z => exact congrArg Sum.inl (unique z hz)
      | inr z =>
        have eq : c = p := Option.some.inj (hr.symm.trans hz.1)
        exact (cp eq).elim

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completeInherited_objects (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d owner : Fin k)
    (lookup : v.analysis.referenceOwners[d] = some owner) (x y : Fin o) :
    (Clafer.Behavioral.Structural.observed
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l)).deref
        t d (Sum.inl x) (Sum.inl y) ↔
      (l.objects.at t).live[x] = true ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        l.objects.identities.directType[x] d ∧ (owner, x, y) ∈ (l.objects.at t).references := by
  have owner := SemanticsBridge.BehavioralStructural.owner_sound v.checked.2.1
    v.checked.1.2.2.2.2.1 lookup
  change Clafer.Behavioral.InheritedReference.deref _ _ _ _ _ ↔ _
  rw [Clafer.Behavioral.InheritedReference.deref_owner owner]
  change ((_ ∧ _) ∧ _) ↔ _
  exact and_assoc

theorem completeInherited_integer (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d owner : Fin k)
    (lookup : v.analysis.referenceOwners[d] = some owner) (x : Fin o) (z : Int) :
    (Clafer.Behavioral.Structural.observed
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l)).deref
        t d (Sum.inl x) (Sum.inr z) ↔
      (l.objects.at t).live[x] = true ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        l.objects.identities.directType[x] d ∧
      (v.core.structural.get owner).reference.target = some p ∧ (l.valuesAt t)[x] = z := by
  have ho := SemanticsBridge.BehavioralStructural.owner_sound v.checked.2.1
    v.checked.1.2.2.2.2.1 lookup
  change Clafer.Behavioral.InheritedReference.deref _ _ _ _ _ ↔ _
  rw [Clafer.Behavioral.InheritedReference.deref_owner ho]
  change ((_ ∧ _) ∧ (_ ∧ _ ∧ _ ∧ _)) ↔ _
  constructor
  · rintro ⟨⟨live, ancestor⟩, target, _, _, scalar⟩
    exact ⟨live, ancestor, target, scalar⟩
  · rintro ⟨live, ancestor, target, scalar⟩
    exact ⟨⟨live, ancestor⟩, target, live, ancestor.trans ho.ancestor, scalar⟩

end ClaferCompiler.Correctness.Behavioral.Full
