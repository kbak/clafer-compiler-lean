module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural
open Clafer.Semantics DPGraph.Predicates

theorem unrestricted_range (U : Type u) : InRange ⟨0, .unbounded⟩ U :=
  ⟨⟨Function.Embedding.ofIsEmpty⟩, trivial⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
def complete_containment_equiv (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (ordinary : d ≠ p) (x : Fin o) :
    {y : Fin o // ((SemanticsBridge.Behavioral.trace l.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y} ≃
    {y : Completion o // ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains
        d (Sum.inl x) y} :=
  Equiv.ofBijective (fun y => ⟨Sum.inl y.val,
    (completeContains_objects v p l t d x y.val).mpr y.property⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      cases y with
      | inl y => exact ⟨⟨y, (completeContains_objects v p l t d x y).mp hy⟩, rfl⟩
      | inr z =>
        have eq := ((completeContains_integer v p primitive l t d (Sum.inl x) z).mp hy).2.2
        exact (ordinary eq.symm).elim)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem complete_multiplicities (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (l : ObservedLasso k o steps) (t : Nat)
    (objects : ∀ d c, (v.core.structural.get d).parent = some c → d ≠ p → c ≠ p →
      ∀ x, x ∈ ((SemanticsBridge.Behavioral.trace l.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c →
      InRange (SemanticsBridge.Structural.bounds (v.core.structural.get d).localBounds)
        {y : Fin o // ((SemanticsBridge.Behavioral.trace l.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y}) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Multiplicities
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore := by
  intro d c parent x head
  by_cases dp : d = p
  · subst d
    change InRange (SemanticsBridge.Structural.bounds (v.core.structural.get p).localBounds) _
    rw [(shape p primitive).2.1]
    exact unrestricted_range _
  · have cp : c ≠ p := by
      intro eq
      subst c
      exact (shape p primitive).2.2.2.2.2 d parent
    cases x with
    | inr z =>
      exact (cp ((completeHead_integer v p primitive l t c z).mp head).symm).elim
    | inl x =>
      exact (inRange_iff _ (complete_containment_equiv v p primitive l t d dp x)).mp
        (objects d c parent dp cp x head)

theorem completeChildObjects_objects (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x y : Fin o) :
    Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t)
        d (Sum.inl x) (Sum.inl y) ↔
    Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((SemanticsBridge.Behavioral.trace l.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y := by
  unfold Groups.ChildObjects
  exact exists_congr fun _ => and_congr_right fun _ =>
    exists_congr fun c => and_congr_right fun _ => completeContains_objects v p l t c x y

def complete_children_equiv (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x : Fin o)
    (nonroot : x ≠ l.objects.identities.root) :
    {y : Fin o // Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((SemanticsBridge.Behavioral.trace l.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y} ≃
    {y : Completion o // Groups.ChildObjects (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((completeTrace v p l).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d (Sum.inl x) y} :=
  Equiv.ofBijective (fun y => ⟨Sum.inl y.val,
    (completeChildObjects_objects v p l t d x y.val).mpr y.property⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      cases y with
      | inl y => exact ⟨⟨y, (completeChildObjects_objects v p l t d x y).mp hy⟩, rfl⟩
      | inr z =>
        obtain ⟨_, _, c, _, contained⟩ := hy
        have eq := ((completeContains_integer v p primitive l t c (Sum.inl x) z).mp contained).1
        exact (nonroot (Sum.inl.inj eq)).elim)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Primitive and root groups use their admitted unrestricted bounds. All other
groups count exactly the same union of occurrence fibres, including overlap. -/
theorem complete_groups (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (l : ObservedLasso k o steps) (t : Nat)
    (ids : Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (SemanticsBridge.Behavioral.trace l.objects))
    (objects : ∀ d, v.core.authoredAbstract[d] = false → d ≠ p → d ≠ v.core.structural.root →
      Groups.Holds (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((SemanticsBridge.Behavioral.trace l.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d) :
    Clafer.Behavioral.Structural.Groups (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p l) t := by
  have wf := SemanticsBridge.BehavioralStructural.validated_wellFormed v
  intro d concrete x
  by_cases dp : d = p
  · subst d
    rw [← wf.group_agrees p]
    change InRange (SemanticsBridge.Structural.bounds (v.core.structural.get p).groupBounds) _
    rw [(shape p primitive).2.2.1]
    exact unrestricted_range _
  by_cases dr : d = v.core.structural.root
  · subst d
    rw [← wf.group_agrees v.core.structural.root]
    change InRange (SemanticsBridge.Structural.bounds (v.core.structural.get v.core.structural.root).groupBounds) _
    rw [(shape p primitive).2.2.2.1]
    exact unrestricted_range _
  rcases x with ⟨x, hx⟩
  cases x with
  | inr z => exact (dp ((completeHead_integer v p primitive l t d z).mp hx).symm).elim
  | inl x =>
    have nonroot : x ≠ l.objects.identities.root := by
      intro eq
      subst x
      exact raw_root_separate _ _ wf ids t d dr hx
    exact (inRange_iff _ (complete_children_equiv v p primitive l t d x nonroot)).mp
      (objects d concrete dp dr ⟨x, hx⟩)

end ClaferCompiler.Correctness.Behavioral.Full
