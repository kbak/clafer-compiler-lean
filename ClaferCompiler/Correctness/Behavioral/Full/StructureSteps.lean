module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureObservations
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

/-- The expression observation universe contains every occurrence and exactly
those mathematical integers representable at the selected target width. -/
def observedDomain (width : Nat) : Set (Completion o) := {x | match x with
  | .inl _ => True
  | .inr z => Backend.Alloy.fitsInt width z = true}

@[simp] theorem observedDomain_object (width : Nat) (x : Fin o) :
    Sum.inl x ∈ observedDomain width := trivial
@[simp] theorem observedDomain_integer (width : Nat) (z : Int) :
    Sum.inr z ∈ observedDomain (o := o) width ↔ Backend.Alloy.fitsInt width z = true := Iff.rfl

theorem observedLive_term (v : IR.BehavioralStructural.Validated k) :
    (observedLive v).Term := .union (live_term v) .ints

theorem step_term (v : IR.BehavioralStructural.Validated k) (st : IR.Behavioral.Step k) :
    (step v st).Term := by
  cases st with
  | parent =>
    exact .union (.inter (.field 0) (.product (.sig 0) (live_term v)))
      (.product .ints (root_term v))
  | child d => exact contains_term v d
  | deref d => exact deref_term v d

namespace Mixed

theorem of_objects_binary {labels : Fin o ↪ Nat} {R : Fin o → Fin o → Prop} {rows : Relation}
    (h : Relations.Binary labels R rows) :
    Binary (completionAtom labels) (fun x y => ∃ a b, x = Sum.inl a ∧ y = Sum.inl b ∧ R a b) rows := by
  intro row
  rw [h row]
  constructor
  · rintro ⟨a, b, h, he⟩
    exact ⟨Sum.inl a, Sum.inl b, ⟨a, b, rfl, rfl, h⟩, he⟩
  · rintro ⟨x, y, ⟨a, b, rfl, rfl, h⟩, he⟩
    exact ⟨a, b, h, he⟩

end Mixed

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem root_completed (rep : TraceRep v source target) (p : Fin k)
    (w : Nat) (e : Environment) (t : Nat) :
    Mixed.Unary rep.atoms {(completeTrace v p source).identities.root}
      ((root v).eval (schema v) w target.unfold e t) := by
  apply Mixed.unary_congr (Mixed.of_objects_unary (rep.root_meaning w e t))
  intro x
  simp only [Set.mem_image, Set.mem_singleton_iff, exists_eq_left]
  change Sum.inl source.objects.identities.root = x ↔ x = Sum.inl source.objects.identities.root
  exact eq_comm

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem observedLive_completed (rep : TraceRep v source target) (p : Fin k)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat) :
    Mixed.Unary rep.atoms ((completeTrace v p source).live t ∩ observedDomain w)
      ((observedLive v).eval (schema v) w target.unfold e t) := by
  apply Mixed.unary_congr (Mixed.unary_union (live_term v) .ints
    (Mixed.of_objects_unary (rep.live_meaning w e t)) (rep.ints_completed w positive small e t))
  intro x
  cases x <;> simp [completeTrace, observedDomain]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Parent navigation is available from an absent captured occurrence. Only
the destination must be live; primitive integers have the synthetic root parent. -/
theorem parent_completed (rep : TraceRep v source target) (p : Fin k)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (rootLive : (source.objects.at t).live[source.objects.identities.root] = true) :
    Mixed.Binary rep.atoms (fun x y => x ∈ observedDomain w ∧
      (completeTrace v p source).identities.parent x = some y ∧
      y ∈ (completeTrace v p source).live t)
      ((step v .parent).eval (schema v) w target.unfold e t) := by
  have objectRows := Relations.binary_inter rep.label_injective
    (.field 0) (.product (.sig 0) (live_term v)) (rep.parent_meaning w e t)
    (Relations.binary_product (.sig 0) (live_term v)
      (rep.objects_meaning w e t) (rep.live_meaning w e t))
  have objects := Mixed.of_objects_binary (labels := rep.labels) objectRows
  have integers := Mixed.binary_product .ints (root_term v)
    (rep.ints_completed w positive small e t) (rep.root_completed p w e t)
  apply Mixed.binary_congr (Mixed.binary_union
    (.inter (.field 0) (.product (.sig 0) (live_term v)))
    (.product .ints (root_term v)) objects integers)
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y => simp [completeTrace, completeIdentities, observedDomain, Option.map_eq_some_iff]
    | inr z => simp [completeTrace, completeIdentities, observedDomain, Option.map_eq_some_iff]
  | inr z =>
    cases y with
    | inl y =>
      simp only [Set.mem_singleton_iff, Set.mem_univ, Sum.inr.injEq,
        reduceCtorEq, false_and, exists_false, false_or,
        completeTrace, completeIdentities, observedDomain, Set.mem_ofPred_eq,
        Sum.elim_inr, Option.some.injEq, Sum.inl.injEq]
      constructor
      · rintro ⟨⟨u, rfl, fits⟩, rfl⟩
        exact ⟨fits, rfl, rootLive⟩
      · rintro ⟨fits, rfl, _⟩
        exact ⟨⟨z, rfl, fits⟩, rfl⟩
    | inr u => simp [completeTrace, completeIdentities, observedDomain]

theorem head_inside (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (w t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ⊆ observedDomain w := by
  intro x hx
  cases x with
  | inl x => trivial
  | inr z =>
    have eq := (completeHead_integer v p primitive source t d z).mp hx
    have hi := (integerDeclaration_eq v p primitive d).mpr eq.symm
    rw [ordinary] at hi
    contradiction

theorem contains_inside (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (w t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false)
    {x y : Completion o}
    (h : ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d x y) :
    x ∈ observedDomain w ∧ y ∈ observedDomain w := by
  constructor
  · cases x with
    | inl x => trivial
    | inr z =>
      cases y with
      | inr u =>
        have impossible := ((completeContains_integer v p primitive source t d (Sum.inr z) u).mp h).1
        contradiction
      | inl y =>
        have hp := h.1.2.2
        change source.objects.identities.parent[y].map Sum.inl = some (Sum.inr z) at hp
        simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at hp
  · exact head_inside p primitive w t d ordinary ⟨h.1.2.1, h.2.1⟩

theorem deref_inside (p : Fin k)
    (w t : Nat) (d : Fin k)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    {x y : Completion o}
    (h : Clafer.Behavioral.InheritedReference.deref
      (SemanticsBridge.BehavioralStructural.interpret v.core).family
      ((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d x y) :
    x ∈ observedDomain w ∧ y ∈ observedDomain w := by
  obtain ⟨owner, _, _, raw⟩ := h
  cases x with
  | inr z => exact raw.elim
  | inl x =>
    refine ⟨trivial, ?_⟩
    cases y with
    | inl y => trivial
    | inr z => exact raw.2.2.2 ▸ fits x

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Static type filtering includes absent captured occurrences. Primitive type
filtering observes the complete integer type only inside the bounded universe. -/
theorem pool_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat) (d : Fin k) :
    Mixed.Unary rep.atoms {x | (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
      ((completeTrace v p source).identities.directType x) d ∧ x ∈ observedDomain w}
      ((pool v d).eval (schema v) w target.unfold e t) := by
  cases hd : integerDeclaration v d with
  | false =>
    apply Mixed.unary_congr (Mixed.of_objects_unary (rep.pool_meaning w e t d hd))
    intro x
    cases x with
    | inl x =>
      simp only [Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq, exists_eq_right,
        observedDomain_object, and_true, ancestor_iff]
      rfl
    | inr z =>
      have dp : p ≠ d := by
        intro eq
        have hi := (integerDeclaration_eq v p primitive d).mpr eq.symm
        rw [hd] at hi
        contradiction
      simp only [Set.mem_image, reduceCtorEq, and_false, exists_false, Set.mem_ofPred_eq]
      change False ↔ (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor p d ∧ _
      rw [primitive_ancestor v p d primitive]
      simp only [dp, false_and]
  | true =>
    have dp := (integerDeclaration_eq v p primitive d).mp hd
    subst d
    simp only [pool, hd, ↓reduceIte]
    apply Mixed.unary_congr (rep.ints_completed w positive small e t)
    intro x
    cases x with
    | inl x =>
      have ne : source.objects.identities.directType[x] ≠ p := by
        intro eq
        have ho := ordinary x
        rw [eq, hd] at ho
        contradiction
      simp only [Set.mem_ofPred_eq, reduceCtorEq, false_and, exists_false]
      change False ↔ (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor source.objects.identities.directType[x] p ∧ _
      rw [ancestor_primitive v p _ primitive shape]
      simp only [ne, false_and]
    | inr z =>
      simp only [Set.mem_ofPred_eq, Sum.inr.injEq]
      change (∃ a, z = a ∧ Backend.Alloy.fitsInt w a = true) ↔
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor p p ∧ Backend.Alloy.fitsInt w z = true
      constructor
      · rintro ⟨a, rfl, fits⟩
        exact ⟨.refl, fits⟩
      · rintro ⟨_, fits⟩
        exact ⟨z, rfl, fits⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
