module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Representation
public import ClaferCompiler.SemanticsBridge.BehavioralStructural
public import ClaferCompiler.SemanticsBridge.Behavioral.Trace
public import Clafer.Behavioral.IntegerObservation

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open IR.BehavioralStructural

/-- Finite observed occurrences and the complete mathematical integer universe
are different summands. Equal scalar targets never identify occurrences. -/
abbrev Completion (o : Nat) := Fin o ⊕ Int

-- [impl->req~compiler-trace-assurance~1]
def completeIntegers : Clafer.Constraints.IntegerRealization (Completion o) where
  encode := ⟨Sum.inr, Sum.inr_injective⟩
  decode := Sum.elim (fun _ => 0) id
  decode_encode := fun _ => rfl

@[simp] theorem completeIntegers_encode (z : Int) :
    (completeIntegers (o := o)).encode z = Sum.inr z := rfl

@[simp] theorem completeIntegers_decode (z : Int) :
    (completeIntegers (o := o)).decode (Sum.inr z) = z := rfl

@[simp] theorem completeIntegers_domain (x : Completion o) :
    x ∈ (completeIntegers (o := o)).domain ↔ ∃ z, x = Sum.inr z := by
  simp [FormalCD.IntegerRealization.domain, completeIntegers, eq_comm]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Completion never replaces the primitive domain with the bounded Analyzer
integer pool. Only observations of this domain may be restricted. -/
theorem completeIntegers_infinite :
    (completeIntegers (o := o)).domain.Infinite := by
  exact Set.infinite_range_of_injective (completeIntegers (o := o)).encode.injective

def completeIdentities (p : Fin k) (l : ObservedLasso k o steps) :
    Clafer.Behavioral.Identities (Fin k) (Completion o) where
  root := Sum.inl l.objects.identities.root
  directType := Sum.elim (fun x => l.objects.identities.directType[x]) (fun _ => p)
  parent := Sum.elim (fun x => (l.objects.identities.parent[x]).map Sum.inl)
    (fun _ => some (Sum.inl l.objects.identities.root))

-- [impl->req~compiler-trace-assurance~1]
/-- Scalar rows contribute a source link precisely on a live occurrence of a
declaration whose explicit reference target is the integer declaration. Object
rows remain visible even when invalid, so completion cannot hide a bad link. -/
def completeTrace (v : Validated k) (p : Fin k) (l : ObservedLasso k o steps) :
    Clafer.Behavioral.Trace (Fin k) (Completion o) where
  identities := completeIdentities p l
  live t := {x | match x with
    | .inl x => (l.objects.at t).live[x] = true
    | .inr _ => True}
  deref t d x y := match x, y with
    | .inl x, .inl y => (d, x, y) ∈ (l.objects.at t).references
    | .inl x, .inr z => (v.core.structural.get d).reference.target = some p ∧
        (l.objects.at t).live[x] = true ∧
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
          l.objects.identities.directType[x] d ∧ (l.valuesAt t)[x] = z
    | .inr _, _ => False

@[simp] theorem complete_live_object (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (x : Fin o) :
    Sum.inl x ∈ (completeTrace v p l).live t ↔ (l.objects.at t).live[x] = true := Iff.rfl

@[simp] theorem complete_live_integer (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (z : Int) :
    Sum.inr z ∈ (completeTrace v p l).live t := trivial

@[simp] theorem complete_parent_object (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (x y : Fin o) :
    (completeTrace v p l).identities.parent (Sum.inl x) = some (Sum.inl y) ↔
      l.objects.identities.parent[x] = some y := by
  simp [completeTrace, completeIdentities, Option.map_eq_some_iff]

@[simp] theorem complete_parent_integer (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (z : Int) :
    (completeTrace v p l).identities.parent (Sum.inr z) =
      some (Sum.inl l.objects.identities.root) := rfl

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completeHead_object (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x : Fin o) :
    Sum.inl x ∈ ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ↔
    (l.objects.at t).live[x] = true ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        l.objects.identities.directType[x] d := Iff.rfl

theorem primitive_super_none (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) :
    (SemanticsBridge.BehavioralStructural.interpret v.core).family.super p = none := by
  have hp : (SemanticsBridge.BehavioralStructural.interpret v.core).family.origin p =
      .primitive .int := by
    simp [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret,
      SemanticsBridge.Structural.origin, primitive]
  exact (SemanticsBridge.BehavioralStructural.validated_wellFormed v).primitive_shape p _ hp |>.2.2

theorem primitive_ancestor (v : Validated k) (p d : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) :
    (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor p d ↔ p = d := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | @head x y edge _ _ =>
      have : (SemanticsBridge.BehavioralStructural.interpret v.core).family.super x = some y := edge
      rw [primitive_super_none v x primitive] at this
      contradiction
  · rintro rfl; exact .refl

theorem ancestor_primitive (v : Validated k) (p d : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (shape : PrimitiveShape v) :
    (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor d p ↔ d = p := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail y z _ edge _ =>
      exact ((shape z primitive).2.2.2.2.1 y edge).elim
  · rintro rfl; exact .refl

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completeHead_integer (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (z : Int) :
    Sum.inr z ∈ ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ↔ p = d := by
  change (True ∧ (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor p d) ↔ _
  simp only [true_and, primitive_ancestor v p d primitive]

theorem completeHead_primitive (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (l : ObservedLasso k o steps)
    (nonprimitive : ∀ x : Fin o, l.objects.identities.directType[x] ≠ p) (t : Nat) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head p =
      completeIntegers.domain := by
  ext x
  cases x with
  | inl x =>
    simp only [completeHead_object, ancestor_primitive v p _ primitive shape,
      completeIntegers_domain, Sum.inl_ne_inr, exists_false, iff_false, not_and]
    exact fun _ => nonprimitive x
  | inr z => simp [completeHead_integer v p primitive]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completeContains_objects (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x y : Fin o) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains
        d (Sum.inl x) (Sum.inl y) ↔
    ((l.objects.at t).live[x] = true ∧ (l.objects.at t).live[y] = true ∧
      l.objects.identities.parent[y] = some x) ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        l.objects.identities.directType[y] d ∧
      (v.core.structural.get d).parent ≠ none := by
  simp only [Clafer.Behavioral.Trace.raw, Clafer.Behavioral.Trace.ParentAt,
    complete_live_object, complete_parent_object]
  rfl

theorem completeContains_integer (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x : Completion o) (z : Int) :
    ((completeTrace v p l).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains
        d x (Sum.inr z) ↔
      x = Sum.inl l.objects.identities.root ∧
        (l.objects.at t).live[l.objects.identities.root] = true ∧ p = d := by
  have hp : (v.core.structural.get p).parent = some v.core.structural.root :=
    (v.checked.2.2.2.2.2.1 p primitive).1
  simp only [Clafer.Behavioral.Trace.raw, Clafer.Behavioral.Trace.ParentAt,
    complete_parent_integer, Option.some.injEq]
  constructor
  · rintro ⟨⟨hx, _, he⟩, ha, _⟩
    subst x
    exact ⟨rfl, hx, (primitive_ancestor v p d primitive).mp ha⟩
  · rintro ⟨rfl, hx, rfl⟩
    exact ⟨⟨hx, trivial, rfl⟩, .refl, by simp [SemanticsBridge.BehavioralStructural.interpret,
      SemanticsBridge.Structural.interpret, hp]⟩

@[simp] theorem completeDeref_objects (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x y : Fin o) :
    (completeTrace v p l).deref t d (Sum.inl x) (Sum.inl y) ↔
      (d, x, y) ∈ (l.objects.at t).references := Iff.rfl

@[simp] theorem completeDeref_integer (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (x : Fin o) (z : Int) :
    (completeTrace v p l).deref t d (Sum.inl x) (Sum.inr z) ↔
      (v.core.structural.get d).reference.target = some p ∧
        (l.objects.at t).live[x] = true ∧
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
          l.objects.identities.directType[x] d ∧ (l.valuesAt t)[x] = z := Iff.rfl

@[simp] theorem completeDeref_integer_source (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps) (t : Nat) (d : Fin k) (z : Int) (y : Completion o) :
    ¬ (completeTrace v p l).deref t d (Sum.inr z) y := by
  cases y <;> exact id

theorem primitive_ne_root (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) :
    p ≠ v.core.structural.root := by
  intro eq
  have root := v.checked.1.2.1 v.core.structural.root
  rw [eq, root.mpr rfl] at primitive
  contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Lifts the six actual identity conditions on finite nonprimitive occurrences.
The new primitive identities have their canonical type and fixed root parent. -/
theorem completeIdentities_valid (v : Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (l : ObservedLasso k o steps)
    (objects : Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core)
      (SemanticsBridge.Behavioral.trace l.objects)) :
    Clafer.Behavioral.Structural.IdentitiesValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p l) := by
  constructor
  · exact objects.root_type
  · intro x hx
    cases x with
    | inl x => exact congrArg Sum.inl (objects.root_only x hx)
    | inr z => exact (primitive_ne_root v p primitive hx).elim
  · intro x
    cases x with
    | inl x => exact objects.concrete x
    | inr z => exact (shape p primitive).1
  · change (l.objects.identities.parent[l.objects.identities.root]).map Sum.inl = none
    have h : l.objects.identities.parent[l.objects.identities.root] = none := objects.root_parent
    rw [h]; rfl
  · intro x hx
    cases x with
    | inl x =>
      obtain ⟨q, hq⟩ := objects.parent_exists x (fun eq => hx (congrArg Sum.inl eq))
      change l.objects.identities.parent[x] = some q at hq
      exact ⟨Sum.inl q, by change (l.objects.identities.parent[x]).map Sum.inl = _; rw [hq]; rfl⟩
    | inr z => exact ⟨Sum.inl l.objects.identities.root, rfl⟩
  · intro x q hq
    cases x with
    | inl x =>
      change (l.objects.identities.parent[x]).map Sum.inl = some q at hq
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact objects.parent_typed x y hy
    | inr z =>
      have he : Sum.inl l.objects.identities.root = q := Option.some.inj hq
      subst q
      refine ⟨v.core.structural.root, (v.checked.2.2.2.2.2.1 p primitive).1, ?_⟩
      change (SemanticsBridge.BehavioralStructural.interpret v.core).Ancestor
        l.objects.identities.directType[l.objects.identities.root] _
      have ht : l.objects.identities.directType[l.objects.identities.root] = v.core.structural.root :=
        objects.root_type
      rw [ht]; exact .refl

theorem complete_root_live (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps)
    (root : ∀ t, (l.objects.at t).live[l.objects.identities.root] = true) :
    ∀ t, (completeTrace v p l).identities.root ∈ (completeTrace v p l).live t := root

theorem complete_parent_live (v : Validated k) (p : Fin k)
    (l : ObservedLasso k o steps)
    (root : ∀ t, (l.objects.at t).live[l.objects.identities.root] = true)
    (parents : ∀ t (x y : Fin o), (l.objects.at t).live[x] = true →
      l.objects.identities.parent[x] = some y → (l.objects.at t).live[y] = true) :
    ∀ t x q, x ∈ (completeTrace v p l).live t →
      (completeTrace v p l).identities.parent x = some q → q ∈ (completeTrace v p l).live t := by
  intro t x q hx hq
  cases x with
  | inl x =>
    change (l.objects.identities.parent[x]).map Sum.inl = some q at hq
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hq
    exact parents t x y hx hy
  | inr z =>
    have he : Sum.inl l.objects.identities.root = q := Option.some.inj hq
    subst q
    exact root t

end ClaferCompiler.Correctness.Behavioral.Full
