module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletion
public import Mathlib.Data.Set.Card

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open scoped BigOperators

-- [impl->req~compiler-trace-assurance~1]
/-- The same labels are used at every time, for every occurrence and its captured
uses. Mathematical integer values are mapped identically, never by object labels. -/
def completionAtom (labels : Fin o ↪ Nat) : Completion o ↪ Temporal.Atom where
  toFun := Sum.elim (fun x => .object (labels x)) Temporal.Atom.integer
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (labels.injective (Temporal.Atom.object.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Temporal.Atom.integer.inj h)

@[simp] theorem completionAtom_object (labels : Fin o ↪ Nat) (x : Fin o) :
    completionAtom labels (Sum.inl x) = .object (labels x) := rfl

@[simp] theorem completionAtom_integer (labels : Fin o ↪ Nat) (z : Int) :
    completionAtom labels (Sum.inr z) = .integer z := rfl

def atomIntegers : Clafer.Constraints.IntegerRealization Temporal.Atom where
  encode := ⟨Temporal.Atom.integer, fun _ _ h => Temporal.Atom.integer.inj h⟩
  decode
    | .integer z => z
    | .object _ => 0
  decode_encode := fun _ => rfl

@[simp] theorem completionAtom_domain (labels : Fin o ↪ Nat) (x : Completion o) :
    completionAtom labels x ∈ atomIntegers.domain ↔ x ∈ completeIntegers.domain := by
  cases x with
  | inl x => simp [FormalCD.IntegerRealization.domain, atomIntegers, completeIntegers]
  | inr z => exact ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨z, rfl⟩⟩

@[simp] theorem completionAtom_decode (labels : Fin o ↪ Nat) (x : Completion o) :
    atomIntegers.decode (completionAtom labels x) = completeIntegers.decode x := by
  cases x <;> rfl

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Implicit conversion preserves distinct targets, including the empty sum and
undefinedness on infinite or mixed observations. This uses upstream conversion
and Mathlib finite image/sum laws, with no new arithmetic evaluator. -/
theorem completionAtom_coerce (labels : Fin o ↪ Nat) (S : Set (Completion o)) :
    Clafer.Behavioral.IntegerObservation.coerce atomIntegers (completionAtom labels '' S) =
      Clafer.Behavioral.IntegerObservation.coerce completeIntegers S := by
  classical
  by_cases hf : S.Finite
  · have imageFinite := hf.image (completionAtom labels)
    by_cases ht : S ⊆ completeIntegers.domain
    · have imageTyped : completionAtom labels '' S ⊆ atomIntegers.domain := by
        rintro _ ⟨x, hx, rfl⟩
        exact (completionAtom_domain labels x).mpr (ht hx)
      rw [Clafer.Behavioral.IntegerObservation.coerce_finite _ imageFinite imageTyped,
        Clafer.Behavioral.IntegerObservation.coerce_finite _ hf ht]
      congr 1
      rw [Set.Finite.toFinset_image (completionAtom labels) hf imageFinite]
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun x _ => completionAtom_decode labels x)
      · intro x _ y _ h
        exact (completionAtom labels).injective h
    · obtain ⟨x, hx, bad⟩ := Set.not_subset.mp ht
      rw [Clafer.Behavioral.IntegerObservation.coerce_wrong_domain _
          (Set.mem_image_of_mem _ hx) (by simpa using bad),
        Clafer.Behavioral.IntegerObservation.coerce_wrong_domain _ hx bad]
  · have imageInfinite : (completionAtom labels '' S).Infinite := by
      exact Set.Infinite.image (completionAtom labels).injective.injOn hf
    rw [Clafer.Behavioral.IntegerObservation.coerce_infinite _ imageInfinite,
      Clafer.Behavioral.IntegerObservation.coerce_infinite _ hf]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completionAtom_extract (labels : Fin o ↪ Nat) (S : Set (Completion o)) :
    atomIntegers.extract (completionAtom labels '' S) = completeIntegers.extract S := by
  apply Option.ext
  intro z
  rw [FormalCD.IntegerRealization.extract_eq_some_iff,
    FormalCD.IntegerRealization.extract_eq_some_iff]
  change completionAtom labels '' S = {Temporal.Atom.integer z} ↔ S = {Sum.inr z}
  have singleton : completionAtom labels '' {Sum.inr z} = {Temporal.Atom.integer z} := by
    simp
  rw [← singleton]
  exact Set.image_injective.mpr (completionAtom labels).injective |>.eq_iff

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem integerAtoms_member (width : Nat) (positive : 0 < width) (z : Int) :
    Temporal.Atom.integer z ∈ Temporal.integerAtoms width ↔
      minInt width ≤ z ∧ z ≤ maxInt width := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have power : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  simp only [Temporal.integerAtoms, List.mem_map, List.mem_range,
    Temporal.Atom.integer.injEq, minInt, maxInt, Nat.succ_sub_one]
  change (∃ i : Nat, i < 2 ^ (w + 1) ∧ -((2 ^ w : Nat) : Int) + (i : Int) = z) ↔
    -((2 ^ w : Nat) : Int) ≤ z ∧ z ≤ ((2 ^ w : Nat) : Int) - 1
  constructor
  · rintro ⟨i, hi, eq⟩
    rw [power] at hi
    omega
  · rintro ⟨lo, hi⟩
    refine ⟨(z + ((2 ^ w : Nat) : Int)).toNat, ?_, ?_⟩
    · rw [power]
      omega
    · omega

theorem integerAtoms_fits (width : Nat) (positive : 0 < width) (small : width ≤ 16) (z : Int) :
    Temporal.Atom.integer z ∈ Temporal.integerAtoms width ↔ fitsInt width z = true := by
  rw [integerAtoms_member width positive]
  simp [fitsInt, show 1 ≤ width by omega, small]

/-- Only used observations are restricted. The full completed primitive extent
is infinite and is deliberately not asserted to satisfy this condition. -/
def ObservationFits (width : Nat) (S : Set (Completion o)) : Prop :=
  S.Finite ∧ ∀ z : Int, Sum.inr z ∈ S → fitsInt width z = true

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem primitive_extent_not_fits (width : Nat) :
    ¬ ObservationFits width (completeIntegers (o := o)).domain :=
  fun h => completeIntegers_infinite h.1

theorem primitive_extent_coerce_undefined :
    Clafer.Behavioral.IntegerObservation.coerce (completeIntegers (o := o))
      completeIntegers.domain = none :=
  Clafer.Behavioral.IntegerObservation.coerce_infinite _ completeIntegers_infinite

def restrictObservation (labels : Fin o ↪ Nat) (width : Nat) (S : Set (Completion o)) :
    Set Temporal.Atom := completionAtom labels '' {x ∈ S | match x with
      | .inl _ => True
      | .inr z => fitsInt width z = true}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem restrictObservation_lossless (labels : Fin o ↪ Nat) (width : Nat)
    (S : Set (Completion o)) (fits : ObservationFits width S) :
    restrictObservation labels width S = completionAtom labels '' S := by
  apply congrArg (Set.image (completionAtom labels))
  ext x
  cases x with
  | inl x => simp
  | inr z => exact ⟨And.left, fun h => ⟨h, fits.2 z h⟩⟩

theorem restrictObservation_finite (labels : Fin o ↪ Nat) (width : Nat)
    (S : Set (Completion o)) (fits : ObservationFits width S) :
    (restrictObservation labels width S).Finite := by
  rw [restrictObservation_lossless labels width S fits]
  exact fits.1.image _

theorem restrictObservation_card (labels : Fin o ↪ Nat) (width : Nat)
    (S : Set (Completion o)) (fits : ObservationFits width S) :
    (restrictObservation labels width S).ncard = S.ncard := by
  rw [restrictObservation_lossless labels width S fits]
  exact Set.ncard_image_of_injective _ (completionAtom labels).injective

theorem restrictObservation_coerce (labels : Fin o ↪ Nat) (width : Nat)
    (S : Set (Completion o)) (fits : ObservationFits width S) :
    Clafer.Behavioral.IntegerObservation.coerce atomIntegers
      (restrictObservation labels width S) =
      Clafer.Behavioral.IntegerObservation.coerce completeIntegers S := by
  rw [restrictObservation_lossless labels width S fits, completionAtom_coerce]

theorem restrictObservation_extract (labels : Fin o ↪ Nat) (width : Nat)
    (S : Set (Completion o)) (fits : ObservationFits width S) :
    atomIntegers.extract (restrictObservation labels width S) = completeIntegers.extract S := by
  rw [restrictObservation_lossless labels width S fits, completionAtom_extract]

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Multiplicity of equal values remains multiplicity of distinct heads. -/
theorem completionAtom_distinct_occurrences (labels : Fin o ↪ Nat)
    (x y : Fin o) (z : Int) (different : x ≠ y) :
    (completionAtom labels (Sum.inl x), completionAtom labels (Sum.inr z)) ≠
      (completionAtom labels (Sum.inl y), completionAtom labels (Sum.inr z)) := by
  intro eq
  exact different (Sum.inl.inj ((completionAtom labels).injective (Prod.mk.inj eq).1))

end ClaferCompiler.Correctness.Behavioral.Full
