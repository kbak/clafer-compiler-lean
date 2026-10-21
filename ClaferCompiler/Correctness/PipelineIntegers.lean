module

public import ClaferCompiler.Correctness.PipelineAtoms
public import ClaferCompiler.SemanticsBridge.ExprObservation
public import Mathlib.Basic.Denumerable

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr SemanticsBridge.Expr

/-- Complete the mathematical integer domain on the common ambient carrier,
while fixing the finite observed integer values. Ordinary live objects remain
outside that domain; every other ambient atom belongs to it. The bijection is
proof-only and never used for executable source compilation. -/
theorem integer_completion (ordinary : Finset Atom)
    (ho : ∀ z, Atom.integer z ∉ ordinary) (observed : Finset Int) :
    ∃ R : FormalCD.IntegerRealization Atom,
      R.domain = {a | a ∉ ordinary} ∧ ∀ z ∈ observed, R.encode z = .integer z := by
  classical
  let : Countable Atom := atomCode_injective.countable
  let P := {a : Atom // a ∉ ordinary}
  let embed : Int → P := fun z => ⟨.integer z,ho z⟩
  have hembed : Function.Injective embed := by
    intro x y h
    exact Atom.integer.inj (congrArg Subtype.val h)
  let : Infinite P := Infinite.of_injective embed hembed
  obtain ⟨base⟩ : Nonempty (Int ≃ P) := nonempty_equiv_of_countable
  let : Fintype {z : Int // z ∈ observed} := Fintype.ofFinset observed (by intro z; rfl)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun z : {z : Int // z ∈ observed} => base z.val)
    (fun z : {z : Int // z ∈ observed} => embed z.val)
    (base.injective.comp Subtype.val_injective) (hembed.comp Subtype.val_injective)
  let e : Int ≃ P := base.trans σ
  let R : FormalCD.IntegerRealization Atom := {
    encode := ⟨fun z => (e z).val, Subtype.val_injective.comp e.injective⟩
    decode := fun a => if h : a ∉ ordinary then e.symm ⟨a,h⟩ else 0
    decode_encode := by
      intro z
      change (if h : (e z).val ∉ ordinary then e.symm ⟨(e z).val,h⟩ else 0) = z
      rw [dite_eq_left (e z).property]
      exact e.symm_apply_apply z }
  refine ⟨R, ?_, ?_⟩
  · ext a
    constructor
    · rintro ⟨z,rfl⟩
      exact (e z).property
    · intro ha
      refine ⟨e.symm ⟨a,ha⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨a,ha⟩)
  · intro z hz
    exact congrArg Subtype.val (hσ ⟨z,hz⟩)

/-- Extraction only inspects recorded finite values. Completing the primitive
carrier cannot change successful, failed or nonsingleton extraction there. -/
theorem completed_extraction (ordinary : Finset Atom)
    (ho : ∀ z, Atom.integer z ∉ ordinary) (observed : Finset Int)
    (R : FormalCD.IntegerRealization Atom) (domain : R.domain = {a | a ∉ ordinary})
    (fixed : ∀ z ∈ observed, R.encode z = .integer z) (S : Set Atom)
    (recorded : ∀ a ∈ S, a ∈ ordinary ∨ ∃ z ∈ observed, a = .integer z) :
    R.extract S = integers.extract S := by
  have values (z : Int) : R.extract S = some z ↔ integers.extract S = some z := by
    rw [R.extract_eq_some_iff, integers.extract_eq_some_iff]
    unfold FormalCD.IntegerRealization.Extracts
    constructor
    · intro hs
      have hm : R.encode z ∈ S := by rw [hs]; exact Set.mem_singleton _
      rcases recorded _ hm with hord | ⟨k,hk,he⟩
      · have hd : R.encode z ∈ R.domain := ⟨z,rfl⟩
        rw [domain] at hd
        exact (hd hord).elim
      · have hz : z = k := R.encode.injective (he.trans (fixed k hk).symm)
        subst k
        simpa only [fixed z hk, show integers.encode z = .integer z from rfl] using hs
    · intro hs
      have hm : Atom.integer z ∈ S := by rw [hs]; exact Set.mem_singleton _
      rcases recorded _ hm with hord | ⟨k,hk,he⟩
      · exact (ho z hord).elim
      · have hz : z = k := Atom.integer.inj he
        subst k
        simpa only [fixed z hk, show integers.encode z = .integer z from rfl] using hs
  cases hr : R.extract S with
  | none =>
    cases hi : integers.extract S with
    | none => rfl
    | some z => have := (values z).mpr hi; rw [hr] at this; cases this
  | some z => exact ((values z).mp hr).symm

/-- Pointwise encoder agreement on the inspected set suffices even when the
two full integer domains differ away from that set. -/
theorem extraction_on (R : FormalCD.IntegerRealization Atom) (S : Set Atom)
    (h : ∀ a ∈ S, ∀ z, a = R.encode z ↔ a = integers.encode z) :
    R.extract S = integers.extract S := by
  apply Option.ext
  intro z
  rw [R.extract_eq_some_iff,integers.extract_eq_some_iff]
  unfold FormalCD.IntegerRealization.Extracts
  constructor
  · intro hs
    have ha : R.encode z ∈ S := by rw [hs]; exact Set.mem_singleton _
    exact hs.trans (congrArg (fun a : Atom => ({a} : Set Atom)) ((h _ ha z).mp rfl))
  · intro hs
    have ha : integers.encode z ∈ S := by rw [hs]; exact Set.mem_singleton _
    exact hs.trans (congrArg (fun a : Atom => ({a} : Set Atom)) ((h _ ha z).mpr rfl))

end ClaferCompiler.Correctness.Pipeline
