module

public import ClaferCompiler.IR.Behavioral.RangeRules
public import ClaferCompiler.SemanticsBridge.BehavioralArithmetic
public import Mathlib.Data.Set.Card

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Ranges
open IR.Behavioral.Expression.Ranges
open IR.Expr IR.BehavioralArithmetic
open scoped BigOperators

/-- Bounds constrain finite observations and their mathematical integer members.
They impose neither integer typing nor definedness nor truth. -/
structure CollectionBound (R : Clafer.Constraints.IntegerRealization U)
    (b : CollectionEstimate) (S : Set U) : Prop where
  finite : S.Finite
  card : S.ncard ≤ b.budget
  values : ∀ x ∈ S, x ∈ R.domain → b.values.Contains (R.decode x)

universe u
variable {U : Type u} {R : Clafer.Constraints.IntegerRealization U}
  {a b : CollectionEstimate} {S T : Set U}

theorem CollectionBound.empty : CollectionBound R ⟨0, ⟨0, 0⟩⟩ ∅ :=
  ⟨Set.finite_empty, by simp, by simp⟩

theorem CollectionBound.subset (h : CollectionBound R a S) (sub : T ⊆ S) :
    CollectionBound R a T :=
  ⟨h.finite.subset sub, (Set.ncard_le_ncard sub h.finite).trans h.card,
    fun x hx => h.values x (sub hx)⟩

theorem CollectionBound.union (ha : CollectionBound R a S) (hb : CollectionBound R b T) :
    CollectionBound R (IR.Behavioral.Expression.Ranges.union a b) (S ∪ T) := by
  refine ⟨ha.finite.union hb.finite, ?_, ?_⟩
  · exact (Set.ncard_union_le S T).trans (Nat.add_le_add ha.card hb.card)
  · intro x hx ht
    rcases hx with hx | hx
    · have h := ha.values x hx ht
      exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
    · have h := hb.values x hx ht
      exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

theorem CollectionBound.inter (ha : CollectionBound R a S) (hb : CollectionBound R b T) :
    CollectionBound R (intersection a b) (S ∩ T) := by
  refine ⟨ha.finite.inter_of_left T, ?_, fun x hx => ha.values x hx.1⟩
  exact le_min ((Set.ncard_le_ncard Set.inter_subset_left ha.finite).trans ha.card)
    ((Set.ncard_le_ncard Set.inter_subset_right hb.finite).trans hb.card)

theorem CollectionBound.diff (ha : CollectionBound R a S) :
    CollectionBound R a (S \ T) := ha.subset Set.sdiff_subset

theorem CollectionBound.selected_left (ha : CollectionBound R a S) :
    CollectionBound R (selected a b) S := by
  refine ⟨ha.finite, ha.card.trans (Nat.le_max_left _ _), ?_⟩
  intro x hx ht
  have h := ha.values x hx ht
  exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩

theorem CollectionBound.selected_right (hb : CollectionBound R b T) :
    CollectionBound R (selected a b) T := by
  refine ⟨hb.finite, hb.card.trans (Nat.le_max_right _ _), ?_⟩
  intro x hx ht
  have h := hb.values x hx ht
  exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

theorem CollectionBound.singleton_member (ha : CollectionBound R a S) (hx : x ∈ S) :
    CollectionBound R (singleton a) {x} :=
  ⟨Set.finite_singleton _, by simp [IR.Behavioral.Expression.Ranges.singleton], fun y hy => by
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ha.values _ hx⟩

theorem CollectionBound.integer (h : r.Contains z) :
    CollectionBound R ⟨1, r⟩ {R.encode z} := by
  refine ⟨Set.finite_singleton _, by simp, ?_⟩
  intro x hx _
  obtain rfl := Set.mem_singleton_iff.mp hx
  simpa only [R.decode_encode] using h

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem CollectionBound.extreme (ha : CollectionBound R a S)
    (op : Clafer.Behavioral.Aggregate.Extreme) (h : op.select R S = some T) :
    CollectionBound R ⟨min 1 a.budget, a.values⟩ T := by
  have sub := Clafer.Behavioral.Aggregate.select_subset op R h
  have base := ha.subset sub
  refine ⟨base.finite, le_min ?_ base.card, base.values⟩
  by_cases ne : S.Nonempty
  · obtain ⟨_, typed⟩ := (Clafer.Behavioral.Aggregate.select_defined_iff op R S).mp ⟨T, h⟩
    obtain ⟨x, _, hs⟩ := Clafer.Behavioral.Aggregate.select_singleton op R ha.finite typed ne
    have eq : T = {x} := Option.some.inj (h.symm.trans hs)
    simp [eq]
  · have eq : S = ∅ := Set.not_nonempty_iff_eq_empty.mp ne
    subst S
    have eq : T = ∅ := Option.some.inj (h.symm.trans (Clafer.Behavioral.Aggregate.select_empty op R))
    simp [eq]

/-- Reuse the finite-list arithmetic bridge on a semantic observation. The
finite enumeration is proof-only and preserves each distinct integer object. -/
theorem CollectionBound.coerce (ha : CollectionBound R a S)
    (h : Clafer.Behavioral.IntegerObservation.coerce R S = some z) :
    (setSumRange a.budget a.values).Contains z := by
  classical
  have typed := ((Clafer.Behavioral.IntegerObservation.coerce_defined_iff R S).mp ⟨z, h⟩).2
  let values := ha.finite.toFinset.toList.map R.decode
  have observed : SemanticsBridge.BehavioralArithmetic.observed R values = S := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hy : y ∈ S := ha.finite.mem_toFinset.mp (Finset.mem_toList.mp hy)
      simpa only [R.encode_decode (typed hy)] using hy
    · intro hx
      exact ⟨R.decode x, List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩, R.encode_decode (typed hx)⟩
  have eq := SemanticsBridge.BehavioralArithmetic.coerce_agrees R values
  rw [observed, h] at eq
  have hz : IR.BehavioralArithmetic.coerce values = z := Option.some.inj eq.symm
  rw [← hz]
  apply SemanticsBridge.BehavioralArithmetic.observation_range
  · simpa only [values, List.length_map, Finset.length_toList, ← Set.ncard_eq_toFinset_card S ha.finite] using ha.card
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    have hx : x ∈ S := by simpa using hx
    exact ha.values x hx (typed hx)

theorem CollectionBound.extract (ha : CollectionBound R a S) (h : R.extract S = some z) :
    a.values.Contains z := by
  have eq := (R.extract_eq_some_iff S z).mp h
  change S = {R.encode z} at eq
  have hz : R.encode z ∈ S := by simp [eq]
  simpa only [R.decode_encode] using ha.values (R.encode z) hz ⟨z, rfl⟩

theorem CollectionBound.cardinality (ha : CollectionBound R a S) :
    (countRange a.budget).Contains (S.ncard : Int) :=
  SemanticsBridge.BehavioralArithmetic.count_range ha.card

end ClaferCompiler.Correctness.Behavioral.Full.Ranges
