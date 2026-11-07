module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersValues

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem integerCandidates_member (r : IR.Expr.Interval) (z : Int) :
    z ∈ integerCandidates r ↔ r.Contains z := by
  simp only [integerCandidates, List.mem_map, List.mem_range, IR.Expr.Interval.Contains]
  constructor
  · rintro ⟨i, hi, rfl⟩
    change r.lower ≤ r.lower + (i : Int) ∧ r.lower + (i : Int) ≤ r.upper
    constructor <;> omega
  · intro h
    refine ⟨(z - r.lower).toNat, by omega, ?_⟩
    change r.lower + ((z - r.lower).toNat : Int) = z
    omega

namespace CollectionObservation
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def conversionBody (range : IR.Expr.Interval) (n : Integer) : Value Rel :=
  ⟨(integerCandidates range).map fun z => (.compare .eq n (.literal z), .integer z)⟩

theorem conversionBody_built (range : IR.Expr.Interval) (n : Integer) :
    Full.Value.Built (conversionBody range n) := by
  intro g r hr
  obtain ⟨z, _, equal⟩ := List.mem_map.mp hr
  cases equal
  exact .compare _ _ _

theorem conversionBody_meaning (range : IR.Expr.Interval) (n : Integer) (value : Int)
    (he : n.eval s w τ e t = some value) :
    Full.Value.Meaning s w τ e t (conversionBody range n) r ↔
      range.Contains value ∧ Backend.Alloy.fitsInt w value = true ∧ r = .integer value := by
  change (∃ g, (g, r) ∈ (integerCandidates range).map
    (fun z => (Formula.compare .eq n (.literal z), Rel.integer z)) ∧ g.Holds s w τ e t) ↔ _
  constructor
  · rintro ⟨g, hg, holds⟩
    obtain ⟨z, hz, eq⟩ := List.mem_map.mp hg
    cases eq
    change ∃ x y, n.eval s w τ e t = some x ∧ Backend.Alloy.boundedInt w z = some y ∧
      Backend.Alloy.Comparison.eq.holds x y = true at holds
    obtain ⟨x, y, hx, hy, equal⟩ := holds
    have xv := Option.some.inj (hx.symm.trans he)
    have yz : y = z := by
      unfold Backend.Alloy.boundedInt at hy
      split at hy
      · exact (Option.some.inj hy).symm
      · contradiction
    have xy : x = y := by simpa [Backend.Alloy.Comparison.holds] using equal
    subst x; subst y; subst z
    exact ⟨(integerCandidates_member _ _).mp hz, (Backend.Alloy.boundedInt_some_iff _ _).mp hy, rfl⟩
  · rintro ⟨bounds, fits, rfl⟩
    refine ⟨.compare .eq n (.literal value),
      List.mem_map.mpr ⟨value, (integerCandidates_member _ _).mpr bounds, rfl⟩, ?_⟩
    change ∃ x y, n.eval s w τ e t = some x ∧ Backend.Alloy.boundedInt w value = some y ∧
      Backend.Alloy.Comparison.eq.holds x y = true
    exact ⟨value, value, he, (Backend.Alloy.boundedInt_some_iff _ _).mpr fits, by simp [Backend.Alloy.Comparison.holds]⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem integer (labels : Fin o ↪ Nat)
    {source : Option Int} {a : Value Integer}
    (ha : IntegerObservation s w τ e t source a)
    (range : IR.Expr.Interval)
    (bounds : ∀ z, source = some z → range.Contains z ∧ Backend.Alloy.fitsInt w z = true) :
    CollectionObservation s w τ e t (completionAtom labels) (source.map fun z => {Sum.inr z})
      (integerCollection range a) := by
  change CollectionObservation s w τ e t _ _ (a.bind (conversionBody range))
  refine ⟨Full.Value.bind_built a _ ha.built (conversionBody_built range), ?_, ?_⟩
  · intro r hr
    obtain ⟨n, hn, hr⟩ := (Full.Value.bind_meaning a _ ha.built (conversionBody_built range)).mp hr
    obtain ⟨z, hz, _, he⟩ := ha.sound n hn
    obtain ⟨_, fits, rfl⟩ := (conversionBody_meaning range n z he).mp hr
    refine ⟨{Sum.inr z}, by simp [hz], .integer z, ?_⟩
    simpa [Rel.eval, Rel.integer, Rel.fold, RelAlgebra.step, relationAlgebra, fits] using
      Mixed.unary_singleton (f := completionAtom labels) (Sum.inr z)
  · intro S hS
    obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.mp hS
    obtain ⟨n, hn⟩ := ha.complete z hz
    obtain ⟨i, hi, _, he⟩ := ha.sound n hn
    have same : i = z := Option.some.inj (hi.symm.trans hz)
    subst i
    refine ⟨.integer z, (Full.Value.bind_meaning a _ ha.built (conversionBody_built range)).mpr ⟨n, hn, ?_⟩⟩
    exact (conversionBody_meaning range n z he).mpr ⟨(bounds z hz).1, (bounds z hz).2, rfl⟩
end CollectionObservation
end ClaferCompiler.Correctness.Behavioral.Full
