module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersValues

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal

namespace Mixed

theorem unary_rows (h : Unary f S rows) : UnaryRows rows := by
  intro row hr
  obtain ⟨x, _, rfl⟩ := (h row).mp hr
  exact ⟨f x, rfl⟩

theorem unary_rowSet (h : Unary f S rows) : rowSet rows = f '' S := by
  ext a
  change [a] ∈ rows ↔ a ∈ f '' S
  rw [h]
  simp only [List.cons.injEq, and_true]
  exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩, fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩⟩
end Mixed

namespace IntegerObservation
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def extractionBody (range : IR.Expr.Interval) (r : Rel) :
    Backend.Alloy.Behavioral.Full.Value Integer :=
  ⟨[(.binary .conj (.mult .one r) (.subset r .ints), .scalar range.lower range.upper r)]⟩

theorem extractionBody_built (range : IR.Expr.Interval) (r : Rel) :
    Value.Built (extractionBody range r) := by
  intro g x hg
  simp only [extractionBody, List.mem_singleton, Prod.mk.injEq] at hg
  rw [hg.1]
  exact .binary .conj (.mult _ _) (.subset _ _)

theorem extractionBody_meaning (range : IR.Expr.Interval) (r : Rel) :
    Value.Meaning s w τ e t (extractionBody range r) n ↔
      n = .scalar range.lower range.upper r ∧
      (Formula.binary .conj (.mult .one r) (.subset r .ints)).Holds s w τ e t := by
  simp only [extractionBody, Value.Meaning, List.mem_singleton, Prod.mk.injEq]
  aesop

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Explicit extraction preserves its original singleton domain. The range
premise concerns source values and follows from the checked range derivation;
the target scalar fallback is never used for a defined source value. -/
theorem extract (labels : Fin o ↪ Nat)
    {source : Option (Set (Completion o))} {a : Backend.Alloy.Behavioral.Full.Value Rel}
    (ha : CollectionObservation s w τ e t (completionAtom labels) source a)
    (range : IR.Expr.Interval) (positive : 0 < w) (small : w ≤ 16)
    (bounds : ∀ S, source = some S → ∀ z, completeIntegers.extract S = some z →
      range.Contains z ∧ Backend.Alloy.fitsInt w z = true) :
    IntegerObservation s w τ e t (source.bind completeIntegers.extract)
      (Backend.Alloy.Behavioral.Full.integerExtract range a) := by
  change IntegerObservation s w τ e t _ (a.bind (extractionBody range))
  refine ⟨Value.bind_built a _ ha.built (extractionBody_built range), ?_, ?_⟩
  · intro n hn
    obtain ⟨r, hr, hn⟩ := (Value.bind_meaning a _ ha.built (extractionBody_built range)).mp hn
    obtain ⟨S, sourceS, _, rows⟩ := ha.sound r hr
    obtain ⟨rfl, guard⟩ := (extractionBody_meaning range r).mp hn
    rw [extract_guard r (Mixed.unary_rows rows) positive small, Mixed.unary_rowSet rows,
      completionAtom_extract] at guard
    obtain ⟨z, hz, fits⟩ := guard
    obtain ⟨⟨lo, hi⟩, _⟩ := bounds S sourceS z hz
    exact ⟨z, by simp [sourceS, hz], .scalar _ _ _,
      completed_extract_some labels S r (Mixed.unary_rows rows) (Mixed.unary_rowSet rows) hz lo hi fits⟩
  · intro z hz
    obtain ⟨S, sourceS, extractZ⟩ := Option.bind_eq_some_iff.mp hz
    obtain ⟨r, hr⟩ := ha.complete S sourceS
    obtain ⟨T, sourceT, _, rows⟩ := ha.sound r hr
    have same : T = S := Option.some.inj (sourceT.symm.trans sourceS)
    subst T
    refine ⟨.scalar range.lower range.upper r,
      (Value.bind_meaning a _ ha.built (extractionBody_built range)).mpr ⟨r, hr, ?_⟩⟩
    apply (extractionBody_meaning range r).mpr
    refine ⟨rfl, ?_⟩
    rw [extract_guard r (Mixed.unary_rows rows) positive small, Mixed.unary_rowSet rows,
      completionAtom_extract]
    exact ⟨z, extractZ, (bounds S sourceS z extractZ).2⟩

end IntegerObservation
end ClaferCompiler.Correctness.Behavioral.Full
