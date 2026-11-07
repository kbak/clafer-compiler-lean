module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersExtraction
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersFolds
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsSelectionSources

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open scoped BigOperators

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem subset_ints (labels : Fin o ↪ Nat) (rows : Mixed.Unary (completionAtom labels) S (r.eval s w τ e t))
    (positive : 0 < w) (small : w ≤ 16)
    (fit : ∀ z, Sum.inr z ∈ S → Backend.Alloy.fitsInt w z = true) :
    (Formula.subset r .ints).Holds s w τ e t ↔ S ⊆ completeIntegers.domain := by
  change (∀ row ∈ r.eval s w τ e t, row ∈ (Rel.ints).eval s w τ e t) ↔ _
  constructor
  · intro h x hx
    have mem := h [completionAtom labels x] ((rows _).mpr ⟨x, hx, rfl⟩)
    change [completionAtom labels x] ∈ (integerAtoms w).map (fun a => [a]) at mem
    obtain ⟨atom, ha, eq⟩ := List.mem_map.mp mem
    have eq : atom = completionAtom labels x := by simpa using eq
    subst atom
    obtain ⟨i, _, eq⟩ := List.mem_map.mp ha
    apply (completionAtom_domain labels x).mp
    exact ⟨_, eq⟩
  · intro typed row hr
    obtain ⟨x, hx, rfl⟩ := (rows row).mp hr
    obtain ⟨z, eq⟩ := typed hx
    change Sum.inr z = x at eq
    subst x
    change [Atom.integer z] ∈ (integerAtoms w).map (fun a => [a])
    exact List.mem_map.mpr ⟨.integer z, (integerAtoms_fits w positive small z).mpr (fit z hx), rfl⟩

theorem coerce_source_list {U : Type} {S : Set U} (R : Clafer.Constraints.IntegerRealization U)
    (xs : List U) (nodup : xs.Nodup) (represented : ∀ x, x ∈ xs ↔ x ∈ S)
    (typed : S ⊆ R.domain) :
    Clafer.Behavioral.IntegerObservation.coerce R S = some (xs.map R.decode).sum := by
  classical
  have finite : S.Finite := (List.finite_toSet xs).subset (fun _ h => (represented _).mpr h)
  have eq : finite.toFinset = xs.toFinset := by ext x; simpa using (represented x).symm
  rw [Clafer.Behavioral.IntegerObservation.coerce_finite R finite typed, eq,
    List.sum_toFinset R.decode nodup]

namespace IntegerObservation
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def coercionTerms (range : IR.Expr.Interval) (heads : List Rel) : List Integer :=
  heads.map fun entry => .scalar range.lower range.upper entry

def coercionGuard (r : Rel) (heads : List Rel) : Formula :=
  .binary .conj (.subset r .ints) (.equal r (Backend.Alloy.Behavioral.Full.union heads))

def coercionBody (aliases : List Rel) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate)
    (r : Rel) : Value Integer :=
  (Value.selections aliases r estimate.budget).bind fun heads =>
    Value.guard (coercionGuard r heads) (integerFold .sum ((coercionTerms estimate.values heads).map Value.pure))

theorem coercionGuard_built (r : Rel) (heads : List Rel) : (coercionGuard r heads).Built :=
  .binary .conj (.subset _ _) (.equal _ _)

theorem coercionBody_built (aliases : List Rel) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate)
    (r : Rel) : Full.Value.Built (coercionBody aliases estimate r) := by
  apply Full.Value.bind_built _ _ (Full.Value.selections_built _ _ _)
  intro heads
  exact Full.Value.guard_built _ _ (coercionGuard_built r heads) (IntegerFold.pure_built _ _)

theorem coercionBody_meaning (aliases : List Rel) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate)
    (r : Rel) :
    Full.Value.Meaning s w τ e t (coercionBody aliases estimate r) n ↔
      ∃ heads, Full.Value.Meaning s w τ e t (Value.selections aliases r estimate.budget) heads ∧
        (coercionGuard r heads).Holds s w τ e t ∧
        n = IntegerFold.term .sum (coercionTerms estimate.values heads) (.literal 0) := by
  unfold coercionBody
  rw [Full.Value.bind_meaning _ _ (Full.Value.selections_built _ _ _)
    (fun heads => Full.Value.guard_built _ _ (coercionGuard_built r heads) (IntegerFold.pure_built _ _))]
  simp only [Full.Value.guard_meaning _ _ (coercionGuard_built _ _) (IntegerFold.pure_built _ _),
    IntegerFold.pure_meaning, IntegerFold.initial]
  rfl

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem coercionBody_source (labels : Fin o ↪ Nat) (S : Set (Completion o))
    (aliases : List Rel) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate) (r : Rel)
    (rows : Mixed.Unary (completionAtom labels) S (r.eval s w τ e t))
    (positive : 0 < w) (small : w ≤ 16)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ x ∈ S, ∃ entry ∈ aliases,
      Mixed.Unary (completionAtom labels) {x} (entry.eval s w τ e t))
    (bound : S.ncard ≤ estimate.budget)
    (values : ∀ z, Sum.inr z ∈ S → estimate.values.Contains z)
    (fits : ∀ z, Sum.inr z ∈ S → Backend.Alloy.fitsInt w z = true)
    (sumFits : (IR.BehavioralArithmetic.setSumRange estimate.budget estimate.values).fits w = true) :
    IntegerObservation s w τ e t
      (Clafer.Behavioral.IntegerObservation.coerce completeIntegers S)
      (coercionBody aliases estimate r) := by
  refine ⟨coercionBody_built aliases estimate r, ?_, ?_⟩
  · intro n hn
    obtain ⟨heads, selected, guard, rfl⟩ := (coercionBody_meaning aliases estimate r).mp hn
    obtain ⟨typedTarget, _⟩ := (Encoding.holds_and (.subset _ _) (.equal _ _)).mp guard
    have typed := (subset_ints labels rows positive small fits).mp typedTarget
    obtain ⟨decode, singles, nodup, source⟩ := Selection.source_heads (Sum.inr 0)
      (completionAtom labels).injective rows terms cover bound selected
    let zs := (heads.map decode).map completeIntegers.decode
    have size : zs.length ≤ estimate.budget := by
      simpa only [zs, List.length_map,
        source_selection_cardinality (completionAtom labels).injective rows terms cover bound selected] using bound
    have valueBound : ∀ z ∈ zs, estimate.values.Contains z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have member := (source x).mp hx
      obtain ⟨i, eq⟩ := typed member
      change Sum.inr i = x at eq
      subst x
      exact values i member
    have represented : List.Forall₂ (fun n z => Arithmetic.Term n ∧ n.eval s w τ e t = some z)
        (coercionTerms estimate.values heads) zs := by
      dsimp only [coercionTerms, zs]
      rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro head hh
      have member : decode head ∈ S := (source _).mp (List.mem_map.mpr ⟨head, hh, rfl⟩)
      obtain ⟨i, eq⟩ := typed member
      change Sum.inr i = decode head at eq
      refine ⟨.scalar _ _ _, ?_⟩
      have singleton := (singles head hh).2
      change (Integer.scalar estimate.values.lower estimate.values.upper head).eval s w τ e t =
        some (completeIntegers.decode (decode head))
      rw [← eq] at singleton member ⊢
      change (Integer.scalar estimate.values.lower estimate.values.upper head).eval s w τ e t = some i
      exact scalar_eval_singleton head (by simpa using Mixed.unary_singleton_rows singleton)
        (values i member).1 (values i member).2 (fits i member)
    have fit0 : Backend.Alloy.fitsInt w 0 = true :=
      IntegerFold.prefixes_fit .sum estimate.values sumFits size valueBound [] (by simp)
    obtain ⟨term, eval⟩ := IntegerFold.term_eval .sum represented (.literal 0)
      ((Backend.Alloy.boundedInt_some_iff w 0).mpr fit0)
      (IntegerFold.prefixes_fit .sum estimate.values sumFits size valueBound)
    refine ⟨zs.sum, coerce_source_list completeIntegers _ nodup source typed, term, ?_⟩
    change _ = some (zs.foldl (· + ·) 0) at eval
    rwa [← List.sum_eq_foldl] at eval
  · intro z hz
    have typed := ((Clafer.Behavioral.IntegerObservation.coerce_defined_iff completeIntegers S).mp ⟨z, hz⟩).2
    have rowCover : ∀ row ∈ r.eval s w τ e t,
        ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row] := by
      intro row hr
      obtain ⟨x, hx, rfl⟩ := (rows row).mp hr
      obtain ⟨entry, he, hsingle⟩ := cover x hx
      exact ⟨entry, he, Mixed.unary_singleton_rows hsingle⟩
    have rowBound : (r.eval s w τ e t).toFinset.card ≤ estimate.budget := by
      rw [Mixed.unary_card (completionAtom labels).injective rows]
      exact bound
    obtain ⟨heads, selected, _, _, equal⟩ := Selection.selections_complete aliases r estimate.budget terms rowCover rowBound
    refine ⟨_, (coercionBody_meaning aliases estimate r).mpr ⟨heads, selected, ?_, rfl⟩⟩
    apply (Encoding.holds_and (.subset _ _) (.equal _ _)).mpr
    exact ⟨(subset_ints labels rows positive small fits).mpr typed, fun row => (equal row).symm⟩

theorem collectionBind {U : Type} {f : U → Atom} {source : Option (Set U)} {a : Value Rel}
    (ha : CollectionObservation s w τ e t f source a)
    (sourceBody : Set U → Option Int) (targetBody : Rel → Value Integer)
    (bodyBuilt : ∀ r, Full.Value.Built (targetBody r))
    (body : ∀ S r, source = some S → r.Term → Mixed.Unary f S (r.eval s w τ e t) →
      IntegerObservation s w τ e t (sourceBody S) (targetBody r)) :
    IntegerObservation s w τ e t (source.bind sourceBody) (a.bind targetBody) := by
  refine ⟨Full.Value.bind_built a targetBody ha.built bodyBuilt, ?_, ?_⟩
  · intro n hn
    obtain ⟨r, hr, hn⟩ := (Full.Value.bind_meaning a targetBody ha.built bodyBuilt).mp hn
    obtain ⟨S, hs, ht, hrows⟩ := ha.sound r hr
    obtain ⟨z, hz, hnt, hne⟩ := (body S r hs ht hrows).sound n hn
    exact ⟨z, by simp [hs, hz], hnt, hne⟩
  · intro z hz
    obtain ⟨S, hs, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain ⟨r, hr⟩ := ha.complete S hs
    obtain ⟨T, ht, term, rows⟩ := ha.sound r hr
    have same : T = S := Option.some.inj (ht.symm.trans hs)
    subst T
    obtain ⟨n, hn⟩ := (body S r hs term rows).complete z hz
    exact ⟨n, (Full.Value.bind_meaning a targetBody ha.built bodyBuilt).mpr ⟨r, hr, hn⟩⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem coerce (labels : Fin o ↪ Nat) {source : Option (Set (Completion o))} {a : Value Rel}
    (ha : CollectionObservation s w τ e t (completionAtom labels) source a)
    (aliases : List Rel) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate)
    (positive : 0 < w) (small : w ≤ 16)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ S, source = some S → ∀ x ∈ S, ∃ entry ∈ aliases,
      Mixed.Unary (completionAtom labels) {x} (entry.eval s w τ e t))
    (bound : ∀ S, source = some S → S.ncard ≤ estimate.budget)
    (values : ∀ S, source = some S → ∀ z, Sum.inr z ∈ S → estimate.values.Contains z)
    (fits : ∀ S, source = some S → ∀ z, Sum.inr z ∈ S → Backend.Alloy.fitsInt w z = true)
    (sumFits : (IR.BehavioralArithmetic.setSumRange estimate.budget estimate.values).fits w = true) :
    IntegerObservation s w τ e t
      (source.bind (Clafer.Behavioral.IntegerObservation.coerce completeIntegers))
      (a.bind (coercionBody aliases estimate)) :=
  collectionBind ha _ _ (coercionBody_built aliases estimate)
    (fun S r hs _ rows => coercionBody_source labels S aliases estimate r rows positive small terms
      (cover S hs) (bound S hs) (values S hs) (fits S hs) sumFits)

end IntegerObservation
end ClaferCompiler.Correctness.Behavioral.Full
