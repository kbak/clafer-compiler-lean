module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersCoercion

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

namespace Extreme
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def better (op : IR.Behavioral.Primitive.Extreme) (candidate other : Int) : Bool :=
  match op with | .minimum => other < candidate | .maximum => candidate < other

def forbidden (op : IR.Behavioral.Primitive.Extreme) (range : IR.Expr.Interval) (z : Int) : Rel :=
  union (((integerCandidates range).filter (better op z)).map Rel.integer)

def guard (op : IR.Behavioral.Primitive.Extreme) (range : IR.Expr.Interval) (r : Rel) (z : Int) : Formula :=
  .binary .conj (.subset r .ints) (.binary .conj (.subset (.integer z) r)
    (.equal (.inter r (forbidden op range z)) (.empty .unary)))

def body (op : IR.Behavioral.Primitive.Extreme) (range : IR.Expr.Interval) (r : Rel) : Value Rel :=
  ⟨(.equal r (.empty .unary), .empty .unary) ::
    (integerCandidates range).map fun z => (guard op range r z, .integer z)⟩

theorem guard_built (op : IR.Behavioral.Primitive.Extreme) (range : IR.Expr.Interval) (r : Rel) (z : Int) :
    (guard op range r z).Built :=
  .binary .conj (.subset _ _) (.binary .conj (.subset _ _) (.equal _ _))

theorem body_built (op : IR.Behavioral.Primitive.Extreme) (range : IR.Expr.Interval) (r : Rel) :
    Value.Built (body op range r) := by
  intro g result member
  simp only [body, List.mem_cons, List.mem_map, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨z, _, eq, _⟩
  · exact .equal _ _
  · rw [← eq]; exact guard_built _ _ _ _

theorem range_fits (range : IR.Expr.Interval) (fits : range.fits w = true)
    {z : Int} (hz : range.Contains z) : Backend.Alloy.fitsInt w z = true := by
  simp only [IR.Expr.Interval.fits, decide_eq_true_eq] at fits
  simp only [Backend.Alloy.fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨fits.1, fits.2.1⟩, fits.2.2.2.1.trans hz.1⟩, hz.2.trans fits.2.2.2.2⟩

theorem integers_term (zs : List Int) : (union (zs.map Rel.integer)).Term :=
  union_term _ (by intro r hr; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr; exact .integer z) _ (.empty _)

theorem integer_rows (labels : Fin o ↪ Nat) (z : Int) (fits : Backend.Alloy.fitsInt w z = true) :
    Mixed.Unary (completionAtom labels) {Sum.inr z} ((Rel.integer z).eval s w τ e t) := by
  simpa [Rel.eval, Rel.integer, Rel.fold, RelAlgebra.step, relationAlgebra, fits] using
    Mixed.unary_singleton (f := completionAtom labels) (Sum.inr z)

theorem integers_rows (labels : Fin o ↪ Nat) (zs : List Int)
    (fits : ∀ z ∈ zs, Backend.Alloy.fitsInt w z = true) :
    Mixed.Unary (completionAtom labels) (Sum.inr '' {z | z ∈ zs})
      ((union (zs.map Rel.integer)).eval s w τ e t) := by
  intro row
  unfold union
  rw [union_rows _ (by intro r hr; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr; exact .integer z) _ (.empty _)]
  constructor
  · rintro (bad | ⟨r, hr, hrow⟩)
    · exact (List.not_mem_nil bad).elim
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
      obtain ⟨x, hx, he⟩ := (integer_rows labels z (fits z hz) row).mp hrow
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨Sum.inr z, ⟨z, hz, rfl⟩, he⟩
  · rintro ⟨x, ⟨z, hz, rfl⟩, he⟩
    exact Or.inr ⟨.integer z, List.mem_map.mpr ⟨z, hz, rfl⟩,
      (integer_rows labels z (fits z hz) row).mpr ⟨Sum.inr z, rfl, he⟩⟩

theorem better_before (op : IR.Behavioral.Primitive.Extreme) (z q : Int) :
    better op z q = false ↔ (SemanticsBridge.Behavioral.Primitive.extreme op).before z q := by
  cases op <;> simp [better, SemanticsBridge.Behavioral.Primitive.extreme,
    Clafer.Behavioral.Aggregate.Extreme.before]

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem guard_meaning (labels : Fin o ↪ Nat) (op : IR.Behavioral.Primitive.Extreme)
    (range : IR.Expr.Interval) (fits : range.fits w = true)
    (r : Rel) (term : r.Term) (rows : Mixed.Unary (completionAtom labels) S (r.eval s w τ e t))
    (bounds : ∀ z, Sum.inr z ∈ S → range.Contains z) (z : Int) (hz : range.Contains z) :
    (guard op range r z).Holds s w τ e t ↔
      S ⊆ completeIntegers.domain ∧ Sum.inr z ∈ S ∧
        ∀ q, Sum.inr q ∈ S → (SemanticsBridge.Behavioral.Primitive.extreme op).before z q := by
  have width : 0 < w ∧ w ≤ 16 := by
    simp only [IR.Expr.Interval.fits, decide_eq_true_eq] at fits
    exact ⟨fits.1, fits.2.1⟩
  have forbiddenRows := integers_rows (s := s) (τ := τ) (e := e) (t := t) labels
    ((integerCandidates range).filter (better op z)) (fun q hq => range_fits range fits
      ((integerCandidates_member _ _).mp (List.mem_filter.mp hq).1))
  have inter := Mixed.unary_inter (completionAtom labels).injective term (integers_term _)
    rows forbiddenRows
  unfold guard forbidden
  rw [Encoding.holds_and (.subset _ _) (.binary .conj (.subset _ _) (.equal _ _)),
    Encoding.holds_and (.subset _ _) (.equal _ _), subset_ints labels rows width.1 width.2
      (fun q hq => range_fits range fits (bounds q hq)),
    Mixed.unary_subset (completionAtom labels).injective (integer_rows labels z (range_fits range fits hz)) rows,
    Mixed.unary_equal (completionAtom labels).injective inter (Mixed.unary_empty (f := completionAtom labels))]
  simp only [Set.singleton_subset_iff]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro empty q hq
    apply (better_before op z q).mp
    apply Bool.eq_false_iff.mpr
    intro better
    have member : Sum.inr q ∈ S ∩ Sum.inr '' {i | i ∈ (integerCandidates range).filter (Extreme.better op z)} :=
      ⟨hq, q, List.mem_filter.mpr ⟨(integerCandidates_member _ _).mpr (bounds q hq), better⟩, rfl⟩
    rw [empty] at member
    exact member
  · intro best
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, q, hq, rfl⟩
    have noBetter := (better_before op z q).mpr (best q hx)
    have yesBetter := (List.mem_filter.mp hq).2
    rw [noBetter] at yesBetter
    contradiction

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem select_singleton (op : IR.Behavioral.Primitive.Extreme) (S : Set (Completion o))
    (finite : S.Finite) (typed : S ⊆ completeIntegers.domain) (z : Int) :
    (SemanticsBridge.Behavioral.Primitive.extreme op).select completeIntegers S = some {Sum.inr z} ↔
      Sum.inr z ∈ S ∧ ∀ q, Sum.inr q ∈ S → (SemanticsBridge.Behavioral.Primitive.extreme op).before z q := by
  rw [Clafer.Behavioral.Aggregate.select_finite _ _ finite typed, Option.some.injEq]
  constructor
  · intro eq
    have member : Sum.inr z ∈ {x | x ∈ S ∧ ∀ y ∈ S,
        (SemanticsBridge.Behavioral.Primitive.extreme op).before (completeIntegers.decode x) (completeIntegers.decode y)} := by
      rw [eq]; exact Set.mem_singleton _
    exact ⟨member.1, fun q hq => member.2 _ hq⟩
  · rintro ⟨hz, best⟩
    ext x
    constructor
    · rintro ⟨hx, hxBest⟩
      obtain ⟨q, rfl⟩ := (completeIntegers_domain _).mp (typed hx)
      have h₁ := hxBest (Sum.inr z) hz
      have h₂ := best q hx
      have eq : q = z := by
        cases op <;> simp only [SemanticsBridge.Behavioral.Primitive.extreme,
          Clafer.Behavioral.Aggregate.Extreme.before, completeIntegers_decode] at h₁ h₂ <;> omega
      exact congrArg Sum.inr eq
    · rintro rfl
      refine ⟨hz, ?_⟩
      intro y hy
      obtain ⟨q, rfl⟩ := (completeIntegers_domain _).mp (typed hy)
      exact best q hy

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem observation (labels : Fin o ↪ Nat) (op : IR.Behavioral.Primitive.Extreme)
    (range : IR.Expr.Interval) (fits : range.fits w = true)
    (r : Rel) (term : r.Term) (rows : Mixed.Unary (completionAtom labels) S (r.eval s w τ e t))
    (bounds : ∀ z, Sum.inr z ∈ S → range.Contains z) :
    CollectionObservation s w τ e t (completionAtom labels)
      ((SemanticsBridge.Behavioral.Primitive.extreme op).select completeIntegers S) (body op range r) := by
  classical
  have finite := Mixed.unary_finite (completionAtom labels).injective rows
  have emptyRows : Mixed.Unary (completionAtom labels) ∅ ((Rel.empty .unary).eval s w τ e t) := Mixed.unary_empty
  refine ⟨body_built op range r, ?_, ?_⟩
  · rintro result ⟨g, member, holds⟩
    simp only [body, List.mem_cons, List.mem_map, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩
    · have empty := (Mixed.unary_equal (completionAtom labels).injective rows emptyRows).mp holds
      subst S
      exact ⟨∅, Clafer.Behavioral.Aggregate.select_empty _ _, .empty _, emptyRows⟩
    · have hz := (integerCandidates_member _ _).mp hz
      obtain ⟨typed, hzS, best⟩ := (guard_meaning labels op range fits r term rows bounds z hz).mp holds
      exact ⟨{Sum.inr z}, (select_singleton op S finite typed z).mpr ⟨hzS, best⟩,
        .integer z, integer_rows labels z (range_fits range fits hz)⟩
  · intro T selected
    have typed := ((Clafer.Behavioral.Aggregate.select_defined_iff _ _ _).mp ⟨T, selected⟩).2
    by_cases empty : S = ∅
    · refine ⟨.empty .unary, .equal r (.empty .unary), List.mem_cons_self, ?_⟩
      exact (Mixed.unary_equal (completionAtom labels).injective rows emptyRows).mpr empty
    · obtain ⟨x, hx, selectedX⟩ := Clafer.Behavioral.Aggregate.select_singleton
        (SemanticsBridge.Behavioral.Primitive.extreme op) completeIntegers finite typed
          (Set.nonempty_iff_ne_empty.mpr empty)
      obtain ⟨z, rfl⟩ := (completeIntegers_domain _).mp (typed hx)
      have best := ((select_singleton op S finite typed z).mp selectedX).2
      refine ⟨.integer z, guard op range r z, List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨z, (integerCandidates_member _ _).mpr (bounds z hx), rfl⟩), ?_⟩
      exact (guard_meaning labels op range fits r term rows bounds z (bounds z hx)).mpr ⟨typed, hx, best⟩

end Extreme
namespace CollectionObservation
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The concrete min/max lowering preserves empty results and the original
integer-domain failure. Its complete enumerated interval must fit, including
candidates absent from the operand, as checked by range analysis. -/
theorem extreme (labels : Fin o ↪ Nat) (op : IR.Behavioral.Primitive.Extreme)
    {source : Option (Set (Completion o))} {a : Value Rel}
    (ha : CollectionObservation s w τ e t (completionAtom labels) source a)
    (range : IR.Expr.Interval) (fits : range.fits w = true)
    (bounds : ∀ S, source = some S → ∀ z, Sum.inr z ∈ S → range.Contains z) :
    CollectionObservation s w τ e t (completionAtom labels)
      (source.bind ((SemanticsBridge.Behavioral.Primitive.extreme op).select completeIntegers))
      (collectionExtreme op range a) := by
  change CollectionObservation s w τ e t _ _ (a.bind (Extreme.body op range))
  refine ⟨Value.bind_built a _ ha.built (Extreme.body_built op range), ?_, ?_⟩
  · intro result meaning
    obtain ⟨r, hr, bodyMeaning⟩ := (Value.bind_meaning a _ ha.built (Extreme.body_built op range)).mp meaning
    obtain ⟨S, sourceS, term, rows⟩ := ha.sound r hr
    obtain ⟨T, selected, resultTerm, resultRows⟩ :=
      (Extreme.observation labels op range fits r term rows (bounds S sourceS)).sound result bodyMeaning
    exact ⟨T, by simp [sourceS, selected], resultTerm, resultRows⟩
  · intro T hT
    obtain ⟨S, sourceS, selected⟩ := Option.bind_eq_some_iff.mp hT
    obtain ⟨r, hr⟩ := ha.complete S sourceS
    obtain ⟨S', sourceS', term, rows⟩ := ha.sound r hr
    have same : S' = S := Option.some.inj (sourceS'.symm.trans sourceS)
    subst S'
    obtain ⟨result, bodyMeaning⟩ :=
      (Extreme.observation labels op range fits r term rows (bounds S sourceS)).complete T selected
    exact ⟨result, (Value.bind_meaning a _ ha.built (Extreme.body_built op range)).mpr ⟨r, hr, bodyMeaning⟩⟩

end CollectionObservation

end ClaferCompiler.Correctness.Behavioral.Full
