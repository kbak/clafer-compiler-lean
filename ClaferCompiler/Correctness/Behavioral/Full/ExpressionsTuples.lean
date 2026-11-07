module

public import ClaferCompiler.Correctness.Behavioral.Full.Expressions
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsSets
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsSelectionSources
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionFormula

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

namespace Tuples

-- The executable disjointness filter uses the derived structural comparison.
-- Reuse Lean's checked lawful-BEq derivation before interpreting `contains`.
deriving instance ReflBEq, LawfulBEq for Backend.Alloy.Arity
deriving instance ReflBEq, LawfulBEq for RelOp
deriving instance ReflBEq, LawfulBEq for Rel
attribute [local instance] Classical.propDecidable

def prepend (x : Rel) (xs : Vector Rel n) : Vector Rel (n + 1) :=
  Vector.ofFn (Fin.cases x (fun i => xs[i]))
def tail (xs : Vector Rel (n + 1)) : Vector Rel n :=
  Vector.ofFn (fun i => xs[i.succ])

@[simp] theorem prepend_zero (x : Rel) (xs : Vector Rel n) : (prepend x xs)[0] = x := by
  simp [prepend]
@[simp] theorem prepend_succ (x : Rel) (xs : Vector Rel n) (i : Fin n) :
    (prepend x xs)[i.succ] = xs[i] := by simp [prepend]
@[simp] theorem prepend_get_succ (x : Rel) (xs : Vector Rel n) (i : Nat) (hi : i < n) :
    (prepend x xs)[i + 1] = xs[i] := prepend_succ x xs ⟨i, hi⟩
@[simp] theorem tail_get (xs : Vector Rel (n + 1)) (i : Fin n) :
    (tail xs)[i] = xs[i.succ] := by simp [tail]
@[simp] theorem tail_get_nat (xs : Vector Rel (n + 1)) (i : Nat) (hi : i < n) :
    (tail xs)[i] = xs[i + 1] := tail_get xs ⟨i, hi⟩
@[simp] theorem tail_prepend (x : Rel) (xs : Vector Rel n) : tail (prepend x xs) = xs := by
  apply Vector.ext
  intro i hi
  rw [tail_get_nat _ i hi, prepend_get_succ _ _ i hi]
theorem prepend_tail (xs : Vector Rel (n + 1)) : prepend xs[0] (tail xs) = xs := by
  apply Vector.ext
  intro i hi
  cases i with
  | zero => exact prepend_zero _ _
  | succ i => rw [prepend_get_succ _ _ i (by omega), tail_get_nat _ i (by omega)]

theorem prepend_injective (xs : Vector Rel n) : Function.Injective (fun x => prepend x xs) := by
  intro x y eq
  simpa using congrArg (fun (v : Vector Rel (n + 1)) => v[0]) eq

theorem mem_toList (xs : Vector Rel n) (x : Rel) : x ∈ xs.toList ↔ ∃ i : Fin n, xs[i] = x := by
  simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem, Fin.exists_iff, Fin.getElem_fin]

def Admitted (domain : List Rel) (disjoint : Bool) (xs : Vector Rel n) : Prop :=
  (∀ i : Fin n, xs[i] ∈ domain) ∧ (disjoint = true → Function.Injective (fun i : Fin n => xs[i]))

theorem admitted_prepend (domain : List Rel) (disjoint : Bool) (x : Rel) (xs : Vector Rel n) :
    Admitted domain disjoint (prepend x xs) ↔
      Admitted domain disjoint xs ∧ x ∈ domain ∧ (disjoint = true → x ∉ xs.toList) := by
  constructor
  · rintro ⟨members, distinct⟩
    refine ⟨⟨fun i => by simpa using members i.succ, ?_⟩, by simpa using members 0, ?_⟩
    · intro h i j eq
      apply Fin.succ_injective
      apply distinct h
      simpa using eq
    · intro h member
      obtain ⟨i, hi⟩ := (mem_toList xs x).mp member
      have eq := distinct h (a₁ := i.succ) (a₂ := 0) (by simpa using hi)
      exact Fin.succ_ne_zero i eq
  · rintro ⟨⟨members, distinct⟩, hx, fresh⟩
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using members j
    · intro h i j eq
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          have same : xs[j] = x := by simpa using eq.symm
          exact (fresh h ((mem_toList xs x).mpr ⟨j, same⟩)).elim
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have same : xs[i] = x := by simpa using eq
          exact (fresh h ((mem_toList xs x).mpr ⟨i, same⟩)).elim
        | succ j => exact congrArg Fin.succ (distinct h (by simpa using eq))

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Membership is all ordered assignments, with optional identity distinctness.
Arity zero has exactly its empty assignment. -/
theorem mem_tuples (domain : List Rel) (disjoint : Bool) (xs : Vector Rel arity) :
    xs ∈ Expressions.tuples domain disjoint arity ↔ Admitted domain disjoint xs := by
  induction arity with
  | zero =>
    have eq : xs = #v[] := Vector.ext (by omega)
    subst xs
    simp [Expressions.tuples, Admitted, Function.Injective]
  | succ n ih =>
    change xs ∈ (Expressions.tuples domain disjoint n).flatMap
      (fun ys => (domain.filter fun x => !disjoint || !ys.toList.contains x).map (fun x => prepend x ys)) ↔ _
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨ys, hys, x, ⟨hx, fresh⟩, rfl⟩
      apply (admitted_prepend domain disjoint x ys).mpr
      refine ⟨(ih ys).mp hys, hx, ?_⟩
      cases disjoint with
      | false => simp
      | true => simpa only [Bool.not_true, Bool.false_or, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not, true_implies] using fresh
    · intro h
      have hs := (admitted_prepend domain disjoint xs[0] (tail xs)).mp (prepend_tail xs ▸ h)
      refine ⟨tail xs, (ih _).mpr hs.1, xs[0], ⟨hs.2.1, ?_⟩, prepend_tail xs⟩
      cases disjoint with
      | false => simp
      | true => simpa only [Bool.not_true, Bool.false_or, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not, true_implies] using hs.2.2

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem nodup (domain : List Rel) (distinct : domain.Nodup) (disjoint : Bool) (arity : Nat) :
    (Expressions.tuples domain disjoint arity).Nodup := by
  induction arity with
  | zero => simp [Expressions.tuples]
  | succ n ih =>
    change ((Expressions.tuples domain disjoint n).flatMap
      (fun ys => (domain.filter fun x => !disjoint || !ys.toList.contains x).map (fun x => prepend x ys))).Nodup
    rw [List.nodup_flatMap]
    constructor
    · intro xs _
      exact (distinct.filter _).map (prepend_injective xs)
    · apply ih.imp
      intro xs ys different
      apply List.disjoint_left.mpr
      intro zs hxs hys
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hxs
      obtain ⟨y, _, eq⟩ := List.mem_map.mp hys
      exact different (by simpa using congrArg tail eq.symm)

/-- Runtime lexical position zero is the last authored binder. This reversal
turns each runtime vector into the source's left-to-right ordered assignment. -/
def assignment (decode : Rel → U) (xs : Vector Rel arity) : Fin arity → U :=
  fun i => decode xs[i.rev]

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem assignment_image {U : Type} (decode : Rel → U) (domain : List Rel)
    (injective : Set.InjOn decode {r | r ∈ domain}) (S : Set U)
    (represented : ∀ x, x ∈ S ↔ ∃ r ∈ domain, decode r = x)
    (disjoint : Bool) (arity : Nat) :
    assignment decode '' {xs | xs ∈ Expressions.tuples domain disjoint arity} =
      SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S := by
  classical
  ext a
  constructor
  · rintro ⟨xs, hx, rfl⟩
    obtain ⟨members, distinct⟩ := (mem_tuples domain disjoint xs).mp hx
    refine ⟨fun i => (represented _).mpr ⟨xs[i.rev], members i.rev, rfl⟩, ?_⟩
    intro h i j eq
    apply Fin.rev_involutive.injective
    exact distinct h (injective (members i.rev) (members j.rev) eq)
  · rintro ⟨members, distinct⟩
    choose r hr he using fun i => (represented (a i)).mp (members i)
    let xs : Vector Rel arity := Vector.ofFn (fun i => r i.rev)
    have value : assignment decode xs = a := by
      funext i
      simp only [assignment, xs, Fin.getElem_fin, Vector.getElem_ofFn]
      change decode (r i.rev.rev) = a i
      simpa only [Fin.rev_rev] using he i
    refine ⟨xs, (mem_tuples domain disjoint xs).mpr ⟨?_, ?_⟩, value⟩
    · intro i
      simpa [xs] using hr i.rev
    · intro h i j eq
      apply Fin.rev_involutive.injective
      apply distinct h
      simpa only [xs, Fin.getElem_fin, Vector.getElem_ofFn, ← he i.rev, ← he j.rev] using congrArg decode eq

theorem assignment_injective {U : Type} (decode : Rel → U) (domain : List Rel)
    (injective : Set.InjOn decode {r | r ∈ domain}) (disjoint : Bool) (arity : Nat) :
    Set.InjOn (assignment decode)
      {xs | xs ∈ Expressions.tuples domain disjoint arity} := by
  intro xs hxs ys hys eq
  have mx := ((mem_tuples domain disjoint xs).mp hxs).1
  have my := ((mem_tuples domain disjoint ys).mp hys).1
  apply Vector.ext
  intro i hi
  apply injective (mx ⟨i, hi⟩) (my ⟨i, hi⟩)
  simpa [assignment] using congrFun eq (⟨i, hi⟩ : Fin arity).rev

@[simp] theorem assignment_rev (decode : Rel → U) (xs : Vector Rel arity) (i : Fin arity) :
    assignment decode xs i.rev = decode xs[i] := by simp only [assignment, Fin.rev_rev]

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem context_extend {U : Type} {s : Schema} {w : Nat} {τ : Trace} {f : U → Atom}
    {A : Set U} {c : Expressions.Context n} {ρ : Clafer.Behavioral.Environment U n}
    {e : Environment} (hc : Sets.ContextRows s w τ f A c ρ e)
    (decode : Rel → U) (xs : Vector Rel arity) (estimate : IR.Behavioral.Expression.Ranges.CollectionEstimate)
    (terms : ∀ i : Fin arity, (xs[i]).Term)
    (entries : ∀ (i : Fin arity) t, Mixed.Unary f {decode xs[i]} ((xs[i]).eval s w τ e t))
    (inside : ∀ i : Fin arity, decode xs[i] ∈ A) :
    Sets.ContextRows s w τ f A (c.extend xs estimate)
      (SemanticsBridge.Behavioral.Grouped.extend ρ arity (assignment decode xs)) e := by
  refine ⟨hc.this_term, hc.this, hc.this_inside, ?_, ?_, ?_⟩
  · intro i
    change (if h : i.val < arity then xs[i.val] else c.lexical.lookup ⟨i.val - arity, by omega⟩).Term
    split
    · exact terms ⟨i.val, ‹i.val < arity›⟩
    · exact hc.lookup_term _
  · intro i t
    unfold Expressions.Context.extend SemanticsBridge.Behavioral.Grouped.extend
    dsimp only
    split
    · rename_i hi
      have rev : (⟨arity - (i.val + 1), by omega⟩ : Fin arity) = (⟨i.val, hi⟩ : Fin arity).rev := rfl
      rw [rev, assignment_rev]
      exact entries ⟨i.val, hi⟩ t
    · exact hc.lookup _ t
  · intro i
    unfold SemanticsBridge.Behavioral.Grouped.extend
    dsimp only
    split
    · rename_i hi
      have rev : (⟨arity - (i.val + 1), by omega⟩ : Fin arity) = (⟨i.val, hi⟩ : Fin arity).rev := rfl
      rw [rev, assignment_rev]
      exact Set.singleton_subset_iff.mpr (inside ⟨i.val, hi⟩)
    · exact hc.lookup_inside _

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Counting distinct runtime vectors equals counting distinct satisfying
source assignments, including tuples with repeated entries when permitted. -/
theorem countP_assignments {U : Type} (decode : Rel → U) (domain : List Rel)
    (distinct : domain.Nodup) (injective : Set.InjOn decode {r | r ∈ domain}) (S : Set U)
    (represented : ∀ x, x ∈ S ↔ ∃ r ∈ domain, decode r = x)
    (disjoint : Bool) (arity : Nat) (P : (Fin arity → U) → Prop) :
    (Expressions.tuples domain disjoint arity).countP (fun xs => decide (P (assignment decode xs))) =
      {a | a ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S ∧ P a}.ncard := by
  classical
  let source := {xs | xs ∈ Expressions.tuples domain disjoint arity ∧ P (assignment decode xs)}
  have image : assignment decode '' source =
      {a | a ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S ∧ P a} := by
    ext a
    rw [← assignment_image decode domain injective S represented disjoint arity]
    constructor
    · rintro ⟨xs, ⟨hx, hp⟩, rfl⟩
      exact ⟨⟨xs, hx, rfl⟩, hp⟩
    · rintro ⟨⟨xs, hx, rfl⟩, hp⟩
      exact ⟨xs, ⟨hx, hp⟩, rfl⟩
  rw [← image, (assignment_injective decode domain injective disjoint arity).mono
    (fun _ hx => hx.1) |>.ncard_image]
  have eq : source = ↑((Expressions.tuples domain disjoint arity).filter
      (fun xs => decide (P (assignment decode xs)))).toFinset := by
    ext xs
    simp [source]
  rw [eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((nodup domain distinct disjoint arity).filter _)]
  exact List.countP_eq_length_filter

/-- Cardinal form of the source's whole-assignment counting quantifier. -/
theorem count_eval {U : Type} (q : IR.Behavioral.Grouped.Count) (S : Set U)
    (finite : S.Finite) (P : U → Prop) :
    (SemanticsBridge.Behavioral.Grouped.count q).eval S P ↔
      match q with
      | .one => {x | x ∈ S ∧ P x}.ncard = 1
      | .lone => {x | x ∈ S ∧ P x}.ncard ≤ 1 := by
  cases q with
  | one =>
    rw [Set.ncard_eq_one]
    change (∃! x, x ∈ S ∧ P x) ↔ ∃ x, {y | y ∈ S ∧ P y} = {x}
    constructor
    · rintro ⟨x, hx, unique⟩
      refine ⟨x, Set.ext (fun y => ?_)⟩
      exact ⟨fun hy => unique y hy, fun hy => (Set.mem_singleton_iff.mp hy) ▸ hx⟩
    · rintro ⟨x, eq⟩
      refine ⟨x, ?_, ?_⟩
      · have hx := eq.symm ▸ Set.mem_singleton x
        exact hx
      · intro y hy
        exact Set.mem_singleton_iff.mp (eq ▸ hy)
  | lone =>
    rw [Set.ncard_le_one (finite.subset (fun _ h => h.1))]
    change (∀ x ∈ S, ∀ y ∈ S, P x → P y → x = y) ↔ _
    constructor
    · exact fun h x hx y hy => h x hx.1 y hy.1 hx.2 hy.2
    · exact fun h x hx y hy px py => h x ⟨hx, px⟩ y ⟨hy, py⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The actual generated one/lone circuit agrees with source grouped counting
once its emitted body formulas agree on the represented tuple assignments. -/
theorem countTruth_assignments {U : Type} (decode : Rel → U) (domain : List Rel)
    (distinct : domain.Nodup) (injective : Set.InjOn decode {r | r ∈ domain}) (S : Set U)
    (represented : ∀ x, x ∈ S ↔ ∃ r ∈ domain, decode r = x)
    (disjoint : Bool) (arity : Nat) (q : IR.Behavioral.Grouped.Count)
    (body : Vector Rel arity → Formula) (P : (Fin arity → U) → Prop)
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (built : ∀ xs ∈ Expressions.tuples domain disjoint arity, (body xs).Built)
    (agree : ∀ xs ∈ Expressions.tuples domain disjoint arity,
      (body xs).Holds s w τ e t ↔ P (assignment decode xs)) :
    (Expressions.countTruth q ((Expressions.tuples domain disjoint arity).map body)).Holds s w τ e t ↔
      (SemanticsBridge.Behavioral.Grouped.count q).eval
        (SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S) P := by
  classical
  have finite : (SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S).Finite := by
    rw [← assignment_image decode domain injective S represented disjoint arity]
    exact (List.finite_toSet _).image _
  rw [countTruth_correct q _ (by
    intro p hp
    obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hp
    exact built xs hx), count_eval q _ finite P]
  have count : trueCount s w τ e t ((Expressions.tuples domain disjoint arity).map body) =
      {a | a ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S ∧ P a}.ncard := by
    unfold trueCount
    rw [List.countP_map, ← countP_assignments decode domain distinct injective S represented disjoint arity P]
    exact List.countP_congr (by intro xs hx; simpa only [Function.comp_apply, decide_eq_true_eq] using agree xs hx)
  cases q <;> rw [count]

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The actual alias selection procedure supplies the distinct assignment
representation consumed by the generated grouped counting circuit. -/
theorem selected_count {U : Type} (fallback : U) {s : Schema} {w : Nat} {τ : Trace}
    {e : Environment} {t : Nat} {f : U → Atom} {S : Set U} {aliases chosen : List Rel}
    {domain : Rel} {budget : Nat} (hf : Function.Injective f)
    (rows : Mixed.Unary f S (domain.eval s w τ e t))
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ x ∈ S, ∃ entry ∈ aliases, Mixed.Unary f {x} (entry.eval s w τ e t))
    (bound : S.ncard ≤ budget)
    (selected : Value.Meaning s w τ e t (Value.selections aliases domain budget) chosen) :
    ∃ decode : Rel → U,
      (∀ entry ∈ chosen, entry.Term ∧ Mixed.Unary f {decode entry} (entry.eval s w τ e t)) ∧
      ∀ (disjoint : Bool) (arity : Nat) (q : IR.Behavioral.Grouped.Count)
        (body : Vector Rel arity → Formula) (P : (Fin arity → U) → Prop),
        (∀ xs ∈ Expressions.tuples chosen disjoint arity, (body xs).Built) →
        (∀ xs ∈ Expressions.tuples chosen disjoint arity,
          (body xs).Holds s w τ e t ↔ P (assignment decode xs)) →
        ((Expressions.countTruth q ((Expressions.tuples chosen disjoint arity).map body)).Holds s w τ e t ↔
          (SemanticsBridge.Behavioral.Grouped.count q).eval
            (SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S) P) := by
  obtain ⟨decode, heads, distinct, members⟩ := Selection.source_heads fallback hf rows terms cover bound selected
  have nodup : chosen.Nodup := distinct.of_map decode
  have injective : Set.InjOn decode {r | r ∈ chosen} := (List.nodup_map_iff_inj_on nodup).mp distinct
  refine ⟨decode, heads, ?_⟩
  intro disjoint arity q body P built agree
  apply countTruth_assignments decode chosen nodup injective S
    (fun x => by simpa only [List.mem_map] using (members x).symm) disjoint arity q body P s w τ e t built agree

end Tuples
end ClaferCompiler.Correctness.Behavioral.Full
