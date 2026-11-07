module

public import ClaferCompiler.IR.Behavioral.RangeRules
public import Mathlib.Data.Int.Basic

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Expression.Ranges

theorem hull_fits (ha : a.fits w = true) (hb : b.fits w = true) : (hull a b).fits w = true := by
  simp only [hull, Expr.Interval.fits, decide_eq_true_eq] at *
  apply decide_eq_true
  omega

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem collection_fits {a : Collection k n} (h : CollectionBound b Γ a r) :
    r.values.fits b.width = true := by
  apply CollectionBound.rec (t := h) (motive_1 := fun _ _ r _ => r.values.fits b.width = true)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun _ _ _ => True)
  all_goals intros
  all_goals first | assumption | trivial | (apply integer_fits; assumption) | (apply hull_fits <;> assumption)

theorem set_unique (h : SetBound b Γ a x) (other : SetBound b Γ a y) : x = y := by
  induction h generalizing y with
  | empty => cases other; rfl
  | this => cases other; rfl
  | root => cases other; rfl
  | var => cases other; rfl
  | extent => cases other; rfl
  | union left right ihl ihr =>
    cases other with
    | union l r => rw [ihl l, ihr r]
  | inter left right ihl ihr =>
    cases other with
    | inter l r => rw [ihl l, ihr r]
  | diff left right ihl ihr =>
    cases other with
    | diff l _ => exact ihl l
  | step => cases other; rfl
  | thisStep => cases other; rfl

mutual
-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem collection_unique {a : Collection k n}
    (h : CollectionBound b Γ a x) (other : CollectionBound b Γ a y) : x = y := by
  cases h with
  | set path _ => cases other with | set path' _ => exact set_unique path path'
  | literal => cases other; rfl
  | integer body => cases other with | integer body' => rw [integer_unique body body']
  | extreme body => cases other with | extreme body' => rw [collection_unique body body']
  | union left right => cases other with | union l r => rw [collection_unique left l, collection_unique right r]
  | inter left right => cases other with | inter l r => rw [collection_unique left l, collection_unique right r]
  | diff left _ => cases other with | diff l _ => exact collection_unique left l
  | step => cases other; rfl
  | ofType body => cases other with | ofType body' => exact collection_unique body body'
  | ite _ yes no => cases other with | ite _ yes' no' => rw [collection_unique yes yes', collection_unique no no']
termination_by sizeOf a

theorem integer_unique {a : Integer k n}
    (h : IntegerBound b Γ a x) (other : IntegerBound b Γ a y) : x = y := by
  cases h with
  | literal => cases other; rfl
  | coerce body _ => cases other with | coerce body' _ => rw [collection_unique body body']
  | extract body _ => cases other with | extract body' _ => rw [collection_unique body body']
  | cardinality body _ => cases other with | cardinality body' _ => rw [collection_unique body body']
  | binary left right _ => cases other with | binary l r _ => rw [integer_unique left l, integer_unique right r]
  | negate body _ => cases other with | negate body' _ => rw [integer_unique body body']
  | fold domains body _ =>
    cases other with
    | fold domains' body' _ =>
      have hd := collections_unique domains domains'
      subst hd
      rw [integer_unique body body']
  | ite _ yes no _ => cases other with | ite _ yes' no' _ => rw [integer_unique yes yes', integer_unique no no']
termination_by sizeOf a

theorem collections_unique {a : Collections k n}
    (h : CollectionsBound b Γ a x) (other : CollectionsBound b Γ a y) : x = y := by
  cases h with
  | nil => cases other; rfl
  | cons head tail => cases other with | cons head' tail' => rw [collection_unique head head', collections_unique tail tail']
termination_by sizeOf a
end

end ClaferCompiler.IR.Behavioral.Expression.Ranges
