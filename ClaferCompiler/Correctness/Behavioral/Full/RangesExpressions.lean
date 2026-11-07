module

public import ClaferCompiler.Correctness.Behavioral.Full.RangesEnvironments

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Ranges
open IR.Behavioral.Expression.Ranges
open IR.Behavioral
open SemanticsBridge.Behavioral.Expression

private theorem lift_some {a : Option A} {b : Option B} {f : A → B → C}
    (h : Clafer.Constraints.lift₂ f a b = some c) :
    ∃ x y, a = some x ∧ b = some y ∧ f x y = c := by
  cases a <;> cases b <;> simp_all [Clafer.Constraints.lift₂]

private theorem conditional_choice {c : Option Bool} {a b : Option A}
    (h : IR.BehavioralArithmetic.conditional c a b = some x) : a = some x ∨ b = some x := by
  cases c with
  | none => cases h
  | some c => cases c <;> cases a <;> cases b <;> simp_all [IR.BehavioralArithmetic.conditional]

variable {U : Type} {v : IR.BehavioralStructural.Validated k} {b : Inputs k}
  {σ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}

mutual
  -- [proof->req~compiler-full-behavioral-correctness~1]
  /-- Successful source observations satisfy the admitted estimate. Every
  constructor follows the original partial source meaning, including strict
  conditional branches and indexed fold occurrences. -/
  theorem collection_bound (hb : InputsBound v b σ R) (hρ : EnvironmentBound b Γ R ρ)
      (h : Expression.Ranges.CollectionBound b Γ a r)
      (value : collection (Sets.model v) σ R a ρ t = some S) : CollectionBound R r S := by
    cases h with
    | set path _ =>
      have eq := Option.some.inj value
      rw [← eq]
      exact set_bound hb hρ path t
    | literal =>
      have eq : {R.encode _} = S := Option.some.inj value
      rw [← eq]
      exact CollectionBound.integer ⟨le_refl _, le_refl _⟩
    | integer body =>
      obtain ⟨z, hz, eq⟩ := Option.map_eq_some_iff.mp value
      subst S
      exact CollectionBound.integer (integer_bound hb hρ body hz)
    | extreme body =>
      obtain ⟨T, ht, hs⟩ := Option.bind_eq_some_iff.mp value
      exact (collection_bound hb hρ body ht).extreme _ hs
    | union left right =>
      obtain ⟨S₁, S₂, h₁, h₂, eq⟩ := lift_some value
      subst S
      exact (collection_bound hb hρ left h₁).union (collection_bound hb hρ right h₂)
    | inter left right =>
      obtain ⟨S₁, S₂, h₁, h₂, eq⟩ := lift_some value
      subst S
      exact (collection_bound hb hρ left h₁).inter (collection_bound hb hρ right h₂)
    | diff left _ =>
      obtain ⟨S₁, _, h₁, _, eq⟩ := lift_some value
      subst S
      exact (collection_bound hb hρ left h₁).diff
    | step _ allowed _ =>
      obtain ⟨T, _, eq⟩ := Option.map_eq_some_iff.mp value
      subst S
      exact hb.steps _ allowed t T
    | ofType body =>
      obtain ⟨T, ht, eq⟩ := Option.map_eq_some_iff.mp value
      subst S
      exact (collection_bound hb hρ body ht).subset (fun _ hx => hx.1)
    | ite _ yes no =>
      rw [collection_ite] at value
      rcases conditional_choice value with yesValue | noValue
      · exact (collection_bound hb hρ yes yesValue).selected_left
      · exact (collection_bound hb hρ no noValue).selected_right
  termination_by sizeOf a
  decreasing_by
    all_goals (subst_vars; simp)
    all_goals omega

  -- [proof->req~compiler-full-behavioral-correctness~1]
  theorem integer_bound (hb : InputsBound v b σ R) (hρ : EnvironmentBound b Γ R ρ)
      (h : IntegerBound b Γ a r)
      (value : integer (Sets.model v) σ R a ρ t = some z) : r.Contains z := by
    cases h with
    | literal =>
      cases Option.some.inj value
      exact ⟨le_refl _, le_refl _⟩
    | coerce body _ =>
      obtain ⟨S, hs, hz⟩ := Option.bind_eq_some_iff.mp value
      exact (collection_bound hb hρ body hs).coerce hz
    | extract body _ =>
      obtain ⟨S, hs, hz⟩ := Option.bind_eq_some_iff.mp value
      exact (collection_bound hb hρ body hs).extract hz
    | cardinality body _ =>
      obtain ⟨number, hn, hz⟩ := Option.map_eq_some_iff.mp value
      obtain ⟨S, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
      have bound := collection_bound hb hρ body hs
      rw [Clafer.Constraints.finiteCard_finite _ bound.finite] at hn
      cases Option.some.inj hn
      subst z
      exact bound.cardinality
    | binary left right _ =>
      obtain ⟨x, hx, rest⟩ := Option.bind_eq_some_iff.mp value
      obtain ⟨y, hy, hz⟩ := Option.bind_eq_some_iff.mp rest
      exact SemanticsBridge.BehavioralArithmetic.range_contains _
        (integer_bound hb hρ left hx) (integer_bound hb hρ right hy)
        ((SemanticsBridge.BehavioralArithmetic.scalar_agrees _ (some x) (some y)).trans hz)
    | negate body _ =>
      obtain ⟨x, hx, eq⟩ := Option.map_eq_some_iff.mp value
      subst z
      exact SemanticsBridge.BehavioralArithmetic.negate_range (integer_bound hb hρ body hx)
    | fold domains body _ =>
      obtain ⟨sets, hs, hz⟩ := Option.bind_eq_some_iff.mp value
      have hsets := collections_bound hb hρ domains hs
      obtain ⟨finite, count⟩ := occurrences_bound hsets
      apply fold_range _ finite count _ ?_ hz
      intro ix hix number hnumber
      have member : ix.2 ∈ unionSets sets :=
        ⟨sets[ix.1], List.getElem_mem _, hix⟩
      have capture := (family_bound hsets).singleton_member member
      exact integer_bound hb (hρ.push capture) body hnumber
    | ite _ yes no _ =>
      rw [integer_ite] at value
      rcases conditional_choice value with yesValue | noValue
      · have hy := integer_bound hb hρ yes yesValue
        exact ⟨(min_le_left _ _).trans hy.1, hy.2.trans (le_max_left _ _)⟩
      · have hn := integer_bound hb hρ no noValue
        exact ⟨(min_le_right _ _).trans hn.1, hn.2.trans (le_max_right _ _)⟩
  termination_by sizeOf a
  decreasing_by
    all_goals (subst_vars; simp)
    all_goals omega

  theorem collections_bound (hb : InputsBound v b σ R) (hρ : EnvironmentBound b Γ R ρ)
      (h : CollectionsBound b Γ a rs)
      (value : collections (Sets.model v) σ R a ρ t = some sets) :
      List.Forall₂ (CollectionBound R) rs sets := by
    cases h with
    | nil => cases Option.some.inj value; exact .nil
    | cons head tail =>
      obtain ⟨S, rest, hs, hr, eq⟩ := lift_some value
      subst sets
      exact .cons (collection_bound hb hρ head hs) (collections_bound hb hρ tail hr)
  termination_by sizeOf a
  decreasing_by
    all_goals (subst_vars; simp)
    all_goals omega
end

/-- Each accepted scalar derivation bounds its successful value by the target
width. The original derivation retains all intermediate and vacuous-body checks. -/
theorem integer_fits (hb : InputsBound v b σ R) (hρ : EnvironmentBound b Γ R ρ)
    (h : IntegerBound b Γ a r)
    (value : integer (Sets.model v) σ R a ρ t = some z) :
    (IR.Expr.signedRange b.width).Contains z := by
  have hr := integer_bound hb hρ h value
  have hf := Expression.Ranges.integer_fits h
  simp only [IR.Expr.Interval.fits, decide_eq_true_eq] at hf
  exact ⟨hf.2.2.2.1.trans hr.1, hr.2.trans hf.2.2.2.2⟩

end ClaferCompiler.Correctness.Behavioral.Full.Ranges
