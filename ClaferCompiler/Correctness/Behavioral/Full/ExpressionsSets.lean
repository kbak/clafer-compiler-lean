module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsObservations
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Expressions
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
namespace Sets
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral
variable {U : Type}

abbrev model (v : IR.BehavioralStructural.Validated k) : Clafer.Semantics.EffectiveCore k :=
  (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore

def FiniteStep (v : IR.BehavioralStructural.Validated k) : Step k → Prop
  | .child d => integerDeclaration v d = false
  | _ => True

def FinitePath (v : IR.BehavioralStructural.Validated k) : SetExpr k n → Prop :=
  SetExpr.rec True True True (fun _ => True) (fun d => integerDeclaration v d = false)
    (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
    (fun st _ a => FiniteStep v st ∧ a) (FiniteStep v)

/-- Primitive row observations on the bounded observation universe. The parent
relation is restricted only at its input, since the canonical source contains
all mathematical integers. Closure records scalar-range and identity coverage;
no set expression or formula agreement is assumed. -/
structure PrimitiveRows (v : IR.BehavioralStructural.Validated k)
    (s : Schema) (w : Nat) (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace)
    (f : U → Atom) (A : Set U) : Prop where
  injective : Function.Injective f
  root : ∀ e t, Mixed.Unary f {σ.identities.root} ((Backend.Alloy.Behavioral.Full.root v).eval s w τ e t)
  root_inside : σ.identities.root ∈ A
  live : ∀ e t, Mixed.Unary f (σ.live t ∩ A) ((Backend.Alloy.Behavioral.Full.observedLive v).eval s w τ e t)
  pool : ∀ d e t, Mixed.Unary f {x | (model v).Ancestor (σ.identities.directType x) d ∧ x ∈ A}
    ((Backend.Alloy.Behavioral.Full.pool v d).eval s w τ e t)
  head : ∀ d, integerDeclaration v d = false → ∀ e t,
    Mixed.Unary f ((σ.raw (model v) t).head d) ((Backend.Alloy.Behavioral.Full.head v d).eval s w τ e t)
  head_inside : ∀ d, integerDeclaration v d = false → ∀ t,
    (σ.raw (model v) t).head d ⊆ A
  step_term : ∀ st, (Backend.Alloy.Behavioral.Full.step v st).Term
  step : ∀ st, FiniteStep v st → ∀ e t,
    Mixed.Binary f (fun x y => x ∈ A ∧
      (SemanticsBridge.Behavioral.step st).relation (model v) σ t x y)
      ((Backend.Alloy.Behavioral.Full.step v st).eval s w τ e t)
  step_inside : ∀ st, FiniteStep v st → ∀ t x y, x ∈ A →
    (SemanticsBridge.Behavioral.step st).relation (model v) σ t x y → y ∈ A

structure ContextRows (s : Schema) (w : Nat) (τ : Trace) (f : U → Atom) (A : Set U)
    (c : Expressions.Context n) (ρ : Clafer.Behavioral.Environment U n) (e : Environment) : Prop where
  this_term : c.lexical.this.Term
  this : ∀ t, Mixed.Unary f {ρ.this} (c.lexical.this.eval s w τ e t)
  this_inside : ρ.this ∈ A
  lookup_term : ∀ i, (c.lexical.lookup i).Term
  lookup : ∀ i t, Mixed.Unary f (ρ.lookup i) ((c.lexical.lookup i).eval s w τ e t)
  lookup_inside : ∀ i, ρ.lookup i ⊆ A

theorem finiteStep_success (v : IR.BehavioralStructural.Validated k) (st : Step k)
    (h : finiteStep v st = .ok result) : result = Backend.Alloy.Behavioral.Full.step v st ∧ FiniteStep v st := by
  cases st with
  | parent => cases h; exact ⟨rfl, True.intro⟩
  | deref d => cases h; exact ⟨rfl, True.intro⟩
  | child d =>
    simp only [finiteStep] at h
    split at h
    · contradiction
    · rename_i hn
      cases h
      exact ⟨rfl, Bool.eq_false_iff.mpr hn⟩

theorem bind2_success (f : α → β → γ) (a : Result α) (b : Result β)
    (h : (do let x ← a; let y ← b; pure (f x y)) = .ok result) :
    ∃ x y, a = .ok x ∧ b = .ok y := by
  cases a with
  | error err => contradiction
  | ok x =>
    cases b with
    | error err => contradiction
    | ok y => exact ⟨x, y, rfl, rfl⟩

theorem map_success (f : α → β) (a : Result α)
    (h : (do let x ← a; pure (f x)) = .ok result) : ∃ x, a = .ok x := by
  cases a with
  | error err => contradiction
  | ok x => exact ⟨x, rfl⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem lowerAt_set_finite (v : IR.BehavioralStructural.Validated k)
    (b : Expression.Ranges.Inputs k) (fuel depth : Nat) (c : Expressions.Context n)
    (a : SetExpr k n) (success : ((lowerAt v b fuel depth).set c a) = .ok result) :
    FinitePath v a := by
  induction depth generalizing a result with
  | zero => contradiction
  | succ depth ih =>
    change ((lowerStep v b fuel (lowerAt v b fuel depth)).set c a) = .ok result at success
    cases a with
    | empty | this | root | var => trivial
    | extent d =>
      simp only [lowerStep] at success
      split at success
      · contradiction
      · rename_i hn
        exact Bool.eq_false_iff.mpr hn
    | union a b' =>
      obtain ⟨ra, rb, ha, hb⟩ := bind2_success Rel.union _ _ success
      exact ⟨ih a ha, ih b' hb⟩
    | inter a b' =>
      obtain ⟨ra, rb, ha, hb⟩ := bind2_success Rel.inter _ _ success
      exact ⟨ih a ha, ih b' hb⟩
    | diff a b' =>
      obtain ⟨ra, rb, ha, hb⟩ := bind2_success Rel.diff _ _ success
      exact ⟨ih a ha, ih b' hb⟩
    | step st a =>
      obtain ⟨ra, rr, ha, hr⟩ := bind2_success Rel.join _ _ success
      exact ⟨(finiteStep_success v st hr).2, ih a ha⟩
    | thisStep st =>
      obtain ⟨rr, hr⟩ := map_success (Rel.join c.lexical.this) _ success
      exact (finiteStep_success v st hr).2

variable {U : Type} {v : IR.BehavioralStructural.Validated k}
  {s : Schema} {w : Nat} {σ : Clafer.Behavioral.Trace (Fin k) U} {τ : Trace}
  {f : U → Atom} {A : Set U} {c : Expressions.Context n}
  {ρ : Clafer.Behavioral.Environment U n} {e : Environment} {t : Nat}
  {input result : Rel} {S : Set U}

theorem image_rows (hp : PrimitiveRows v s w σ τ f A)
    (st : Step k) (valid : FiniteStep v st) (term : input.Term)
    (represented : Mixed.Unary f S (input.eval s w τ e t)) (inside : S ⊆ A) :
    Mixed.Unary f ((SemanticsBridge.Behavioral.step st).image (model v) σ t S)
      ((input.join (Backend.Alloy.Behavioral.Full.step v st)).eval s w τ e t) := by
  have h := Mixed.unary_image hp.injective term (hp.step_term st) represented (hp.step st valid e t)
  convert h using 1
  ext y
  change (∃ x ∈ S, (SemanticsBridge.Behavioral.step st).relation (model v) σ t x y) ↔
    ∃ x ∈ S, x ∈ A ∧ (SemanticsBridge.Behavioral.step st).relation (model v) σ t x y
  exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, inside hx, hxy⟩,
    fun ⟨x, hx, _, hxy⟩ => ⟨x, hx, hxy⟩⟩

theorem image_inside (hp : PrimitiveRows v s w σ τ f A)
    (st : Step k) (valid : FiniteStep v st) (inside : S ⊆ A) :
    (SemanticsBridge.Behavioral.step st).image (model v) σ t S ⊆ A := by
  rintro y ⟨x, hx, hxy⟩
  exact hp.step_inside st valid t x y (inside hx) hxy

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Actual full-profile set lowering preserves independently observed mixed
rows. Explicit infinite primitive extents cannot satisfy the success premise. -/
theorem lowerAt_set (hp : PrimitiveRows v s w σ τ f A) (hc : ContextRows s w τ f A c ρ e)
    (b : Expression.Ranges.Inputs k) (fuel depth : Nat) (a : SetExpr k n)
    (success : ((lowerAt v b fuel depth).set c a) = .ok result) :
    result.Term ∧
    Mixed.Unary f ((SemanticsBridge.Behavioral.setExpr a).eval (model v) σ ρ t)
      (result.eval s w τ e t) ∧
    ((SemanticsBridge.Behavioral.setExpr a).eval (model v) σ ρ t) ⊆ A := by
  induction depth generalizing a result with
  | zero => contradiction
  | succ depth ih =>
    change ((lowerStep v b fuel (lowerAt v b fuel depth)).set c a) = .ok result at success
    cases a with
    | empty =>
      cases success
      exact ⟨.empty _, Mixed.unary_empty, Set.empty_subset A⟩
    | this =>
      cases success
      refine ⟨.inter hc.this_term (Rel.Term.union (Full.live_term v) .ints), ?_, ?_⟩
      · have rows := Mixed.unary_inter hp.injective hc.this_term (Rel.Term.union (Full.live_term v) .ints)
          (hc.this t) (hp.live e t)
        convert rows using 1
        · ext x
          change (x = ρ.this ∧ x ∈ σ.live t) ↔ x ∈ ({ρ.this} ∩ (σ.live t ∩ A))
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨rfl, live⟩
            exact ⟨rfl, live, hc.this_inside⟩
          · rintro ⟨same, live, _⟩
            exact ⟨same, live⟩
        · rfl
      · rintro x ⟨rfl, _⟩
        exact hc.this_inside
    | root =>
      cases success
      exact ⟨Full.root_term v, hp.root e t, Set.singleton_subset_iff.mpr hp.root_inside⟩
    | var i =>
      cases success
      exact ⟨hc.lookup_term i, hc.lookup i t, hc.lookup_inside i⟩
    | extent d =>
      simp only [lowerStep] at success
      split at success
      · contradiction
      · rename_i hn
        cases success
        have hd := Bool.eq_false_iff.mpr hn
        exact ⟨Full.head_term v d, hp.head d hd e t, hp.head_inside d hd t⟩
    | union a b' =>
      cases left : (lowerAt v b fuel depth).set c a with
      | error err =>
        simp only [lowerStep, left] at success
        contradiction
      | ok ra =>
        cases right : (lowerAt v b fuel depth).set c b' with
        | error err =>
          simp only [lowerStep, left, right] at success
          contradiction
        | ok rb =>
          simp only [lowerStep, left, right] at success
          cases success
          obtain ⟨ha, rowsa, ina⟩ := ih a left
          obtain ⟨hb, rowsb, inb⟩ := ih b' right
          exact ⟨.union ha hb, Mixed.unary_union ha hb rowsa rowsb, Set.union_subset ina inb⟩
    | inter a b' =>
      cases left : (lowerAt v b fuel depth).set c a with
      | error err =>
        simp only [lowerStep, left] at success
        contradiction
      | ok ra =>
        cases right : (lowerAt v b fuel depth).set c b' with
        | error err =>
          simp only [lowerStep, left, right] at success
          contradiction
        | ok rb =>
          simp only [lowerStep, left, right] at success
          cases success
          obtain ⟨ha, rowsa, ina⟩ := ih a left
          obtain ⟨hb, rowsb, _⟩ := ih b' right
          exact ⟨.inter ha hb, Mixed.unary_inter hp.injective ha hb rowsa rowsb,
            fun _ hx => ina hx.1⟩
    | diff a b' =>
      cases left : (lowerAt v b fuel depth).set c a with
      | error err =>
        simp only [lowerStep, left] at success
        contradiction
      | ok ra =>
        cases right : (lowerAt v b fuel depth).set c b' with
        | error err =>
          simp only [lowerStep, left, right] at success
          contradiction
        | ok rb =>
          simp only [lowerStep, left, right] at success
          cases success
          obtain ⟨ha, rowsa, ina⟩ := ih a left
          obtain ⟨hb, rowsb, _⟩ := ih b' right
          exact ⟨.diff ha hb, Mixed.unary_diff hp.injective ha hb rowsa rowsb,
            fun _ hx => ina hx.1⟩
    | step st a =>
      cases path : (lowerAt v b fuel depth).set c a with
      | error err =>
        simp only [lowerStep, path] at success
        contradiction
      | ok ra =>
        cases relation : finiteStep v st with
        | error err =>
          simp only [lowerStep, path, relation] at success
          contradiction
        | ok rr =>
          simp only [lowerStep, path, relation] at success
          cases success
          obtain ⟨rfl, valid⟩ := finiteStep_success v st relation
          obtain ⟨ha, rowsa, ina⟩ := ih a path
          exact ⟨.join ha (hp.step_term st), image_rows hp st valid ha rowsa ina,
            image_inside hp st valid ina⟩
    | thisStep st =>
      cases relation : finiteStep v st with
      | error err => simp [lowerStep, relation] at success
      | ok rr =>
        simp only [lowerStep, relation] at success
        cases success
        obtain ⟨rfl, valid⟩ := finiteStep_success v st relation
        have inside : ({ρ.this} : Set U) ⊆ A := by simpa using hc.this_inside
        exact ⟨.join hc.this_term (hp.step_term st), image_rows hp st valid hc.this_term (hc.this t) inside,
          image_inside hp st valid inside⟩

end Sets
end ClaferCompiler.Correctness.Behavioral.Full
