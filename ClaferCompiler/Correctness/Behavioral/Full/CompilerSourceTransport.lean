module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionExpressions
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerSourceValidity
public import ClaferCompiler.Correctness.Behavioral.Full.ModifierMeaning

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full
open IR.Behavioral

namespace ObservesCompletion
variable {U : Type} {v : IR.BehavioralStructural.Validated k} {p : Fin k}
  {l : ObservedLasso k o steps} {τ : Clafer.Behavioral.Trace (Fin k) U}
  {R : Clafer.Constraints.IntegerRealization U} {objects : Fin o ↪ U}

local notation "M" => SemanticsBridge.BehavioralStructural.interpret v.core
local notation "CT" => Clafer.Behavioral.Structural.observed M (completeTrace v p l)
local notation "ST" => Clafer.Behavioral.Structural.observed M τ

@[simp] theorem environment_closed (h : ObservesCompletion v p l τ R objects) (x : Completion o) :
    h.environment (.closed x) = .closed (h.embedding x) := by
  unfold environment Clafer.Behavioral.Environment.closed
  congr 1
  funext i
  exact Fin.elim0 i

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Strict expression satisfaction is invariant under the concrete observation
embedding, retaining the full mathematical integer realization on both sides. -/
theorem formula_satisfies (h : ObservesCompletion v p l τ R objects)
    (a : Expression.Formula k n) (sign : Bool)
    (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) ST R a).Satisfies ST
      SemanticsBridge.Behavioral.Expression.observation sign (h.environment ρ) t ↔
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) CT completeIntegers a).Satisfies CT
      SemanticsBridge.Behavioral.Expression.observation sign ρ t := by
  rw [observed_formula_satisfies, observed_formula_satisfies]
  exact and_congr ((h.formula_transport a).defined ρ t) ((h.formula_transport a).denote sign ρ t)

theorem formula_closed (h : ObservesCompletion v p l τ R objects)
    (a : Expression.Formula k 0) (sign : Bool) (x : Completion o) (t : Nat) :
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) ST R a).Satisfies ST
      SemanticsBridge.Behavioral.Expression.observation sign (.closed (h.embedding x)) t ↔
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) CT completeIntegers a).Satisfies CT
      SemanticsBridge.Behavioral.Expression.observation sign (.closed x) t := by
  simpa only [environment_closed] using h.formula_satisfies a sign (.closed x) t

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem constraint (h : ObservesCompletion v p l τ R objects)
    (valid : Clafer.Behavioral.Structural.Valid M τ)
    (completed : Clafer.Behavioral.Structural.Valid M (completeTrace v p l))
    (a : Constraint k) :
    (sourceConstraint v a).Holds τ (sourceObservation v R τ) ↔
      (sourceConstraint v a).Holds (completeTrace v p l)
        (sourceObservation v completeIntegers (completeTrace v p l)) := by
  rw [sourceConstraint_meaning v R τ valid, sourceConstraint_meaning v completeIntegers _ completed]
  constructor
  · intro hs t x hx
    have hh := hs t (h.embedding x) ((h.head_iff t a.owner x).mpr hx)
    exact (h.formula_closed a.body true x t).mp hh
  · intro hs t y hy
    have covered : y ∈ h.embedding '' ((completeTrace v p l).raw (Sets.model v) t).head a.owner := by
      rw [h.head_image]
      exact hy
    obtain ⟨x, hx, rfl⟩ := covered
    exact (h.formula_closed a.body true x t).mpr (hs t x hx)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem placement (h : ObservesCompletion v p l τ R objects)
    (where_ : Surface.Modifiers.Placement k) (t : Nat) (x : Completion o) :
    h.embedding x ∈ (SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts M τ t ↔
      x ∈ (SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts M
        (completeTrace v p l) t := by
  cases where_ with
  | all => rfl
  | heads d => exact h.head_iff t d x
  | parents d =>
    change (∃ q, _ = some q ∧ h.embedding x ∈ (τ.raw (Sets.model v) t).head q) ↔
      ∃ q, _ = some q ∧ x ∈ ((completeTrace v p l).raw (Sets.model v) t).head q
    simp only [h.head_iff]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem modifierItem (h : ObservesCompletion v p l τ R objects)
    (where_ : Surface.Modifiers.Placement k) (a : Expression.Formula k 0) :
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) ST R a).PartialAttached ST
      SemanticsBridge.Behavioral.Expression.observation
      ((SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts M τ) ↔
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) CT completeIntegers a).PartialAttached CT
      SemanticsBridge.Behavioral.Expression.observation
      ((SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts M (completeTrace v p l)) := by
  constructor
  · intro hs t x member live
    apply (h.formula_closed a true x t).mp
    exact hs t (h.embedding x) ((h.placement where_ t x).mpr member) ((h.live_iff t x).mpr live)
  · intro hs t y member live
    have covered : y ∈ h.embedding '' (completeTrace v p l).live t := by
      rw [h.live_image]
      exact live
    obtain ⟨x, hx, rfl⟩ := covered
    exact (h.formula_closed a true x t).mpr
      (hs t x ((h.placement where_ t x).mp member) hx)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem modifiers (h : ObservesCompletion v p l τ R objects)
    (valid : Clafer.Behavioral.Structural.Valid M τ)
    (completed : Clafer.Behavioral.Structural.Valid M (completeTrace v p l))
    (table : Vector (List Surface.Modifiers.Modifier) k) :
    Clafer.Behavioral.Modifiers.Holds M τ (SemanticsBridge.Behavioral.Modifiers.declared table) ↔
      Clafer.Behavioral.Modifiers.Holds M (completeTrace v p l)
        (SemanticsBridge.Behavioral.Modifiers.declared table) := by
  rw [← modifierExpansions_source v table R τ valid,
    ← modifierExpansions_source v table completeIntegers (completeTrace v p l) completed]
  exact forall_congr' fun item => imp_congr_right fun _ => h.modifierItem item.1 item.2

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem model (m : Model k)
    (h : ObservesCompletion m.structural p l τ R objects)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret m.structural.core) τ)
    (completed : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret m.structural.core) (completeTrace m.structural p l)) :
    (sourceModel m R).Satisfies τ ↔
      (sourceModel m completeIntegers).Satisfies (completeTrace m.structural p l) := by
  rw [sourceModel_satisfies, sourceModel_satisfies]
  constructor
  · intro hs
    exact ⟨completed, (h.modifiers valid completed m.modifiers).mp hs.2.1,
      fun a member => (h.constraint valid completed a).mp (hs.2.2 a member)⟩
  · intro hs
    exact ⟨valid, (h.modifiers valid completed m.modifiers).mpr hs.2.1,
      fun a member => (h.constraint valid completed a).mpr (hs.2.2 a member)⟩

-- [proof->req~compiler-behavioral-property-commands~1]
theorem command (r : Request k)
    (h : ObservesCompletion r.model.structural p l τ R objects)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core) τ)
    (completed : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
      (completeTrace r.model.structural p l)) :
    SourceCommand r R τ ↔ SourceCommand r completeIntegers (completeTrace r.model.structural p l) := by
  cases command : r.command with
  | check i =>
    simp only [SourceCommand, command]
    exact not_congr (h.constraint valid completed r.model.assertions[i])
  | run scenario =>
    simp only [SourceCommand, command]
    exact forall_congr' fun a => imp_congr_right fun _ => h.constraint valid completed a

-- [proof->req~compiler-full-behavioral-correctness~1]
-- [proof->req~compiler-behavioral-property-commands~1]
/-- A source model or counterexample on an arbitrary carrier restricts to the
canonical completion of its finite observation tables. The correspondence
contains only identity, incidence, scalar and live-coverage data. -/
theorem sourceResult (r : Request k)
    (h : ObservesCompletion r.model.structural p l τ R objects)
    (satisfies : SourceResult r R τ) :
    SourceResult r completeIntegers (completeTrace r.model.structural p l) := by
  obtain ⟨source, command⟩ := (sourceResult_iff r R τ).mp satisfies
  have sourceValid := ((sourceModel_satisfies r.model R τ).mp source).1
  have completed := h.valid sourceValid
  exact (sourceResult_iff r completeIntegers _).mpr
    ⟨(model r.model h sourceValid completed).mp source, (ObservesCompletion.command r h sourceValid completed).mp command⟩

end ObservesCompletion
end ClaferCompiler.Correctness.Behavioral.Full
