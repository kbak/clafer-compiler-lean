module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionFormula
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsAttachments
public import ClaferCompiler.SemanticsBridge.Behavioral.Properties

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full
open IR.Behavioral

/-- The accepted source model uses fixed expression syntax and interprets its
observations in each trace's inherited structural view. -/
def sourceObservation {U : Type} (v : IR.BehavioralStructural.Validated k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U) :=
  SemanticsBridge.Behavioral.Expression.syntaxObservation (Sets.model v)
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ) R

abbrev sourceModel {U : Type} (m : Model k) (R : Clafer.Constraints.IntegerRealization U) :=
  SemanticsBridge.Behavioral.Properties.model (fun x => x) (fun x => x) m
    (sourceObservation m.structural R)

abbrev sourceConstraint {U : Type} (v : IR.BehavioralStructural.Validated k) (a : Constraint k) :=
  SemanticsBridge.Behavioral.Properties.constraint (U := U) (fun x => x) (fun x => x) v.core a

/-- A trace witnesses the existing upstream query: a model counterexample for
`check`, or a model trace satisfying the extra scenario for `run`. -/
def SourceResult {U : Type} (r : Request k) (R : Clafer.Constraints.IntegerRealization U)
    (τ : Clafer.Behavioral.Trace (Fin k) U) : Prop :=
  match r.command with
  | .check i => (sourceModel r.model R).Counterexample
      (sourceConstraint r.model.structural r.model.assertions[i]) τ
  | .run scenario => (sourceModel r.model R).Satisfies τ ∧
      ∀ a ∈ SemanticsBridge.Behavioral.Properties.constraints (fun x => x) (fun x => x)
        r.model.structural.core scenario, a.Holds τ (sourceObservation r.model.structural R τ)

def SourceCommand {U : Type} (r : Request k) (R : Clafer.Constraints.IntegerRealization U)
    (τ : Clafer.Behavioral.Trace (Fin k) U) : Prop :=
  match r.command with
  | .check i => ¬ (sourceConstraint r.model.structural r.model.assertions[i]).Holds
      τ (sourceObservation r.model.structural R τ)
  | .run scenario => ∀ a ∈ scenario, (sourceConstraint r.model.structural a).Holds
      τ (sourceObservation r.model.structural R τ)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem sourceResult_request {U : Type} (r : Request k) (R : Clafer.Constraints.IntegerRealization U) :
    (∃ τ, SourceResult r R τ) ↔ match r.command with
      | .check _ => ¬ SemanticsBridge.Behavioral.Properties.request (fun x => x) (fun x => x)
          r (sourceObservation r.model.structural R)
      | .run _ => SemanticsBridge.Behavioral.Properties.request (fun x => x) (fun x => x)
          r (sourceObservation r.model.structural R) := by
  cases command : r.command with
  | check i =>
    simp only [SourceResult, SemanticsBridge.Behavioral.Properties.request, command]
    exact Clafer.Behavioral.Properties.Model.counterexample_iff _ _
  | run scenario => simp only [SourceResult, SemanticsBridge.Behavioral.Properties.request, command]; rfl

theorem observed_formula_satisfies {U : Type} {A D : Nat → Type}
    (m : Clafer.Behavioral.Structural.Core k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (O : Clafer.Behavioral.PartialObservation A D U) (a : Clafer.Behavioral.Formula A D n)
    (positive : Bool) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    a.Satisfies (Clafer.Behavioral.Structural.observed m τ) O positive ρ t ↔
      a.Satisfies τ O positive ρ t := by
  unfold Clafer.Behavioral.Formula.Satisfies
  rw [← Clafer.Behavioral.Formula.normalize_agrees, ← Clafer.Behavioral.Formula.normalize_agrees]
  exact and_congr (observed_formula_defined m τ O a ρ t)
    (observed_formula_raw m τ O.canonical (a.normalize positive) ρ t)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem sourceFormula_meaning {U : Type} (v : IR.BehavioralStructural.Validated k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (a : Expression.Formula k n) (positive : Bool) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (SemanticsBridge.Behavioral.Generic.interpret (fun x => x) (fun x => x) a).Satisfies
      τ (sourceObservation v R τ) positive ρ t ↔
    (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
      R a).Satisfies
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
      SemanticsBridge.Behavioral.Expression.observation positive ρ t := by
  unfold sourceObservation SemanticsBridge.Behavioral.Expression.syntaxObservation
  rw [SemanticsBridge.Behavioral.Generic.satisfies_pullback,
    ← SemanticsBridge.Behavioral.Expression.formula_eq_generic]
  exact (observed_formula_satisfies _ _ _ _ _ _ _).symm

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem sourceConstraint_meaning {U : Type} (v : IR.BehavioralStructural.Validated k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
    (a : Constraint k) :
    (sourceConstraint v a).Holds τ (sourceObservation v R τ) ↔
    ∀ t x, x ∈ (τ.raw (Sets.model v) t).head a.owner →
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        R a.body).Satisfies
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
        SemanticsBridge.Behavioral.Expression.observation true (.closed x) t := by
  unfold sourceConstraint SemanticsBridge.Behavioral.Properties.constraint
  split
  · next root =>
    rw [Clafer.Behavioral.Properties.Constraint.root_holds _ _ _ valid.root_live]
    simp only [sourceFormula_meaning]
    constructor
    · intro h t x hx
      have eq := ((valid.states t).root_head x).mp (by
        simpa only [root, Sets.model, SemanticsBridge.BehavioralStructural.interpret,
          SemanticsBridge.Structural.interpret] using hx)
      exact eq ▸ h t
    · intro h t
      apply h t τ.identities.root
      rw [root]
      exact ((valid.states t).root_head _).mpr rfl
  · rw [Clafer.Behavioral.Properties.Constraint.nested_holds]
    simp only [sourceFormula_meaning]

theorem sourceConstraints_meaning {U : Type} (v : IR.BehavioralStructural.Validated k)
    (R : Clafer.Constraints.IntegerRealization U) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (cs : List (Constraint k)) :
    (∀ a ∈ SemanticsBridge.Behavioral.Properties.constraints (fun x => x) (fun x => x)
      v.core cs, a.Holds τ (sourceObservation v R τ)) ↔
    ∀ a ∈ cs, (sourceConstraint v a).Holds τ (sourceObservation v R τ) := by
  simp only [SemanticsBridge.Behavioral.Properties.constraints, Set.mem_ofPred_eq,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem sourceResult_iff {U : Type} (r : Request k) (R : Clafer.Constraints.IntegerRealization U)
    (τ : Clafer.Behavioral.Trace (Fin k) U) :
    SourceResult r R τ ↔ (sourceModel r.model R).Satisfies τ ∧ SourceCommand r R τ := by
  cases command : r.command with
  | check i => simp only [SourceResult, SourceCommand, command]; rfl
  | run scenario =>
    simp only [SourceResult, SourceCommand, command]
    exact and_congr Iff.rfl (sourceConstraints_meaning _ _ _ _)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem sourceModel_satisfies {U : Type} (m : Model k) (R : Clafer.Constraints.IntegerRealization U)
    (τ : Clafer.Behavioral.Trace (Fin k) U) :
    (sourceModel m R).Satisfies τ ↔
      Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret m.structural.core) τ ∧
      Clafer.Behavioral.Modifiers.Holds (SemanticsBridge.BehavioralStructural.interpret m.structural.core) τ
        (SemanticsBridge.Behavioral.Modifiers.declared m.modifiers) ∧
      ∀ a ∈ m.constraints, (sourceConstraint m.structural a).Holds τ (sourceObservation m.structural R τ) := by
  change ((_ ∧ _ ∧ _) ∧ _) ↔ _
  exact ⟨fun h => ⟨h.1.2.1, h.1.2.2, (sourceConstraints_meaning _ _ _ _).mp h.2⟩,
    fun h => ⟨⟨SemanticsBridge.BehavioralStructural.validated_wellFormed m.structural, h.1, h.2.1⟩,
      (sourceConstraints_meaning _ _ _ _).mpr h.2.2⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem completedConstraint_meaning (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source)) (a : Constraint k) (ordinary : integerDeclaration v a.owner = false) :
    (sourceConstraint v a).Holds (completeTrace v p source)
      (sourceObservation v completeIntegers (completeTrace v p source)) ↔
    ∀ t x, x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw (Sets.model v) t).head a.owner →
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) completeIntegers a.body).Satisfies
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation true (.closed (Sum.inl x)) t := by
  rw [sourceConstraint_meaning v completeIntegers _ valid]
  constructor
  · intro h t x hx
    exact h t (Sum.inl x) hx
  · intro h t x hx
    cases x with
    | inl x => exact h t x hx
    | inr z =>
      have equal := (completeHead_integer v p primitive source t a.owner z).mp hx
      have := (integerDeclaration_eq v p primitive a.owner).mpr equal.symm
      simp only [ordinary, Bool.false_eq_true] at this

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Backend.Alloy.Temporal.Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem constraint_source (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (capacity : o ≤ b.objects)
    (pass : Expressions.PassObservation v (estimates v b) (schema v) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) rep.labels
      (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel))
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source))
    (a : Constraint k) (result : Backend.Alloy.Temporal.Formula)
    (success : constraint v b fuel a = .ok result) :
    result.Holds (schema v) b.bitwidth target.unfold [] 0 ↔
      (sourceConstraint v a).Holds (completeTrace v p source)
        (sourceObservation v completeIntegers (completeTrace v p source)) := by
  have ordinary : integerDeclaration v a.owner = false := by
    cases eq : integerDeclaration v a.owner
    · rfl
    · simp [constraint, eq, bind, Except.bind, throw] at success
  exact (rep.constraint_meaning b fuel capacity pass facts a result success).trans
    (completedConstraint_meaning v p primitive source valid a ordinary).symm

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
