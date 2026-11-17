module

public import ClaferCompiler.Frontend.Behavioral.AbstractMultiplicity
public import ClaferCompiler.SemanticsBridge.Behavioral.Expression
public import ClaferCompiler.SemanticsBridge.BehavioralStructural
public import Clafer.Behavioral.AbstractMultiplicity
public import Clafer.Constraints.DenotationLaws

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.AbstractMultiplicity
open IR.Behavioral
open Clafer.Behavioral (Trace Environment)
open DPGraph.Predicates
namespace Source
abbrev formula {k n : Nat} := @Frontend.Behavioral.AbstractMultiplicity.formula k n
abbrev heads {k n : Nat} := @Frontend.Behavioral.AbstractMultiplicity.heads k n
abbrev authored {k : Nat} := @Frontend.Behavioral.AbstractMultiplicity.authored k
end Source

/-- Only the counted set must be finite. Neither the identity universe nor
the mathematical integer carrier is required to be finite. -/
-- [proof->req~compiler-abstract-multiplicity~1]
theorem formula_iff (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : SetExpr k n)
    (b : IR.Structural.Bounds) (ρ : Environment U n) (t : Nat)
    (finite : ((setExpr a).eval m τ ρ t).Finite) :
    (Expression.formula m τ R (Source.formula a b)).Satisfies
      τ Expression.observation true ρ t ↔
    CountInRange (Structural.bounds b) ((setExpr a).eval m τ ρ t).ncard := by
  classical
  cases b with
  | mk lo hi =>
    cases hi <;>
      simp [Source.formula, Frontend.Behavioral.AbstractMultiplicity.formula,
        Expression.formula, Expression.observation, Clafer.Behavioral.Formula.Satisfies,
        Clafer.Behavioral.Formula.Defined, Clafer.Behavioral.Formula.denote,
        Clafer.Behavioral.PartialObservation.canonical, Clafer.Behavioral.PartialObservation.complete,
        Clafer.Constraints.finiteCard_finite _ finite, Clafer.Constraints.lift₂,
        CountInRange, Structural.bounds, Clafer.Behavioral.polarity] <;> tauto

-- [proof->req~compiler-abstract-multiplicity~1]
theorem formula_inRange (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : SetExpr k n)
    (b : IR.Structural.Bounds) (ρ : Environment U n) (t : Nat)
    (finite : ((setExpr a).eval m τ ρ t).Finite) :
    (Expression.formula m τ R (Source.formula a b)).Satisfies
      τ Expression.observation true ρ t ↔
    InRange (Structural.bounds b) {x // x ∈ (setExpr a).eval m τ ρ t} := by
  let := finite.fintype
  rw [formula_iff _ _ _ _ _ _ _ finite, inRange_card, Set.fintypeCard_eq_ncard]

/-- Source annotations are carried separately into the accepted extension. -/
def interpret (m : IR.BehavioralStructural.Core k) : Clafer.Behavioral.AbstractMultiplicity.Core k where
  toCore := BehavioralStructural.interpret m
  authoredMultiplicity d := ((m.structural.get d).authored.bind (·.localBounds)).map Structural.bounds

theorem authored_range (m : IR.BehavioralStructural.Core k) (d : Fin k) :
    Clafer.Semantics.AbstractMultiplicity.range ((interpret m).authoredMultiplicity d) =
      Structural.bounds (Source.authored m.structural d) := by
  change (((m.structural.get d).authored.bind (·.localBounds)).map Structural.bounds).getD _ = _
  cases h : (m.structural.get d).authored.bind (·.localBounds) <;>
    simp [Source.authored, Frontend.Behavioral.AbstractMultiplicity.authored, h, Structural.bounds,
      Clafer.unrestricted]

-- [proof->req~compiler-abstract-multiplicity~1]
theorem global (m : IR.BehavioralStructural.Core k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (d : Fin k)
    (parent : (m.structural.get d).parent = none) (ρ : Environment U n) (t : Nat)
    (finite : ((τ.raw (BehavioralStructural.interpret m).toEffectiveCore t).head d).Finite) :
    (Expression.formula (BehavioralStructural.interpret m).toEffectiveCore τ R
      (Source.formula (Source.heads m.structural d) (Source.authored m.structural d))).Satisfies
      τ Expression.observation true ρ t ↔
    Clafer.Semantics.AbstractMultiplicity.Global (τ.raw (interpret m).source.toEffectiveCore t) d
      (Clafer.Semantics.AbstractMultiplicity.range ((interpret m).authoredMultiplicity d)) := by
  rw [authored_range]
  unfold Clafer.Semantics.AbstractMultiplicity.Global
  rw [(interpret m).raw_eq τ t]
  simpa [Source.heads, Frontend.Behavioral.AbstractMultiplicity.heads, parent, setExpr,
    Clafer.Behavioral.SetExpr.eval, interpret] using
    formula_inRange (BehavioralStructural.interpret m).toEffectiveCore τ R
      (.extent d) (Source.authored m.structural d) ρ t finite

-- [proof->req~compiler-abstract-multiplicity~1]
theorem fiber (m : IR.BehavioralStructural.Core k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (d p : Fin k)
    (parent : (m.structural.get d).parent = some p) (ρ : Environment U n) (t : Nat)
    (finite : {x | (τ.raw (BehavioralStructural.interpret m).toEffectiveCore t).contains d ρ.this x}.Finite) :
    (Expression.formula (BehavioralStructural.interpret m).toEffectiveCore τ R
      (Source.formula (Source.heads m.structural d) (Source.authored m.structural d))).Satisfies
      τ Expression.observation true ρ t ↔
    InRange (Clafer.Semantics.AbstractMultiplicity.range ((interpret m).authoredMultiplicity d))
      {x // (τ.raw (interpret m).source.toEffectiveCore t).contains d ρ.this x} := by
  have eval : (setExpr (SetExpr.thisStep (.child d) : SetExpr k n)).eval
      (BehavioralStructural.interpret m).toEffectiveCore τ ρ t =
      {x | (τ.raw (BehavioralStructural.interpret m).toEffectiveCore t).contains d ρ.this x} := by
    ext x
    simp [setExpr, step, Clafer.Behavioral.SetExpr.eval,
      Clafer.Behavioral.Step.image, Clafer.Behavioral.Step.relation]
  have fin := eval.symm ▸ finite
  rw [authored_range, (interpret m).raw_eq τ t]
  simpa only [Source.heads, Frontend.Behavioral.AbstractMultiplicity.heads,
    parent, Option.isSome_some, ↓reduceIte, eval, interpret, Set.mem_ofPred_eq] using
    formula_inRange (BehavioralStructural.interpret m).toEffectiveCore τ R
      (.thisStep (.child d)) (Source.authored m.structural d) ρ t fin

/-- Moving abstract ranges into constraints changes only multiplicity
obligations. Inherited reference ownership and per-fiber keys are preserved. -/
-- [proof->req~compiler-abstract-multiplicity~1]
theorem normalized_valid_iff (m : Clafer.Behavioral.AbstractMultiplicity.Core k)
    (τ : Trace (Fin k) U)
    (normalized : ∀ d, m.authoredAbstract d = true → m.family.multiplicity d = Clafer.unrestricted) :
    Clafer.Behavioral.AbstractMultiplicity.Valid m τ ↔
      Clafer.Behavioral.Structural.Valid m.toCore τ ∧
      Clafer.Behavioral.AbstractMultiplicity.Always m τ := by
  constructor
  · rintro ⟨valid, counts⟩
    refine ⟨?_, counts⟩
    have ids : Clafer.Behavioral.Structural.IdentitiesValid m.toCore τ := by
      obtain ⟨a, b, c, d, e, f⟩ := valid.identities
      exact ⟨a, b, c, d, e, f⟩
    refine ⟨ids, valid.root_live, valid.parent_live, fun t => ?_⟩
    refine { valid.states t with
      keys := (m.keys_iff τ t).mp (valid.states t).keys
      multiplicities := ?_ }
    intro d p parent x hx
    cases abstract : m.authoredAbstract d with
    | false =>
      have h := (valid.states t).multiplicities d p parent x hx
      rw [m.ordinary_range d abstract] at h
      exact h
    | true =>
      rw [normalized d abstract]
      exact Clafer.Semantics.AbstractMultiplicity.unrestricted_holds _
  · rintro ⟨valid, counts⟩
    refine ⟨?_, counts⟩
    have ids : Clafer.Behavioral.Structural.IdentitiesValid m.source τ := by
      obtain ⟨a, b, c, d, e, f⟩ := valid.identities
      exact ⟨a, b, c, d, e, f⟩
    refine ⟨ids, valid.root_live, valid.parent_live, fun t => ?_⟩
    refine { valid.states t with
      keys := (m.keys_iff τ t).mpr (valid.states t).keys
      multiplicities := ?_ }
    intro d p parent x hx
    cases abstract : m.authoredAbstract d with
    | false =>
      rw [m.ordinary_range d abstract]
      exact (valid.states t).multiplicities d p parent x hx
    | true =>
      rw [m.abstract_range d abstract]
      have count := counts t d abstract
      change m.family.parent d = some p at parent
      rw [parent] at count
      exact count x hx

end ClaferCompiler.SemanticsBridge.Behavioral.AbstractMultiplicity
