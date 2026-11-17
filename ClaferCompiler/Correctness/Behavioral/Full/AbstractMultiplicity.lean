module

public import ClaferCompiler.Correctness.Behavioral.Full.FrontendCorrectness
public import ClaferCompiler.SemanticsBridge.Behavioral.AbstractMultiplicity
public import ClaferCompiler.SemanticsBridge.BehavioralResolution

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.AbstractMultiplicity
open Backend.Alloy.Behavioral.Full
open Clafer.Behavioral (Trace)
open Frontend.Behavioral.AbstractMultiplicity
namespace Bridge
abbrev interpret {k : Nat} := @SemanticsBridge.Behavioral.AbstractMultiplicity.interpret k
end Bridge

-- [proof->req~compiler-abstract-multiplicity~1]
/-- The existing attachment semantics makes the global obligation unconditional
at every time and the nested obligation conditional on each live declared parent. -/
theorem constraint_iff (v : IR.BehavioralStructural.Validated k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
    (d : Fin k)
    (finite : ∀ t, ((τ.raw (Sets.model v) t).head d).Finite) :
    (sourceConstraint v (constraint v.core.structural d)).Holds τ (sourceObservation v R τ) ↔
    ∀ t, match (Bridge.interpret v.core).family.parent d with
      | none => Clafer.Semantics.AbstractMultiplicity.Global
          (τ.raw (Bridge.interpret v.core).source.toEffectiveCore t) d
          (Clafer.Semantics.AbstractMultiplicity.range ((Bridge.interpret v.core).authoredMultiplicity d))
      | some p => Clafer.Semantics.AbstractMultiplicity.PerParent
          (τ.raw (Bridge.interpret v.core).source.toEffectiveCore t) d p
          (Clafer.Semantics.AbstractMultiplicity.range ((Bridge.interpret v.core).authoredMultiplicity d)) := by
  rw [sourceConstraint_meaning v R τ valid]
  have parent_eq : (Bridge.interpret v.core).family.parent d = (v.core.structural.get d).parent := rfl
  rw [parent_eq]
  cases parent : (v.core.structural.get d).parent with
  | none =>
    simp only [Frontend.Behavioral.AbstractMultiplicity.constraint, parent, Option.getD_none]
    constructor
    · intro h t
      exact (SemanticsBridge.Behavioral.AbstractMultiplicity.global v.core (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ) R d parent
        (.closed τ.identities.root) t (finite t)).mp (h t τ.identities.root
          (((valid.states t).root_head _).mpr rfl))
    · intro h t x _
      exact (SemanticsBridge.Behavioral.AbstractMultiplicity.global v.core (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ) R d parent
        (.closed x) t (finite t)).mpr (h t)
  | some p =>
    simp only [Frontend.Behavioral.AbstractMultiplicity.constraint, parent, Option.getD_some]
    have fibers (t : Nat) (x : U) :
        {y | (τ.raw (Sets.model v) t).contains d x y}.Finite :=
      (finite t).subset (fun _ h => ⟨h.1.2.1, h.2.1⟩)
    constructor
    · intro h t x hx
      exact (SemanticsBridge.Behavioral.AbstractMultiplicity.fiber v.core (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ) R d p parent
        (.closed x) t (fibers t x)).mp (h t x hx)
    · intro h t x hx
      exact (SemanticsBridge.Behavioral.AbstractMultiplicity.fiber v.core (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core) τ) R d p parent
        (.closed x) t (fibers t x)).mpr (h t x hx)

-- [proof->req~compiler-abstract-multiplicity~1]
/-- The complete generated inventory is equivalent to the independently defined
upstream obligation. Finiteness is required only for abstract heads. -/
theorem generated_iff (v : IR.BehavioralStructural.Validated k)
    (τ : Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core) τ)
    (finite : ∀ t d, v.core.authoredAbstract[d] = true → ((τ.raw (Sets.model v) t).head d).Finite) :
    (∀ a ∈ generate v, (sourceConstraint v a).Holds τ (sourceObservation v R τ)) ↔
      Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret v.core) τ := by
  simp only [generate, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h t d hd
    have count := (constraint_iff v τ R valid d (fun t => finite t d hd)).mp (h d hd) t
    cases hp : (Bridge.interpret v.core).family.parent d <;> simpa only [hp] using count
  · intro h d hd
    apply (constraint_iff v τ R valid d (fun t => finite t d hd)).mpr
    intro t
    have count := h t d hd
    cases hp : (Bridge.interpret v.core).family.parent d <;> simpa only [hp] using count

/-- The ordinary model before inserting the aggregate constraints. The same
modifiers, authored properties, generated initializers and assertions remain. -/
def baseModel {source : Frontend.Behavioral.Document} (e : Frontend.Behavioral.Elaborated source) :
    Model e.declarations.resolved.count :=
  { e.model with constraints := e.authored .constraint ++ e.generated }

-- [proof->req~compiler-abstract-multiplicity~1]
-- [proof->req~compiler-full-behavioral-correctness~1]
theorem model_iff {source : Frontend.Behavioral.Document} (e : Frontend.Behavioral.Elaborated source)
    (selected : e.declarations.resolved.aggregate = true)
    (τ : Trace (Fin e.declarations.resolved.count) U) (R : Clafer.Constraints.IntegerRealization U)
    (finite : ∀ t d, e.model.structural.core.authoredAbstract[d] = true →
      ((τ.raw (Sets.model e.model.structural) t).head d).Finite) :
    (sourceModel e.model R).Satisfies τ ↔
      (sourceModel (baseModel e) R).Satisfies τ ∧
      Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret e.model.structural.core) τ := by
  rw [sourceModel_satisfies, sourceModel_satisfies]
  constructor
  · rintro ⟨valid, mods, all⟩
    have parts : (∀ a ∈ (baseModel e).constraints,
        (sourceConstraint e.model.structural a).Holds τ (sourceObservation e.model.structural R τ)) ∧
        (∀ a ∈ generate e.model.structural,
        (sourceConstraint e.model.structural a).Holds τ (sourceObservation e.model.structural R τ)) := by
      simpa only [baseModel, Frontend.Behavioral.Elaborated.model, constraints, selected,
        ↓reduceIte, List.mem_append, or_imp, forall_and] using all
    exact ⟨⟨valid, mods, parts.1⟩, (generated_iff _ τ R valid finite).mp parts.2⟩
  · rintro ⟨⟨valid, mods, all⟩, counts⟩
    refine ⟨valid, mods, ?_⟩
    have generated := (generated_iff _ τ R valid finite).mpr counts
    simpa only [baseModel, Frontend.Behavioral.Elaborated.model, constraints, selected,
      ↓reduceIte, List.mem_append, or_imp, forall_and] using And.intro all generated

-- [proof->req~compiler-abstract-multiplicity~1]
/-- Successful selected elaboration discharges the effective-normalization
premise of the independent upstream source projection. -/
theorem source_valid_iff {source : Frontend.Behavioral.Document}
    (e : Frontend.Behavioral.Elaborated source)
    (selected : e.declarations.resolved.aggregate = true)
    (τ : Trace (Fin e.declarations.resolved.count) U) :
    Clafer.Behavioral.AbstractMultiplicity.Valid (Bridge.interpret e.model.structural.core) τ ↔
      Clafer.Behavioral.Structural.Valid
        (SemanticsBridge.BehavioralStructural.interpret e.model.structural.core) τ ∧
      Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret e.model.structural.core) τ := by
  apply SemanticsBridge.Behavioral.AbstractMultiplicity.normalized_valid_iff
  intro d abstract
  have normalized := (SemanticsBridge.BehavioralResolution.aggregate_bounds
    _ e.declarations.resolved selected d abstract).1
  change SemanticsBridge.Structural.bounds
    (e.declarations.resolved.admitted.core.structural.get d).localBounds = _
  rw [normalized]
  rfl

-- [proof->req~compiler-abstract-multiplicity~1]
theorem result_counts {source : Frontend.Behavioral.Document} (e : Frontend.Behavioral.Elaborated source)
    (selected : e.declarations.resolved.aggregate = true)
    (r : Request e.declarations.resolved.count) (same : r.model = e.model)
    (τ : Trace (Fin e.declarations.resolved.count) U) (R : Clafer.Constraints.IntegerRealization U)
    (finite : ∀ t d, e.model.structural.core.authoredAbstract[d] = true →
      ((τ.raw (Sets.model e.model.structural) t).head d).Finite)
    (satisfies : SourceResult r R τ) :
    Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret e.model.structural.core) τ := by
  have model := ((sourceResult_iff r R τ).mp satisfies).1
  rw [same] at model
  exact ((model_iff e selected τ R finite).mp model).2

-- [proof->req~compiler-abstract-multiplicity~1]
-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Full target soundness now yields the independent aggregate obligation,
including every later state. Finiteness follows from decoded occurrence tables;
the completed mathematical integer domain remains infinite. -/
theorem frontend_sound {source : Frontend.Behavioral.Document}
    (e : Frontend.Behavioral.Elaborated source)
    (elaborated : Frontend.Behavioral.elaborate profile source = .ok e)
    (selected : e.declarations.resolved.aggregate = true)
    (r : Request e.declarations.resolved.count) (same : r.model = e.model)
    (b : Bounds) (fuel : Nat) (c : Compiled) (success : compile r b fuel = .ok c)
    (target : Backend.Alloy.Temporal.Lasso)
    (sat : Backend.Alloy.Temporal.Satisfies c.module.raw target.unfold) :
    SourceElaborated e ∧ ∃ p : Fin e.declarations.resolved.count,
      (r.model.structural.core.structural.get p).origin = .integer ∧
      ∃ decoded : Σ o steps, ObservedLasso e.declarations.resolved.count o steps,
        decode r.model.structural target = .ok decoded ∧
        SourceResult r completeIntegers (completeTrace r.model.structural p decoded.2.2) ∧
        Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret e.model.structural.core)
          (completeTrace r.model.structural p decoded.2.2) := by
  obtain ⟨derivation, p, primitive, decoded, read, sourceSat⟩ :=
    Full.frontend_sound e elaborated r same b fuel c success target sat
  refine ⟨derivation, p, primitive, decoded, read, sourceSat,
    result_counts e selected r same _ _ ?_ sourceSat⟩
  have shape := (frontend_primitive e).1
  have primitive' : (e.model.structural.core.structural.get p).origin = .integer := by
    simpa only [same] using primitive
  intro t d abstract
  have ordinary : d ≠ p := by
    intro eq
    subst d
    have notAbstract := (shape p primitive').1
    simp only [notAbstract, Bool.false_eq_true] at abstract
  simpa only [same] using completeHead_finite r.model.structural p primitive decoded.2.2 t d ordinary

-- [proof->req~compiler-abstract-multiplicity~1]
-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Bounded completeness takes the independent authored count obligation and
retains the existing structural, range, scope and lasso fitting premises. -/
theorem frontend_complete {source : Frontend.Behavioral.Document}
    (e : Frontend.Behavioral.Elaborated source)
    (elaborated : Frontend.Behavioral.elaborate profile source = .ok e)
    (selected : e.declarations.resolved.aggregate = true)
    (r : Request e.declarations.resolved.count) (same : r.model = e.model)
    (b : Bounds) (fuel : Nat) (c : Compiled) (success : compile r b fuel = .ok c)
    (p : Fin e.declarations.resolved.count)
    (primitive : (e.model.structural.core.structural.get p).origin = .integer)
    (observed : ObservedLasso e.declarations.resolved.count o steps)
    (fit : Fits r.model.structural p observed b)
    (base : (sourceModel (baseModel e) completeIntegers).Satisfies
      (completeTrace r.model.structural p observed))
    (counts : Clafer.Behavioral.AbstractMultiplicity.Always (Bridge.interpret e.model.structural.core)
      (completeTrace r.model.structural p observed))
    (command : SourceCommand r completeIntegers (completeTrace r.model.structural p observed)) :
    SourceElaborated e ∧ Backend.Alloy.Temporal.Lasso.Satisfies c.module.raw (encode observed) := by
  apply Full.frontend_complete e elaborated r same b fuel c success p primitive observed fit
  apply (sourceResult_iff r _ _).mpr
  refine ⟨?_, command⟩
  have model : (sourceModel e.model completeIntegers).Satisfies
      (completeTrace r.model.structural p observed) :=
    (model_iff e selected _ _ ?_).mpr ⟨base, counts⟩
  · simpa only [same] using model
  · have shape := (frontend_primitive e).1
    intro t d abstract
    have ordinary : d ≠ p := by
      intro eq
      subst d
      simp only [(shape p primitive).1, Bool.false_eq_true] at abstract
    have primitive' : (r.model.structural.core.structural.get p).origin = .integer := by
      simpa only [same] using primitive
    simpa only [same] using completeHead_finite r.model.structural p primitive' observed t d ordinary

end ClaferCompiler.Correctness.Behavioral.Full.AbstractMultiplicity
