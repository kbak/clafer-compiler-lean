module

public import ClaferCompiler.Correctness.Behavioral.Full.FrontendElaboration
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCorrectness

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Successful in-memory source elaboration composes with the actual full
compiler. Primitive completion's existence follows from declaration binding.
Parsing text and executing the generated solver command remain external gates. -/
theorem frontend_sound {source : Frontend.Behavioral.Document}
    (e : Frontend.Behavioral.Elaborated source)
    (elaborated : Frontend.Behavioral.elaborate profile source = .ok e)
    (r : Request e.declarations.resolved.count) (sameModel : r.model = e.model)
    (b : Bounds) (fuel : Nat) (c : Compiled) (success : compile r b fuel = .ok c)
    (target : Lasso) (sat : Satisfies c.module.raw target.unfold) :
    SourceElaborated e ∧
      ∃ p : Fin e.declarations.resolved.count,
        (r.model.structural.core.structural.get p).origin = .integer ∧
        ∃ decoded : Σ o steps, ObservedLasso e.declarations.resolved.count o steps,
          decode r.model.structural target = .ok decoded ∧
          SourceResult r completeIntegers (completeTrace r.model.structural p decoded.2.2) := by
  obtain ⟨_, p, primitive⟩ := frontend_primitive e
  have primitive : (r.model.structural.core.structural.get p).origin = .integer := by
    simpa only [sameModel] using primitive
  exact ⟨elaborate_source elaborated, p, primitive,
    compiled_sound r b fuel c success p primitive target sat⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Source elaboration and the finite source observation compose with concrete
bounded completeness. The fitting conditions concern source data only. -/
theorem frontend_complete {source : Frontend.Behavioral.Document}
    (e : Frontend.Behavioral.Elaborated source)
    (elaborated : Frontend.Behavioral.elaborate profile source = .ok e)
    (r : Request e.declarations.resolved.count) (sameModel : r.model = e.model)
    (b : Bounds) (fuel : Nat) (c : Compiled) (success : compile r b fuel = .ok c)
    (p : Fin e.declarations.resolved.count)
    (primitive : (e.model.structural.core.structural.get p).origin = .integer)
    (observed : ObservedLasso e.declarations.resolved.count o steps)
    (fit : Fits r.model.structural p observed b)
    (satisfies : SourceResult r completeIntegers (completeTrace r.model.structural p observed)) :
    SourceElaborated e ∧ Lasso.Satisfies c.module.raw (encode observed) := by
  have primitive : (r.model.structural.core.structural.get p).origin = .integer := by
    simpa only [sameModel] using primitive
  exact ⟨elaborate_source elaborated, compiled_complete r b fuel c success p primitive observed fit satisfies⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The original source carrier may contain any mathematical integer realization
and unused identities. A single finite observation map suffices for the same
frontend-to-target completeness conclusion. -/
theorem frontend_complete_observed {source : Frontend.Behavioral.Document} {U : Type}
    (e : Frontend.Behavioral.Elaborated source)
    (elaborated : Frontend.Behavioral.elaborate profile source = .ok e)
    (r : Request e.declarations.resolved.count) (sameModel : r.model = e.model)
    (b : Bounds) (fuel : Nat) (c : Compiled) (success : compile r b fuel = .ok c)
    (p : Fin e.declarations.resolved.count)
    (primitive : (e.model.structural.core.structural.get p).origin = .integer)
    (lasso : ObservedLasso e.declarations.resolved.count o steps)
    (fit : Fits r.model.structural p lasso b)
    (τ : Clafer.Behavioral.Trace (Fin e.declarations.resolved.count) U)
    (R : Clafer.Constraints.IntegerRealization U) (objects : Fin o ↪ U)
    (observed : ObservesCompletion r.model.structural p lasso τ R objects)
    (satisfies : SourceResult r R τ) :
    SourceElaborated e ∧ Lasso.Satisfies c.module.raw (encode lasso) := by
  have primitive : (r.model.structural.core.structural.get p).origin = .integer := by
    simpa only [sameModel] using primitive
  exact ⟨elaborate_source elaborated,
    compiled_complete_observed r b fuel c success p primitive lasso fit τ R objects observed satisfies⟩

end ClaferCompiler.Correctness.Behavioral.Full
