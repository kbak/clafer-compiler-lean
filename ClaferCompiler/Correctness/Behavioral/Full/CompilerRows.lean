module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsCorrectness
public import ClaferCompiler.Correctness.Behavioral.Full.StructureExpressionRows
public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompiled
public import ClaferCompiler.Correctness.Behavioral.Full.RangesStructure

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The primitive and numerical premises of expression preservation follow
from concrete representation data and the actual generated structural facts. -/
theorem modelRows (rep : TraceRep v source target) (b : Bounds)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (shape : PrimitiveShape v) (positive : 0 < b.bitwidth) (small : b.bitwidth ≤ 16)
    (capacity : o ≤ b.objects)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) b.bitwidth target.unfold [] 0)
    (bounds : ∀ f ∈ boundFacts v b, f.Holds (schema v) b.bitwidth target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (fields : ∀ t, (target.unfold.state t).scalarFields b.bitwidth (schema v).declarations = true)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    Expressions.ModelRows v (estimates v b) (schema v) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) rep.labels := by
  exact ⟨rep.primitiveRows p primitive shape (fun x => (rep.ordinary_concrete b.bitwidth identity x).2)
    b.bitwidth positive small (fun t => rep.values_fit b.bitwidth t (fields t)) states valid,
    Ranges.inputs_of_facts rep b primitive capacity bounds valid, positive, small⟩

end TraceRep

namespace CompileOutput
variable {r : Request k} {b : Bounds} {fuel : Nat} {c : Compiled}

theorem identity (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold) :
    ∀ f ∈ identityFacts r.model.structural,
      f.Holds (schema r.model.structural) b.bitwidth target.unfold [] 0 := by
  rw [out.module_eq] at sat
  intro f member
  exact (sat.2.2.2.2.1 f (by simp only [generatedModule, List.mem_append]; aesop)).2

theorem boundFacts (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold) :
    ∀ f ∈ Backend.Alloy.Behavioral.Full.boundFacts r.model.structural b,
      f.Holds (schema r.model.structural) b.bitwidth target.unfold [] 0 := by
  rw [out.module_eq] at sat
  intro f member
  exact (sat.2.2.2.2.1 f (by simp only [generatedModule, List.mem_append]; aesop)).2

theorem states (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold) :
    ∀ t f, f ∈ stateFacts r.model.structural →
      f.Holds (schema r.model.structural) b.bitwidth target.unfold [] t := by
  rw [out.module_eq] at sat
  intro t f member
  have holds := (sat.2.2.2.2.1 (.unary .always f) (by
    simp only [generatedModule, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨f, List.mem_append_left _ member, rfl⟩))))).2
  exact (always_holds (stateFacts_built _ f member)).mp holds t (Nat.zero_le t)

theorem fields (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold) :
    ∀ t, (target.unfold.state t).scalarFields b.bitwidth (schema r.model.structural).declarations = true := by
  rw [out.module_eq] at sat
  exact sat.2.2.2.2.2.2.2

theorem scopes (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold) :
    target.unfold.InScope (Backend.Alloy.Behavioral.Full.scopes r.model.structural b) := by
  rw [out.module_eq] at sat
  exact sat.2.2.2.1

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem modelRows (out : CompileOutput r b fuel c) (target : Lasso)
    (sat : Satisfies c.module.raw target.unfold)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (rep : TraceRep r.model.structural source target)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
      (completeTrace r.model.structural p source)) :
    Expressions.ModelRows r.model.structural (estimates r.model.structural b)
      (schema r.model.structural) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
        (completeTrace r.model.structural p source)) rep.labels := by
  obtain ⟨shape, positive, small⟩ := validateBounds_properties _ _ out.bounds
  exact rep.modelRows b p primitive shape positive small
    (rep.capacity_of_scopes b (out.scopes target sat)) (out.identity target sat)
    (out.boundFacts target sat) (out.states target sat) (out.fields target sat) valid

end CompileOutput
end ClaferCompiler.Correctness.Behavioral.Full
