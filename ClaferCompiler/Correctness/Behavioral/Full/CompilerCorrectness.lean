module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCommands
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerModifiers
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerDefined
public import ClaferCompiler.Correctness.Behavioral.Full.CompilerSourceTransport
public import ClaferCompiler.Correctness.Behavioral.Full.StructureDefined

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

/-- Bounds constrain the finite occurrence inventory, scalar observations,
structural cardinalities and lasso length. They assume no source property,
target formula truth, decoder result or expression agreement. -/
structure Fits (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (source : ObservedLasso k o steps) (b : Bounds) : Prop where
  structural : StructuralFits v p source b.bitwidth b.objects
  scopes : SourceBoundsFits v source b
  minimum : b.minSteps ≤ steps
  maximum : steps ≤ b.maxSteps

theorem encode_fits (fit : Fits v p source b) (kind : Backend.Alloy.CommandKind) (body : Formula) :
    (encode source).Fits ⟨kind, body, scopes v b, b.bitwidth, b.minSteps, b.maxSteps⟩ := by
  simpa only [Lasso.Fits, encode, List.length_map, List.length_finRange] using
    And.intro fit.minimum fit.maximum

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Successful compilation and a satisfying target determine a decoded source
with the complete integer carrier and the concrete premises of expression
preservation. No source validity or representation witness is an assumption. -/
theorem compiled_observations (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Lasso) (sat : Satisfies c.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode r.model.structural target = .ok decoded ∧
      Clafer.Behavioral.Structural.Valid
        (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
        (completeTrace r.model.structural p decoded.2.2) ∧
      ∃ rep : TraceRep r.model.structural decoded.2.2 target,
        decoded.1 ≤ b.objects ∧
        Expressions.ModelRows r.model.structural (estimates r.model.structural b)
          (schema r.model.structural) target.unfold
          (Clafer.Behavioral.Structural.observed
            (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
            (completeTrace r.model.structural p decoded.2.2)) rep.labels := by
  obtain ⟨out⟩ := compile_output r b fuel c success
  obtain ⟨decoded, read, valid⟩ := compiled_structural_sound r b fuel c success p primitive target sat
  let rep := decode_rep r.model.structural target decoded read
  exact ⟨decoded, read, valid, rep, rep.capacity_of_scopes b (out.scopes target sat),
    out.modelRows target sat p primitive decoded.2.2 rep valid⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem compiled_constraints_command (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Lasso) (sat : Satisfies c.module.raw target.unfold)
    (source : ObservedLasso k o steps) (rep : TraceRep r.model.structural source target)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
      (completeTrace r.model.structural p source)) :
    (∀ a ∈ r.model.constraints, (sourceConstraint r.model.structural a).Holds
      (completeTrace r.model.structural p source)
      (sourceObservation r.model.structural completeIntegers (completeTrace r.model.structural p source))) ∧
    SourceCommand r completeIntegers (completeTrace r.model.structural p source) := by
  obtain ⟨out⟩ := compile_output r b fuel c success
  have model := out.modelRows target sat p primitive source rep valid
  have capacity := rep.capacity_of_scopes b (out.scopes target sat)
  have states := out.states target sat
  have generated := sat
  rw [out.module_eq] at generated
  constructor
  · apply (rep.constraints_source b fuel p primitive capacity model states valid _ _ out.constraints_lowered).mp
    intro f member
    exact (generated.2.2.2.2.1 f (by
      simp only [generatedModule, List.mem_append]
      exact Or.inl (Or.inr member))).2
  · exact (command_source r b fuel p primitive source target rep capacity model states valid
      out.kind out.body out.command_lowered).mp generated.2.2.2.2.2.2.1

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encoded_modelRows (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (source : ObservedLasso k o steps) (fit : Fits v p source b)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    ∃ rep : TraceRep v source (encode source),
      Expressions.ModelRows v (estimates v b) (schema v) (encode source).unfold
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) rep.labels := by
  have ids := completeIdentities_restrict v p source valid.identities
  let rep := encode_rep v source fit.structural.unique ids.root_type ids.root_only
  obtain ⟨_, fields, identity, states, _⟩ :=
    encode_structural_complete v p primitive shape source b.bitwidth b.objects fit.structural valid
  exact ⟨rep, rep.modelRows b p primitive shape fit.structural.widthPositive fit.structural.widthSmall
    fit.structural.capacity identity (rep.boundFacts_complete b fit.scopes fit.structural.scalars) states fields valid⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encoded_constraints_command (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (out : CompileOutput r b fuel c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (fit : Fits r.model.structural p source b)
    (satisfies : SourceResult r completeIntegers (completeTrace r.model.structural p source)) :
    (∀ f ∈ out.constraints, f.Holds (schema r.model.structural) b.bitwidth (encode source).unfold [] 0) ∧
      commandHolds out.kind out.body (schema r.model.structural) b.bitwidth (encode source).unfold := by
  obtain ⟨sourceModel, sourceCommand⟩ := (sourceResult_iff _ _ _).mp satisfies
  obtain ⟨valid, _, constraints⟩ := (sourceModel_satisfies _ _ _).mp sourceModel
  have shape := (validateBounds_properties _ _ out.bounds).1
  obtain ⟨rep, model⟩ := encoded_modelRows r.model.structural b p primitive shape source fit valid
  obtain ⟨_, _, _, states, _⟩ := encode_structural_complete r.model.structural p primitive shape source
    b.bitwidth b.objects fit.structural valid
  exact ⟨(rep.constraints_source b fuel p primitive fit.structural.capacity model states valid
    r.model.constraints out.constraints out.constraints_lowered).mpr constraints,
    (command_source r b fuel p primitive source (encode source) rep fit.structural.capacity
      model states valid out.kind out.body out.command_lowered).mpr sourceCommand⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every satisfying output of the actual compiler decodes to a witness for
the accepted full source model and its selected assertion or scenario. The
source uses all mathematical integers and one fixed occurrence correspondence. -/
theorem compiled_sound (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Lasso) (sat : Satisfies c.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode r.model.structural target = .ok decoded ∧
      SourceResult r completeIntegers (completeTrace r.model.structural p decoded.2.2) := by
  obtain ⟨out⟩ := compile_output r b fuel c success
  obtain ⟨decoded, read, valid, rep, capacity, model⟩ :=
    compiled_observations r b fuel c success p primitive target sat
  have states := out.states target sat
  have constraintCommand := compiled_constraints_command r b fuel c success p primitive target sat decoded.2.2 rep valid
  have shape := (validateBounds_properties _ _ out.bounds).1
  have generated := sat
  rw [out.module_eq] at generated
  have modifiers := (rep.modifiers_source b fuel p primitive capacity shape model states valid
    r.model.modifiers out.primitive_modifiers out.modifiers out.modifiers_lowered).mp
      (fun f member => (generated.2.2.2.2.1 f (by
        simp only [generatedModule, List.mem_append]; exact Or.inr member)).2)
  exact ⟨decoded, read, (sourceResult_iff _ _ _).mpr
    ⟨(sourceModel_satisfies _ _ _).mpr ⟨valid, modifiers, constraintCommand.1⟩, constraintCommand.2⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Assembly lemma separating target arithmetic totality from semantic
preservation. The public completeness theorem discharges these two definedness
premises from the successful compiler's checked output. -/
theorem compiled_complete_of_defined (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (out : CompileOutput r b fuel c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (fit : Fits r.model.structural p source b)
    (satisfies : SourceResult r completeIntegers (completeTrace r.model.structural p source))
    (defined : ∀ f ∈ out.constraints ++ out.modifiers,
      f.Defined (schema r.model.structural) b.bitwidth (encode source).unfold [] 0)
    (commandDefined : out.body.Defined (schema r.model.structural) b.bitwidth (encode source).unfold [] 0) :
    Lasso.Satisfies c.module.raw (encode source) := by
  obtain ⟨sourceModel, _⟩ := (sourceResult_iff _ _ _).mp satisfies
  obtain ⟨valid, sourceModifiers, _⟩ := (sourceModel_satisfies _ _ _).mp sourceModel
  have shape := (validateBounds_properties _ _ out.bounds).1
  obtain ⟨rep, model⟩ := encoded_modelRows r.model.structural b p primitive shape source fit valid
  obtain ⟨_, _, _, states, _⟩ := encode_structural_complete r.model.structural p primitive shape source
    b.bitwidth b.objects fit.structural valid
  have modifiers := (rep.modifiers_source b fuel p primitive fit.structural.capacity shape model states valid
    r.model.modifiers out.primitive_modifiers out.modifiers out.modifiers_lowered).mpr sourceModifiers
  obtain ⟨constraints, command⟩ := encoded_constraints_command r b fuel c out p primitive source fit satisfies
  obtain ⟨declarations, scopes, fields, structuralFacts⟩ := encode_full_structure r.model.structural p primitive
    shape source b fit.structural fit.scopes valid
  unfold Lasso.Satisfies
  rw [out.module_eq]
  refine ⟨encode_fits fit out.kind out.body, ?_⟩
  refine ⟨?_, ?_, declarations, scopes, ?_, commandDefined, command, fields⟩
  · rw [← out.module_eq]; exact c.module.typed
  · rw [← out.module_eq]; exact c.module.bounded
  · intro f member
    change f ∈ (_ ++ out.constraints) ++ out.modifiers at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · have holds := structuralFacts f member
        exact ⟨structuralFacts_defined_of_holds r.model.structural b f member holds, holds⟩
      · exact ⟨defined f (List.mem_append_left _ member), constraints f member⟩
    · exact ⟨defined f (List.mem_append_right _ member), modifiers f member⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every source witness fitting the explicit occurrence, scalar, structural
count, declaration-scope and lasso-length budgets is realized by the concrete
encoder as a satisfying output of the actual compiler. Target formula truth
and target arithmetic definedness are conclusions, not fitting premises. -/
theorem compiled_complete (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (fit : Fits r.model.structural p source b)
    (satisfies : SourceResult r completeIntegers (completeTrace r.model.structural p source)) :
    Lasso.Satisfies c.module.raw (encode source) := by
  obtain ⟨out⟩ := compile_output r b fuel c success
  exact compiled_complete_of_defined r b fuel c out p primitive source fit satisfies
    (out.behavioral_defined (encode source).unfold [] 0)
    (out.command_defined (encode source).unfold [] 0)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Bounded completeness for the original source carrier and mathematical
integer realization. One global finite observation correspondence supplies the
lasso tables; source satisfaction is transported by the proved source meaning,
and the concrete encoder constructs the satisfying target witness. -/
theorem compiled_complete_observed {U : Type}
    (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (fit : Fits r.model.structural p source b)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (objects : Fin o ↪ U)
    (observed : ObservesCompletion r.model.structural p source τ R objects)
    (satisfies : SourceResult r R τ) :
    Lasso.Satisfies c.module.raw (encode source) :=
  compiled_complete r b fuel c success p primitive source fit (observed.sourceResult r satisfies)

end ClaferCompiler.Correctness.Behavioral.Full
