module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSoundness
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSyntax
public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationScopes

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full

def commandResult (r : Request k) (b : Bounds) (fuel : Nat) :
    Except IR.Structural.Diagnostic (CommandKind × Temporal.Formula) :=
  match r.command with
  | .check i => do pure (.check, ← constraint r.model.structural b fuel r.model.assertions[i])
  | .run scenario => do
    pure (.run, Expressions.all (← scenario.mapM (constraint r.model.structural b fuel)))

def generatedModule (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (constraints modifiers : List Temporal.Formula) (kind : CommandKind)
    (body : Temporal.Formula) : Temporal.Module where
  schema := schema v
  facts := identityFacts v ++ boundFacts v b ++
    (stateFacts v ++ [reachabilityFact v b.objects]).map (.unary .always) ++ constraints ++ modifiers
  command := ⟨kind, body, scopes v b, b.bitwidth, b.minSteps, b.maxSteps⟩

/-- Successful lowering results remain explicit, so later attachment proofs can
use the actual generated constraints, modifiers and selected command. -/
structure CompileOutput (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled) where
  constraints : List Temporal.Formula
  modifiers : List Temporal.Formula
  kind : CommandKind
  body : Temporal.Formula
  bounds : validateBounds r.model.structural b = .ok ()
  primitive_modifiers : ∀ d, integerDeclaration r.model.structural d = true →
    IR.Behavioral.Modifiers.effective r.model.structural r.model.modifiers d = []
  constraints_lowered : r.model.constraints.mapM (constraint r.model.structural b fuel) = .ok constraints
  modifiers_lowered : ((List.finRange k).flatMap fun d =>
    (IR.Behavioral.Modifiers.effective r.model.structural r.model.modifiers d).flatMap (modifierExpansions d)).mapM
      (fun (where_, formula) => attached r.model.structural b fuel (placement r.model.structural where_) formula) = .ok modifiers
  command_lowered : commandResult r b fuel = .ok (kind, body)
  module_eq : c.module.raw = generatedModule r.model.structural b constraints modifiers kind body
  declarations_eq : c.declarations = (List.finRange k).map (fun d =>
    ((r.model.structural.core.structural.get d).id, signatureId d, head r.model.structural d))

theorem target_check_raw (m : Temporal.Module) (c : Temporal.CheckedModule)
    (success : Temporal.check m = .ok c) : c.raw = m := by
  unfold Temporal.check at success
  split at success
  · split at success
    · cases success; rfl
    · contradiction
  · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem validateModifiers_properties (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List IR.Behavioral.Surface.Modifiers.Modifier) k)
    (success : validateModifiers v table = .ok ()) :
    ∀ d, integerDeclaration v d = true → IR.Behavioral.Modifiers.effective v table d = [] := by
  unfold validateModifiers at success
  split at success
  · rename_i all
    intro d primitive
    have row := List.all_eq_true.mp all d (List.mem_finRange d)
    simpa [primitive] using row
  · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem compile_output (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c) : Nonempty (CompileOutput r b fuel c) := by
  unfold compile at success
  cases hb : validateBounds r.model.structural b with
  | error err => simp [hb, bind, Except.bind] at success
  | ok value =>
    cases value
    simp only [hb, bind, Except.bind] at success
    cases ha : validateModifiers r.model.structural r.model.modifiers with
    | error err => simp [ha] at success
    | ok value =>
      cases value
      simp only [ha] at success
      cases hc : r.model.constraints.mapM (constraint r.model.structural b fuel) with
      | error err => simp [hc] at success
      | ok constraints =>
        simp only [hc] at success
        cases hm : ((List.finRange k).flatMap fun d =>
          (IR.Behavioral.Modifiers.effective r.model.structural r.model.modifiers d).flatMap (modifierExpansions d)).mapM
            (fun (where_, formula) => attached r.model.structural b fuel (placement r.model.structural where_) formula) with
        | error err => simp [hm] at success
        | ok modifiers =>
          simp only [hm] at success
          have commandSuccess : (commandResult r b fuel >>= fun result =>
            match Temporal.check (generatedModule r.model.structural b constraints modifiers result.1 result.2) with
            | .error .unsupportedBounds => throw (error "behavioral.target-bounds")
            | .error .malformedSyntax => throw (error "behavioral.internal-target")
            | .ok checked => pure ⟨checked, (List.finRange k).map fun d =>
              ((r.model.structural.core.structural.get d).id, signatureId d, head r.model.structural d)⟩) = .ok c := by
            cases hcmd : r.command with
            | check i =>
              cases hbody : constraint r.model.structural b fuel r.model.assertions[i] with
              | error err => simp only [hcmd, hbody] at success; cases success
              | ok formula =>
                cases htarget : Temporal.check (generatedModule r.model.structural b constraints modifiers .check formula) with
                | error err =>
                  have htarget' := htarget
                  unfold generatedModule at htarget'
                  cases err <;> simp only [hcmd, hbody, pure, Except.pure, htarget'] at success <;> cases success
                | ok checked =>
                  have htarget' := htarget
                  unfold generatedModule at htarget'
                  simpa only [commandResult, hcmd, hbody, bind, Except.bind, pure, Except.pure,
                    htarget, htarget'] using success
            | run scenario =>
              cases hbody : scenario.mapM (constraint r.model.structural b fuel) with
              | error err => simp only [hcmd, hbody] at success; cases success
              | ok formulas =>
                cases htarget : Temporal.check (generatedModule r.model.structural b constraints modifiers .run (Expressions.all formulas)) with
                | error err =>
                  have htarget' := htarget
                  unfold generatedModule at htarget'
                  cases err <;> simp only [hcmd, hbody, pure, Except.pure, htarget'] at success <;> cases success
                | ok checked =>
                  have htarget' := htarget
                  unfold generatedModule at htarget'
                  simpa only [commandResult, hcmd, hbody, bind, Except.bind, pure, Except.pure,
                    htarget, htarget'] using success
          cases hr : commandResult r b fuel with
          | error err => simp [hr, bind, Except.bind] at commandSuccess
          | ok result =>
            obtain ⟨kind, body⟩ := result
            simp only [hr, bind, Except.bind] at commandSuccess
            cases ht : Temporal.check (generatedModule r.model.structural b constraints modifiers kind body) with
            | error err => cases err <;> simp [ht] at commandSuccess
            | ok checked =>
              simp only [ht, pure, Except.pure, Except.ok.injEq] at commandSuccess
              subst c
              exact ⟨⟨constraints, modifiers, kind, body, hb, validateModifiers_properties _ _ ha, hc, hm, hr,
                target_check_raw _ _ ht, rfl⟩⟩

theorem validateBounds_properties (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (success : validateBounds v b = .ok ()) : PrimitiveShape v ∧ 0 < b.bitwidth ∧ b.bitwidth ≤ 16 := by
  unfold validateBounds at success
  split at success
  · rename_i hs
    simp only [bind, Except.bind] at success
    split at success
    · rename_i hb
      split at success
      ·
        simp only [decide_eq_true_eq] at hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact ⟨hs, hb.1.1.1.1.2, hb.1.1.1.2⟩
      · contradiction
    · split at success <;> contradiction
  · simp only [bind, Except.bind] at success
    split at success <;> split at success <;> contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Actual compiler satisfaction entails decoder success and upstream structural
validity on the completed mathematical-integer carrier. -/
theorem compiled_structural_sound (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Temporal.Lasso) (sat : Temporal.Satisfies c.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode r.model.structural target = .ok decoded ∧
      Clafer.Behavioral.Structural.Valid
        (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core)
        (completeTrace r.model.structural p decoded.2.2) := by
  obtain ⟨out⟩ := compile_output r b fuel c success
  obtain ⟨shape, positive, small⟩ := validateBounds_properties _ _ out.bounds
  rw [out.module_eq] at sat
  apply target_structural_sound r.model.structural p primitive shape b.bitwidth positive small b.objects target sat.2.2.1
  · intro f member
    exact (sat.2.2.2.2.1 f (by simp only [generatedModule, List.mem_append]; aesop)).2
  · intro t f member
    have temporal := (sat.2.2.2.2.1 (.unary .always f) (by
      simp only [generatedModule, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨f, List.mem_append_left _ member, rfl⟩))))).2
    exact (always_holds (stateFacts_built _ f member)).mp temporal t (Nat.zero_le t)
  · intro t
    have temporal := (sat.2.2.2.2.1 (.unary .always (reachabilityFact r.model.structural b.objects)) (by
      simp only [generatedModule, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩))))).2
    exact (always_holds (show (reachabilityFact r.model.structural b.objects).Built from .subset _ _)).mp temporal t (Nat.zero_le t)
  · exact sat.2.2.2.2.2.2.2

theorem TraceRep.capacity_of_scopes {v : IR.BehavioralStructural.Validated k}
    {source : ObservedLasso k o steps} {target : Temporal.Lasso}
    (rep : TraceRep v source target) (b : Bounds)
    (admittedScopes : target.unfold.InScope (scopes v b)) : o ≤ b.objects := by
  classical
  obtain ⟨used, unique, members, size⟩ := admittedScopes 0 ⟨b.objects, false⟩ rfl
  have subset : Finset.univ.image rep.label ⊆ used.toFinset := by
    intro label hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hl
    exact List.mem_toFinset.mpr ((members _).mpr ⟨0, (rep.objects x).property⟩)
  have cardinal := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ rep.label_injective,
    Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup unique] at cardinal
  exact cardinal.trans size

end ClaferCompiler.Correctness.Behavioral.Full
