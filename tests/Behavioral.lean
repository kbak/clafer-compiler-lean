module

public import ClaferCompiler.SemanticsBridge.Behavioral
public import tests.BehavioralNative
public import Clafer.Behavioral.FormulaExamples

public section
namespace ClaferCompiler.Tests.Behavioral
open IR.Behavioral SemanticsBridge.Behavioral

-- [utest->req~compiler-behavioral-ir~1]
theorem admitted : ∃ v, admitBehavioral document = .ok v := by
  apply (admit_success_iff document).mpr
  decide

theorem trace_checked : traceChecks core cycling ∧ fits bounds cycling := by decide

-- [utest->req~compiler-behavioral-interpretation~1]
/-- Runtime tables reconstruct the independently checked upstream fixture. -/
theorem model_eq : SemanticsBridge.Structural.interpret core = Clafer.Behavioral.Examples.model := by
  unfold SemanticsBridge.Structural.interpret core Clafer.Behavioral.Examples.model
  congr 2 <;> funext d <;> fin_cases d <;> rfl

theorem pool_eq : identities pool = Clafer.Behavioral.Examples.pool := by
  unfold identities pool Clafer.Behavioral.Examples.pool
  congr 1 <;> funext x <;> fin_cases x <;> rfl

theorem index_mod (t : Nat) : cycling.index t = ⟨t % 4, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp only [Lasso.index, cycling]
  split
  · simp [Nat.mod_eq_of_lt (by assumption)]
  · simpa using (Nat.mod_eq_sub_mod (show 4 ≤ t by omega)).symm

theorem frame_at (t : Nat) : cycling.at t = frame ⟨t % 4, Nat.mod_lt _ (by decide)⟩ := by
  change (Vector.ofFn frame)[cycling.index t] = _
  simpa using congrArg frame (index_mod t)

theorem trace_eq : trace cycling = Clafer.Behavioral.Examples.cycling := by
  unfold trace Clafer.Behavioral.Examples.cycling
  congr 1
  · exact pool_eq
  · funext t
    ext x
    change (cycling.at t).live[x] = true ↔ _
    rw [frame_at]
    exact (by unfold Clafer.Behavioral.Examples.phaseLive; decide :
      ∀ (i : Fin 4) (x : Fin 8), (frame i).live[x] = true ↔
        Clafer.Behavioral.Examples.phaseLive i x) _ x
  · funext t d x y
    apply propext
    rw [frame_at]
    exact (by unfold Clafer.Behavioral.Examples.phaseDeref; decide :
      ∀ (i : Fin 4) (d : Fin 4) (x y : Fin 8),
        (d, x, y) ∈ (frame i).references ↔
          Clafer.Behavioral.Examples.phaseDeref i d x y) _ d x y

theorem valid_source_trace : (trace cycling).Admissible (SemanticsBridge.Structural.interpret core) := by
  rw [model_eq, trace_eq]
  exact Clafer.Behavioral.Examples.cycling_admissible

def source : Clafer.Behavioral.Environment (Fin 8) 0 := .closed 3
def observation := Clafer.Behavioral.Observation.sets Clafer.Behavioral.Examples.model Clafer.Behavioral.Examples.cycling

-- [utest->req~compiler-behavioral-interpretation~1]
/-- Both normalized source signs can hold on this admitted disappearing parent. -/
theorem both_signs :
    (formula (error.eventually.normalize true 256 (by decide) : Formula 4 0)).raw Clafer.Behavioral.Examples.cycling observation source 0 ∧
    (formula (error.eventually.normalize false 256 (by decide) : Formula 4 0)).raw Clafer.Behavioral.Examples.cycling observation source 0 := by
  constructor
  · apply (normalize_agrees Clafer.Behavioral.Examples.model Clafer.Behavioral.Examples.cycling error.eventually true source 0 256 (by decide)).mpr
    exact Clafer.Behavioral.Lifetime.eventually_cancel (by decide : 0 ≤ 2) (by
      simp [Clafer.Behavioral.Trace.ParentPresent, Clafer.Behavioral.Examples.cycling, Clafer.Behavioral.Examples.pool, Clafer.Behavioral.Examples.phaseLive, source, Clafer.Behavioral.Environment.closed])
  · apply (normalize_agrees Clafer.Behavioral.Examples.model Clafer.Behavioral.Examples.cycling error.eventually false source 0 256 (by decide)).mpr
    intro j _ _
    simp [Clafer.Behavioral.Formula.denote, Clafer.Behavioral.polarity, formula, error, atom, setExpr, Clafer.Behavioral.Observation.sets, Clafer.Behavioral.SetAtom.eval, Clafer.Behavioral.SetExpr.eval]

theorem source_death_not_cancellation :
    ¬ (formula (error.next : Formula 4 0)).denote Clafer.Behavioral.Examples.cycling observation true source 0 := by
  intro h
  have hp : Clafer.Behavioral.Examples.cycling.ParentPresent 3 1 := by
    simp [Clafer.Behavioral.Trace.ParentPresent, Clafer.Behavioral.Examples.cycling, Clafer.Behavioral.Examples.pool, Clafer.Behavioral.Examples.phaseLive]
  have bad := h hp
  simp [Clafer.Behavioral.Formula.denote, Clafer.Behavioral.polarity, formula, error, atom, setExpr, observation, Clafer.Behavioral.Observation.sets,
    Clafer.Behavioral.SetAtom.eval, Clafer.Behavioral.SetExpr.eval] at bad

theorem root_no_cancellation :
    ¬ (formula (error.eventually : Formula 4 0)).denote Clafer.Behavioral.Examples.cycling observation true (.closed 0) 0 := by
  rintro (⟨j, _, hn⟩ | ⟨_, _, _, ha⟩)
  · exact hn (Clafer.Behavioral.Examples.cycling.parentPresent_root j)
  · simp [Clafer.Behavioral.Formula.denote, Clafer.Behavioral.polarity, formula, error, atom, setExpr, observation, Clafer.Behavioral.Observation.sets,
      Clafer.Behavioral.SetAtom.eval, Clafer.Behavioral.SetExpr.eval] at ha

theorem persistent_parent_no_both (a : Atom 4 0) (t : Nat) :
    ¬ ((formula (.eventually (.atom a))).denote Clafer.Behavioral.Examples.cycling observation true (.closed 1) t ∧
      (formula (.not (.eventually (.atom a)))).denote Clafer.Behavioral.Examples.cycling observation true (.closed 1) t) := by
  rintro ⟨hp, hn⟩
  exact Clafer.Behavioral.Formula.persistent_eventually_consistent Clafer.Behavioral.Examples.cycling observation (atom a) (.closed 1) t
    (fun j _ => Or.inr ⟨0, rfl, Clafer.Behavioral.Examples.cycling_valid.root_live j⟩) hp hn

theorem no_resumption (j : Nat) (hj : 2 ≤ j) :
    ¬ Clafer.Behavioral.Lifetime.Through ((trace cycling).ParentPresent 3) 0 j := by
  apply Clafer.Behavioral.Lifetime.not_through_after_end (by decide : 0 ≤ 2) hj
  rw [trace_eq]
  simp [Clafer.Behavioral.Trace.ParentPresent, Clafer.Behavioral.Examples.cycling, Clafer.Behavioral.Examples.pool, Clafer.Behavioral.Examples.phaseLive]

theorem cannot_move_parent :
    ¬ ∃ τ : Clafer.Behavioral.Trace (Fin 4) (Fin 8), τ.ParentAt 0 1 3 ∧ τ.ParentAt 3 2 3 := by
  rintro ⟨τ, h0, h3⟩
  exact (by decide : (1 : Fin 8) ≠ 2) (τ.parent_stable h0 h3)

theorem nested_capture :
    let ρ : Environment 8 0 := .closed 3
    (((ρ.push (fun x => x == 3)).push (fun x => x == 5)).lookup 1) 3 = true ∧
    (((ρ.push (fun x => x == 3)).push (fun x => x == 5)).this) = 3 := by decide

end ClaferCompiler.Tests.Behavioral
