module

public import ClaferCompiler.Correctness.Behavioral.Full.IntegersFolds

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
namespace IntegerFold
variable {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

def sourceValue (op : IR.BehavioralArithmetic.Fold) (sources : List (Option Int)) : Option Int :=
  (sources.mapM id).map fun zs => zs.foldl (scalar op) (initial op)

theorem observations_built
    (observations : List.Forall₂ (IntegerObservation s w τ e t) sources values) :
    ∀ v ∈ values, Full.Value.Built v := by
  induction observations with
  | nil => simp
  | cons obs _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact obs.built
    · exact ih v hv

theorem mapM_id_eq (sources : List (Option Int)) (zs : List Int) :
    sources.mapM id = some zs ↔ sources = zs.map some := by
  induction sources generalizing zs with
  | nil => cases zs <;> simp
  | cons a rest ih =>
    cases a <;> cases zs <;> cases hm : rest.mapM id <;> simp_all

theorem observation_values
    (observations : List.Forall₂ (IntegerObservation s w τ e t) sources values)
    (meanings : List.Forall₂ (Full.Value.Meaning s w τ e t) values terms) :
    ∃ zs, sources = zs.map some ∧
      List.Forall₂ (fun n z => Arithmetic.Term n ∧ n.eval s w τ e t = some z) terms zs := by
  induction observations generalizing terms with
  | nil => cases meanings; exact ⟨[], rfl, .nil⟩
  | @cons source value sources values obs observations ih =>
    cases meanings with
    | cons hm rest =>
      obtain ⟨z, hz, ht, he⟩ := obs.sound _ hm
      obtain ⟨zs, hzs, representations⟩ := ih rest
      exact ⟨z :: zs, by simp [hz, hzs], .cons ⟨ht, he⟩ representations⟩

theorem observations_complete {zs : List Int}
    (observations : List.Forall₂ (IntegerObservation s w τ e t) (zs.map some) values) :
    ∃ terms, List.Forall₂ (Full.Value.Meaning s w τ e t) values terms := by
  induction zs generalizing values with
  | nil => cases observations; exact ⟨[], .nil⟩
  | cons z zs ih =>
    cases observations with
    | cons obs rest =>
      obtain ⟨n, hn⟩ := obs.complete z rfl
      obtain ⟨ns, hns⟩ := ih rest
      exact ⟨n :: ns, .cons hn hns⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The emitted strict occurrence fold preserves every operand position. The
checked conservative range covers each prefix, including the empty identity. -/
theorem observation (op : IR.BehavioralArithmetic.Fold)
    (observations : List.Forall₂ (IntegerObservation s w τ e t) sources values)
    (range : IR.Expr.Interval) (budget : Nat)
    (size : sources.length ≤ budget)
    (bounds : ∀ source ∈ sources, ∀ z, source = some z → range.Contains z)
    (checked : (IR.Behavioral.Expression.Ranges.foldRange op budget range).fits w = true) :
    IntegerObservation s w τ e t (sourceValue op sources) (integerFold op values) := by
  have builtValues := observations_built observations
  refine ⟨built op values builtValues, ?_, ?_⟩
  · intro n hn
    obtain ⟨terms, meanings, rfl⟩ := (meaning op values builtValues).mp hn
    obtain ⟨zs, sourceEq, represented⟩ := observation_values observations meanings
    have size' : zs.length ≤ budget := by simpa [sourceEq] using size
    have bounds' : ∀ z ∈ zs, range.Contains z := by
      intro z hz
      exact bounds (some z) (by rw [sourceEq]; exact List.mem_map.mpr ⟨z, hz, rfl⟩) z rfl
    have fit0 : Backend.Alloy.fitsInt w (initial op) = true := by
      simpa using prefixes_fit op range checked size' bounds' [] (by simp)
    obtain ⟨term, eval⟩ := term_eval op represented (.literal _)
      ((Backend.Alloy.boundedInt_some_iff _ _).mpr fit0)
      (prefixes_fit op range checked size' bounds')
    refine ⟨_, ?_, term, eval⟩
    unfold sourceValue
    rw [(mapM_id_eq sources zs).mpr sourceEq]
    rfl
  · intro z hz
    obtain ⟨zs, collect, _⟩ := Option.map_eq_some_iff.mp hz
    have sourceEq := (mapM_id_eq sources zs).mp collect
    obtain ⟨terms, meanings⟩ := observations_complete (sourceEq ▸ observations)
    exact ⟨_, (meaning op values builtValues).mpr ⟨terms, meanings, rfl⟩⟩
end IntegerFold
end ClaferCompiler.Correctness.Behavioral.Full
