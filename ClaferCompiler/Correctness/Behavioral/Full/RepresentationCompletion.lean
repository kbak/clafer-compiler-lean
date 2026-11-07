module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationTables
public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationDecoding

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral (sameTables sameRelation)

theorem target_static_checks (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace)
    (decl : τ.Declarations (schema v)) (t : Nat) :
    (sameTables (τ.state t).signatures (τ.state 0).signatures &&
      sameRelation ((τ.state t).fields[0]?.getD []) ((τ.state 0).fields[0]?.getD [])) = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply sameTables_complete _ _
    · exact (table_lengths v _ (decl.2.1 t).1).1.trans
        (table_lengths v _ (decl.2.1 0).1).1.symm
    · exact target_signature_static v τ decl t
  · exact sameRelation_complete _ _ (decl.2.2.2.1 0 rfl t)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem target_readFrame (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (decl : τ.Declarations (schema v))
    (ids : IR.Behavioral.Identities k ((τ.state 0).signatures[0]?.getD []).length)
    (data : TargetIdentityData v (τ.state 0) (targetObjects τ) ids) (t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w τ [] t)
    (scalar : (τ.state t).scalarFields w (schema v).declarations = true) :
    ∃ frame values, readFrame ids (τ.state t) = .ok frame ∧
      readValues ids (τ.state t) = .ok values ∧
      sameState (τ.state t) (encodeState ids frame values) = true := by
  have objects (label : Nat) : label ∈ (τ.state t).signatures[0]?.getD [] ↔
      ∃ x : Fin ((τ.state 0).signatures[0]?.getD []).length, label = ids.ids[x] := by
    rw [target_signature_static v τ decl t 0, targetObjects_members, data.labels]
  have liveTyped (row) (hr : row ∈ (τ.state t).fields[1]?.getD []) :
      ∃ x : Fin ((τ.state 0).signatures[0]?.getD []).length, row = [ids.ids[ids.root], ids.ids[x]] := by
    obtain ⟨label, he, hm⟩ := target_live_rows v w τ decl _ data.rootSig t facts row hr
    obtain ⟨x, rfl⟩ := (objects label).mp hm
    exact ⟨x, he⟩
  have refTyped (d : Fin k) (row) (hr : row ∈ (τ.state t).fields[2 + d.val]?.getD []) :
      ∃ x y : Fin ((τ.state 0).signatures[0]?.getD []).length, row = [ids.ids[x], ids.ids[y]] := by
    obtain ⟨a, b, he, ha, hb⟩ := target_reference_rows v τ t
      (decl.2.1 t).1 (decl.2.1 t).2.1 d row hr
    obtain ⟨x, rfl⟩ := (objects a).mp ha
    obtain ⟨y, rfl⟩ := (objects b).mp hb
    exact ⟨x, y, he⟩
  obtain ⟨frame, read, lives, references⟩ :=
    readFrame_success ids (τ.state t) data.unique liveTyped refTyped
  obtain ⟨values, readValues, scalars⟩ := readValues_success v ids (τ.state t) w objects scalar
  refine ⟨frame, values, read, readValues,
    encodeState_agrees v ids frame values (τ.state t) (decl.2.1 t).1 objects ?_ ?_ ?_ ?_ scalars⟩
  · intro d label
    exact (target_signature_static v τ decl t _ label).trans (data.pools d label)
  · intro row
    exact (decl.2.2.2.1 0 rfl t row).trans (data.parents row)
  · intro row
    constructor
    · intro hr
      obtain ⟨x, rfl⟩ := liveTyped row hr
      exact ⟨x, (lives x).mpr hr, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (lives x).mp hx
  · intro d row
    constructor
    · intro hr
      obtain ⟨x, y, rfl⟩ := refTyped d row hr
      exact ⟨x, y, (references d x y).mpr hr, rfl⟩
    · rintro ⟨x, y, hxy, rfl⟩
      exact (references d x y).mp hxy

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The decoder accepts every target with valid declaration tables and the
generated identity facts. This construction inspects the actual finite frames;
it does not assume source validity or a representation witness. -/
theorem target_decode_exists (v : IR.BehavioralStructural.Validated k) (w : Nat) (target : Temporal.Lasso)
    (decl : target.unfold.Declarations (schema v))
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (states : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (scalar : ∀ t, (target.unfold.state t).scalarFields w (schema v).declarations = true) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode v target = .ok decoded := by
  have nonempty := target.nonempty
  let τ : Temporal.Trace := ⟨target.inventory, fun t => match t with
    | 0 => target.frames[0]'(target.nonempty)
    | n + 1 => target.unfold.state (n + 1)⟩
  have stateEq (t : Nat) : τ.state t = target.unfold.state t := by
    cases t with
    | zero => exact (target_unfold_frame target ⟨0, target.nonempty⟩).symm
    | succ => rfl
  have traceEq : τ = target.unfold := by
    apply congrArg (Temporal.Trace.mk target.inventory)
    exact funext stateEq
  have declτ : τ.Declarations (schema v) := traceEq.symm ▸ decl
  have factsτ : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0 := traceEq.symm ▸ facts
  obtain ⟨ids, data⟩ := target_readIdentities v w τ declτ factsτ
  have frameExists (i : Fin target.frames.length) :
      ∃ frame values, readFrame ids target.frames[i.val] = .ok frame ∧
        readValues ids target.frames[i.val] = .ok values ∧
        sameState target.frames[i.val] (encodeState ids frame values) = true := by
    have h := target_readFrame v w τ declτ ids data i.val
      (traceEq.symm ▸ states i.val) (by rw [stateEq]; exact scalar i.val)
    rw [stateEq i.val, target_unfold_frame target i] at h
    exact h
  choose frames values frameRead valueRead frameChecks using frameExists
  let frameList := (List.finRange target.frames.length).map frames
  have frameLength : frameList.length = target.frames.length := by simp [frameList]
  let valueList := (List.finRange target.frames.length).map values
  have valueLength : valueList.length = frameList.length := by simp [valueList, frameLength]
  have loopValid : target.loop < frameList.length := by rw [frameLength]; exact target.loopValid
  let objectSource : IR.Behavioral.Lasso k (target.frames[0].signatures[0]?.getD []).length
      frameList.length :=
    ⟨ids, Vector.ofFn (fun i => frameList[i.val]), ⟨target.loop, loopValid⟩⟩
  let source : ObservedLasso k (target.frames[0].signatures[0]?.getD []).length frameList.length :=
    ⟨objectSource, Vector.ofFn (fun i => valueList[i.val]'(by rw [valueLength]; exact i.isLt))⟩
  have wf : target.frames.all (fun s => s.wellFormed (schema v).declarations) = true := by
    apply List.all_eq_true.mpr
    intro state hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    simpa only [target_unfold_frame target ⟨i, hi⟩] using (decl.2.1 i).1
  have static : target.frames.all (fun s =>
      sameTables s.signatures target.frames[0].signatures &&
      sameRelation (s.fields[0]?.getD []) (target.frames[0].fields[0]?.getD [])) = true := by
    apply List.all_eq_true.mpr
    intro state hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    simpa only [target_unfold_frame target ⟨i, hi⟩, target_unfold_frame target ⟨0, target.nonempty⟩]
      using target_static_checks v target.unfold decl i
  have readFrames : target.frames.mapM (readFrame ids) =
      .ok frameList := by
    conv_lhs => rw [← list_finRange_get target.frames]
    rw [List.mapM_map]
    exact mapM_ok_map _ _ frames (fun i _ => frameRead i)
  have readValueList : target.frames.mapM (readValues ids) = .ok valueList := by
    conv_lhs => rw [← list_finRange_get target.frames]
    rw [List.mapM_map]
    exact mapM_ok_map _ _ values (fun i _ => valueRead i)
  have raw : decodeRaw v target = .ok ⟨_, _, source⟩ := by
    unfold decodeRaw
    simp only [wf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure,
      Except.pure, bind, Except.bind]
    have hread : readIdentities v target.frames[0]
        (Vector.ofFn fun i => (target.frames[0].signatures[0]?.getD [])[i]) = .ok ids := data.read
    rw [hread]
    dsimp only [bind, Except.bind]
    rw [static]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [readFrames]
    dsimp only [bind, Except.bind]
    rw [readValueList]
    dsimp only [bind, Except.bind]
    rw [dite_eq_left loopValid, dite_eq_left valueLength]
    rfl
  have checked : roundTripChecks v source target = true := by
    have unique : (∀ x y : Fin (target.frames[0].signatures[0]?.getD []).length,
      ids.ids[x] = ids.ids[y] → x = y) := data.unique
    have rootOnly : (∀ x : Fin (target.frames[0].signatures[0]?.getD []).length,
      ids.directType[x] = v.core.structural.root → x = ids.root) := data.rootOnly
    simp only [roundTripChecks, source, objectSource, frameLength, beq_self_eq_true, Bool.true_and,
      decide_eq_true unique, decide_eq_true data.rootType, decide_eq_true rootOnly]
    apply List.all_eq_true.mpr
    intro i _
    let j : Fin target.frames.length := ⟨i.val, by rw [← frameLength]; exact i.isLt⟩
    simpa [frameList, valueList, List.getElem_map, j, List.getElem?_eq_getElem j.isLt] using frameChecks j
  refine ⟨⟨_, _, source⟩, ?_⟩
  unfold decode
  rw [raw]
  dsimp only [bind, Except.bind]
  rw [checked]
  rfl

end ClaferCompiler.Correctness.Behavioral.Full
