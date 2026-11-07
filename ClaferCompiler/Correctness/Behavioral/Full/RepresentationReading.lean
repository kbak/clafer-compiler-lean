module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationTarget
public import ClaferCompiler.Correctness.ExpressionScalarFacts

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral (readPair readParent readLive labelIndex DecodeError)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem readType_exact (state : Instance) (label : Nat) (actual : Fin k)
    (pools : ∀ d : Fin k, label ∈ state.signatures[signatureId d]?.getD [] ↔ actual = d) :
    readType state label = .ok actual := by
  have predicate (d : Fin k) :
      (state.signatures[signatureId d]?.getD []).contains label = (d == actual) := by
    have iff : (state.signatures[signatureId d]?.getD []).contains label = true ↔
        (d == actual) = true := by
      rw [List.contains_iff_mem, pools, beq_iff_eq]
      exact eq_comm
    exact Bool.eq_iff_iff.mpr iff
  unfold readType
  rw [List.filter_congr (fun d _ => predicate d), List.filter_beq]
  simp [List.Nodup.count (List.nodup_finRange k)]

theorem readIdentities_success (v : IR.BehavioralStructural.Validated k) (state : Backend.Alloy.Instance)
    (objects : Vector Nat o) (root : Fin o) (types : Fin o → Fin k)
    (pairs : List (Fin o × Fin o)) (parents : Fin o → Option (Fin o))
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y)
    (hr : state.signatures[signatureId v.core.structural.root]?.getD [] = [objects[root]])
    (ht : ∀ x, readType state objects[x] = .ok (types x))
    (hp : (state.fields[0]?.getD []).mapM (readPair objects) = .ok pairs)
    (hparents : ∀ x, readParent pairs x = .ok (parents x)) :
    readIdentities v state objects = .ok
      { ids := objects, root, directType := Vector.ofFn types, parent := Vector.ofFn parents } := by
  have typesRead := mapM_ok_map (List.finRange o) (fun x => readType state objects[x]) types (fun x _ => ht x)
  have parentsRead := mapM_ok_map (List.finRange o) (readParent pairs) parents (fun x _ => hparents x)
  unfold readIdentities
  simp only [hr]
  rw [labelIndex_self objects unique root]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [typesRead]
  dsimp only [bind, Except.bind]
  rw [hp]
  dsimp only [bind, Except.bind]
  rw [parentsRead]
  dsimp only [bind, Except.bind]
  simp [List.length_map, List.length_finRange, Vector.ofFn, List.getElem_map]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem readFrame_success (ids : IR.Behavioral.Identities k o)
    (state : Backend.Alloy.Instance)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (liveTyped : ∀ row ∈ state.fields[1]?.getD [],
      ∃ x : Fin o, row = [ids.ids[ids.root], ids.ids[x]])
    (refTyped : ∀ d : Fin k, ∀ row ∈ state.fields[2 + d.val]?.getD [],
      ∃ x y : Fin o, row = [ids.ids[x], ids.ids[y]]) :
    ∃ frame : IR.Behavioral.Frame k o, readFrame ids state = .ok frame ∧
      (∀ x : Fin o, frame.live[x] = true ↔ [ids.ids[ids.root], ids.ids[x]] ∈ state.fields[1]?.getD []) ∧
      (∀ (d : Fin k) (x y : Fin o), (d, x, y) ∈ frame.references ↔
        [ids.ids[x], ids.ids[y]] ∈ state.fields[2 + d.val]?.getD []) := by
  obtain ⟨labels, liveRead, liveRows⟩ := readLives_success ids _ liveTyped
  have refs : ∀ d : Fin k, ∃ pairs : List (Fin o × Fin o),
      (state.fields[2 + d.val]?.getD []).mapM (readPair ids.ids) = .ok pairs ∧
        pairs.map (fun p => [ids.ids[p.1], ids.ids[p.2]]) = state.fields[2 + d.val]?.getD [] :=
    fun d => readPairs_success ids.ids unique _ (refTyped d)
  choose pairs pairRead pairRows using refs
  let frame : IR.Behavioral.Frame k o :=
    ⟨Vector.ofFn (fun x => labels.contains ids.ids[x]),
      (List.finRange k).flatMap (fun d => (pairs d).map (fun p => (d, p)))⟩
  refine ⟨frame, ?_, ?_, ?_⟩
  · have refsRead := flatMapM_ok_flatMap (List.finRange k)
      (fun d => do
        let ps ← (state.fields[2 + d.val]?.getD []).mapM (readPair ids.ids)
        pure (ps.map (fun p => (d, p))))
      (fun d => (pairs d).map (fun p => (d, p))) (fun d _ => by rw [pairRead d]; rfl)
    unfold readFrame
    rw [liveRead]
    change ((List.finRange k).flatMapM (fun d => do
      let ps ← (state.fields[2 + d.val]?.getD []).mapM (readPair ids.ids)
      pure (ps.map (fun p => (d, p)))) >>= fun rs =>
        Except.ok ⟨Vector.ofFn (fun x => labels.contains ids.ids[x]), rs⟩) = .ok frame
    rw [refsRead]
    rfl
  · intro x
    change (Vector.ofFn (fun x => labels.contains ids.ids[x]))[x] = true ↔ _
    rw [← liveRows]
    simp
  · intro d x y
    change (d, x, y) ∈ (List.finRange k).flatMap (fun e => (pairs e).map (fun p => (e, p))) ↔ _
    rw [← pairRows d]
    constructor
    · intro h
      obtain ⟨e, _, he⟩ := List.mem_flatMap.mp h
      obtain ⟨p, hp, he⟩ := List.mem_map.mp he
      have ed := (Prod.mk.inj he).1
      have pxy := (Prod.mk.inj he).2
      subst e
      subst p
      exact List.mem_map.mpr ⟨(x, y), hp, rfl⟩
    · intro h
      obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      have hx := unique p.1 x (List.cons.inj he).1
      have hy := unique p.2 y (List.cons.inj (List.cons.inj he).2).1
      exact List.mem_flatMap.mpr ⟨d, List.mem_finRange _,
        List.mem_map.mpr ⟨p, hp, congrArg (fun p => (d, p)) (Prod.ext hx hy)⟩⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem readValues_success (v : IR.BehavioralStructural.Validated k)
    (ids : IR.Behavioral.Identities k o) (state : Instance) (w : Nat)
    (objects : ∀ label, label ∈ state.signatures[0]?.getD [] ↔ ∃ x : Fin o, label = ids.ids[x])
    (scalar : state.scalarFields w (schema v).declarations = true) :
    ∃ values : Vector Int o, readValues ids state = .ok values ∧
      ∀ row, row ∈ state.values[0]?.getD [] ↔ ∃ x : Fin o, row = (ids.ids[x], values[x]) := by
  obtain ⟨typed, keys, total⟩ := ExpressionMeaning.scalar_field_rows state w (schema v).declarations
    0 { isAbstract := true, scalar := true } rfl rfl scalar
  have existsValue (x : Fin o) := total ids.ids[x] ((objects _).mpr ⟨x, rfl⟩)
  choose values valueRows using existsValue
  have filter (x : Fin o) : (((state.values[0]?.getD []).filter
      (fun row => row.1 == ids.ids[x])).map Prod.snd).eraseDups = [values x] := by
    apply ExpressionMeaning.dedup_singleton
    intro value
    simp only [List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨row, ⟨hr, he⟩, rfl⟩
      have eq : row = (ids.ids[x], values x) :=
        List.inj_on_of_nodup_map keys hr (valueRows x) he
      exact congrArg Prod.snd eq
    · intro eq
      subst value
      exact ⟨(ids.ids[x], values x), ⟨valueRows x, rfl⟩, rfl⟩
  simp only [Fin.getElem_fin] at filter
  refine ⟨Vector.ofFn values, ?_, ?_⟩
  · simp [readValues, filter, Vector.ofFn, List.getElem_map]
    rfl
  · intro row
    constructor
    · intro hr
      obtain ⟨x, hx⟩ := (objects row.1).mp (typed row hr).1
      have eq : row = (ids.ids[x], values x) :=
        List.inj_on_of_nodup_map keys hr (valueRows x) hx
      exact ⟨x, by simpa using eq⟩
    · rintro ⟨x, rfl⟩
      simpa using valueRows x

end ClaferCompiler.Correctness.Behavioral.Full
