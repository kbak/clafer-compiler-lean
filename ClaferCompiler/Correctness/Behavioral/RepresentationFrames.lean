module

public import ClaferCompiler.Correctness.Behavioral.RepresentationReading

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Behavioral

theorem flatMapM_ok_flatMap (xs : List α) (f : α → Except ε (List β)) (g : α → List β)
    (h : ∀ x ∈ xs, f x = .ok (g x)) : xs.flatMapM f = .ok (xs.flatMap g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMapM_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem readLive_self (ids : IR.Behavioral.Identities k o) (x : Fin o) :
    readLive ids [ids.ids[ids.root], ids.ids[x]] = .ok ids.ids[x] := by
  unfold readLive
  simp only [beq_self_eq_true, Bool.true_and, List.contains_iff_mem]
  simp

theorem readLives_success (ids : IR.Behavioral.Identities k o) (rows : List (List Nat))
    (typed : ∀ row ∈ rows, ∃ x : Fin o, row = [ids.ids[ids.root], ids.ids[x]]) :
    ∃ labels : List Nat, rows.mapM (readLive ids) = .ok labels ∧
      labels.map (fun x => [ids.ids[ids.root], x]) = rows := by
  induction rows with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons row rows ih =>
    obtain ⟨x, rfl⟩ := typed row List.mem_cons_self
    obtain ⟨labels, hp, he⟩ := ih (fun row hr => typed row (List.mem_cons_of_mem _ hr))
    refine ⟨ids.ids[x] :: labels, ?_, ?_⟩
    · rw [List.mapM_cons, readLive_self ids x, hp]
      rfl
    · change [ids.ids[ids.root], ids.ids[x]] :: labels.map _ = _
      rw [he]

-- [proof->req~compiler-trace-representation~1]
theorem readFrame_success (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (state : Backend.Alloy.Instance)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (liveTyped : ∀ row ∈ state.fields[1]?.getD [],
      ∃ x : Fin o, row = [ids.ids[ids.root], ids.ids[x]])
    (refTyped : ∀ d : Fin k, ∀ row ∈ state.fields[2 + d.val]?.getD [],
      ∃ x y : Fin o, row = [ids.ids[x], ids.ids[y]]) :
    ∃ frame : IR.Behavioral.Frame k o, readFrame v ids state = .ok frame ∧
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

end ClaferCompiler.Correctness.Behavioral
