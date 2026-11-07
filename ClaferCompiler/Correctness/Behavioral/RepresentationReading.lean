module

public import ClaferCompiler.Correctness.Behavioral.RepresentationDecoding
public import ClaferCompiler.Correctness.Behavioral.RepresentationInvariants

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Behavioral

theorem mapM_ok_map (xs : List α) (f : α → Except ε β) (g : α → β)
    (h : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

-- [proof->req~compiler-trace-representation~1]
theorem labelIndex_self (objects : Vector Nat o)
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y) (x : Fin o) :
    labelIndex objects objects[x] = .ok x := by
  unfold labelIndex
  cases hf : (List.finRange o).find? (fun i => objects[i] == objects[x]) with
  | none =>
    have hn := List.find?_eq_none.mp hf x (List.mem_finRange x)
    simp at hn
  | some y =>
    have hp := List.find?_some hf
    have hy : y = x := unique y x (by simpa using hp)
    subst y
    rfl

theorem readPair_self (objects : Vector Nat o)
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y) (x y : Fin o) :
    readPair objects [objects[x], objects[y]] = .ok (x, y) := by
  change (labelIndex objects objects[x] >>= fun a => labelIndex objects objects[y] >>= fun b =>
    Except.ok (a, b)) = .ok (x, y)
  rw [labelIndex_self objects unique x]
  change (labelIndex objects objects[y] >>= fun b => Except.ok (x, b)) = .ok (x, y)
  rw [labelIndex_self objects unique y]
  rfl

theorem readPairs_success (objects : Vector Nat o)
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y)
    (rows : List (List Nat))
    (typed : ∀ row ∈ rows, ∃ x y : Fin o, row = [objects[x], objects[y]]) :
    ∃ pairs : List (Fin o × Fin o), rows.mapM (readPair objects) = .ok pairs ∧
      pairs.map (fun p => [objects[p.1], objects[p.2]]) = rows := by
  induction rows with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons row rows ih =>
    obtain ⟨x, y, rfl⟩ := typed row List.mem_cons_self
    obtain ⟨pairs, hp, he⟩ := ih (fun row hr => typed row (List.mem_cons_of_mem _ hr))
    refine ⟨(x, y) :: pairs, ?_, ?_⟩
    · rw [List.mapM_cons, readPair_self objects unique x y, hp]
      rfl
    · change [objects[x], objects[y]] :: pairs.map _ = _
      rw [he]

theorem readParent_success (pairs : List (Fin o × Fin o)) (hn : pairs.Nodup)
    (functional : ∀ x p q, (x, p) ∈ pairs → (x, q) ∈ pairs → p = q)
    (x : Fin o) :
    ∃ parent, readParent pairs x = .ok parent ∧
      ∀ p, parent = some p ↔ (x, p) ∈ pairs := by
  let ps := (pairs.filter fun p => p.1 == x).map Prod.snd
  have members (p : Fin o) : p ∈ ps ↔ (x, p) ∈ pairs := by
    simp only [ps, List.mem_map, List.mem_filter, beq_iff_eq, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
      exact hab
    · intro hp
      exact ⟨x, p, ⟨hp, rfl⟩, rfl⟩
  have nodup : ps.Nodup := by
    apply List.Nodup.map_on _ (hn.filter _)
    intro a ha b hb he
    exact Prod.ext ((beq_iff_eq.mp (List.mem_filter.mp ha).2).trans
      (beq_iff_eq.mp (List.mem_filter.mp hb).2).symm) he
  have equal (p q : Fin o) (hp : p ∈ ps) (hq : q ∈ ps) : p = q :=
    functional x p q ((members p).mp hp) ((members q).mp hq)
  change ∃ parent, (match ps with
    | [] => Except.ok none
    | [p] => .ok (some p)
    | _ => .error DecodeError.malformedIdentities) = .ok parent ∧ _
  cases he : ps with
  | nil =>
    refine ⟨none, rfl, ?_⟩
    intro p
    rw [← members p, he]
    simp
  | cons p rest =>
    cases rest with
    | nil =>
      refine ⟨some p, rfl, ?_⟩
      intro q
      rw [← members q, he]
      simp [eq_comm]
    | cons q rest =>
      have hp : p ∈ ps := by simp [he]
      have hq : q ∈ ps := by simp [he]
      have hpq := equal p q hp hq
      subst q
      simp [he] at nodup

theorem ancestor_antisymm (v : IR.Structural.Layout k) (a b : Fin k)
    (hab : (SemanticsBridge.Structural.interpret v.core).Ancestor a b)
    (hba : (SemanticsBridge.Structural.interpret v.core).Ancestor b a) : a = b := by
  rcases hab.cases_head with he | ⟨c, hc, path⟩
  · exact he
  · exact (no_reverse_super v c a hc (path.trans hba)).elim

-- [proof->req~compiler-trace-representation~1]
/-- The executable direct-type reader recovers the most specific occupied type,
including concrete types whose supertype is concrete. -/
theorem typeCandidates_exact (v : IR.Structural.Layout k) (state : Backend.Alloy.Instance)
    (label : Nat) (actual : Fin k) (concrete : (v.core.get actual).isAbstract = false)
    (pools : ∀ d : Fin k, label ∈ state.signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] ↔
      IR.Behavioral.ancestor v.core actual d = true) :
    typeCandidates v state label = [actual] := by
  unfold typeCandidates
  have predicate (d : Fin k) :
      (!(v.core.get d).isAbstract &&
      (state.signatures[Backend.Alloy.Structural.signatureId v d]?.getD []).contains label &&
      (List.finRange k).all (fun e => e == d ||
        !(IR.Behavioral.ancestor v.core e d &&
          (state.signatures[Backend.Alloy.Structural.signatureId v e]?.getD []).contains label))) =
        (d == actual) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, List.all_eq_true,
      List.mem_finRange, forall_true_left, Bool.or_eq_true, beq_iff_eq, pools,
      Bool.eq_false_iff]
    constructor
    · rintro ⟨⟨_, ha⟩, hm⟩
      rcases hm actual with he | hn
      · exact he.symm
      · apply False.elim
        apply hn
        exact Bool.and_eq_true_iff.mpr ⟨ha, List.contains_iff_mem.mpr
          ((pools actual).mpr ((SemanticsBridge.Behavioral.ancestor_agrees _ _ _).mpr .refl))⟩
    · intro he
      subst d
      refine ⟨⟨by simp [concrete], (SemanticsBridge.Behavioral.ancestor_agrees _ _ _).mpr .refl⟩, ?_⟩
      intro e
      by_cases he : e = actual
      · exact Or.inl he
      · apply Or.inr
        intro hn
        obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hn
        have hb := (pools e).mp (List.contains_iff_mem.mp hb)
        exact he (ancestor_antisymm v e actual
          ((SemanticsBridge.Behavioral.ancestor_agrees _ _ _).mp ha)
          ((SemanticsBridge.Behavioral.ancestor_agrees _ _ _).mp hb))

  rw [List.filter_congr (fun d _ => predicate d), List.filter_beq]
  simp [List.Nodup.count (List.nodup_finRange k)]

theorem readType_exact (v : IR.Structural.Layout k) (state : Backend.Alloy.Instance)
    (label : Nat) (actual : Fin k) (concrete : (v.core.get actual).isAbstract = false)
    (pools : ∀ d : Fin k, label ∈ state.signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] ↔
      IR.Behavioral.ancestor v.core actual d = true) :
    readType v state label = .ok actual := by
  rw [readType, typeCandidates_exact v state label actual concrete pools]

theorem readType_encode (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (concrete : ∀ x : Fin o, (v.core.get ids.directType[x]).isAbstract = false) (x : Fin o) :
    readType v (encodeState v ids f) ids.ids[x] = .ok ids.directType[x] := by
  apply readType_exact _ _ _ _ (concrete x)
  intro d
  rw [encode_pool]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    exact unique y x he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem readIdentities_success (v : IR.Structural.Layout k) (state : Backend.Alloy.Instance)
    (objects : Vector Nat o) (root : Fin o) (types : Fin o → Fin k)
    (pairs : List (Fin o × Fin o)) (parents : Fin o → Option (Fin o))
    (unique : ∀ x y : Fin o, objects[x] = objects[y] → x = y)
    (hr : state.signatures[Backend.Alloy.Structural.signatureId v v.core.root]?.getD [] = [objects[root]])
    (ht : ∀ x, readType v state objects[x] = .ok (types x))
    (hp : (state.fields[0]?.getD []).mapM (readPair objects) = .ok pairs)
    (hparents : ∀ x, readParent pairs x = .ok (parents x)) :
    readIdentities v state objects = .ok
      { ids := objects, root, directType := Vector.ofFn types, parent := Vector.ofFn parents } := by
  have typesRead := mapM_ok_map (List.finRange o) (fun x => readType v state objects[x]) types (fun x _ => ht x)
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

end ClaferCompiler.Correctness.Behavioral
