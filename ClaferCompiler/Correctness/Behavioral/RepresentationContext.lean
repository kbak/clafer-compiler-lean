module

public import ClaferCompiler.Correctness.Behavioral.RepresentationRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps} {target : Lasso}

theorem exists_many_built (n : Nat) (body : Formula) (hb : body.Built) :
    (Nat.repeat (Formula.exists_ (.sig 0)) n body).Built := by
  induction n with
  | zero => exact hb
  | succ n ih => exact .exists_ _ ih

-- [proof->req~compiler-behavioral-correctness~1]
theorem exists_many_meaning (rep : TraceRep v source target) (w : Nat)
    (n : Nat) (body : Formula) (hb : body.Built) (e : Environment) (t : Nat) :
    (Nat.repeat (Formula.exists_ (.sig 0)) n body).Holds (schema v) w target.unfold e t ↔
      ∃ objects : List (Fin o), objects.length = n ∧
        body.Holds (schema v) w target.unfold
          (objects.map (fun x => .object (rep.label x)) ++ e) t := by
  induction n generalizing e with
  | zero => simp [Nat.repeat]
  | succ n ih =>
    simp only [Nat.repeat, Formula.Holds,
      Formula.fold_exists _ _ _ (exists_many_built n body hb)]
    change (∃ atom, [atom] ∈ (Rel.sig 0).eval (schema v) w target.unfold e t ∧
      (Nat.repeat (Formula.exists_ (.sig 0)) n body).Holds (schema v) w target.unfold (atom :: e) t) ↔ _
    constructor
    · rintro ⟨atom, ha, hbody⟩
      obtain ⟨x, _, he⟩ := (rep.objects_meaning w e t [atom]).mp ha
      have he : atom = .object (rep.label x) := List.cons.inj he |>.1
      subst atom
      obtain ⟨objects, hn, hp⟩ := (ih _).mp hbody
      exact ⟨objects ++ [x], by simp [hn], by simpa [Formula.Holds, List.map_append, List.append_assoc] using hp⟩
    · rintro ⟨objects, hn, hp⟩
      rcases objects.eq_nil_or_concat' with rfl | ⟨front, x, rfl⟩
      · simp at hn
      · refine ⟨.object (rep.label x), (rep.objects_meaning w e t _).mpr ⟨x, Set.mem_univ _, rfl⟩, ?_⟩
        apply (ih _).mpr
        exact ⟨front, by simpa using hn, by simpa [Formula.Holds, List.map_append, List.append_assoc] using hp⟩

theorem union_rows (rs : List Rel) (hrs : ∀ r ∈ rs, r.Term)
    (initial : Rel) (hi : initial.Term) (s : Schema) (w : Nat) (τ : Trace)
    (e : Environment) (t : Nat) (row : List Atom) :
    row ∈ (rs.foldl Rel.union initial).eval s w τ e t ↔
      row ∈ initial.eval s w τ e t ∨ ∃ r ∈ rs, row ∈ r.eval s w τ e t := by
  induction rs generalizing initial with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun q hq => hrs q (List.mem_cons_of_mem _ hq)) _ (.union hi (hrs r (List.mem_cons_self)))]
    rw [Rel.eval_union hi (hrs r (List.mem_cons_self))]
    simp only [List.mem_eraseDups, List.mem_append, List.mem_cons]
    aesop

theorem aliases_meaning (v : IR.Structural.Layout k) (w : Nat) (τ : Trace) (f : U → Nat)
    (objects : List U) (t : Nat) :
    Relations.Unary f {x | x ∈ objects}
      ((((List.range objects.length).map Rel.var).foldl Rel.union (.empty .unary)).eval
        (schema v) w τ (objects.map fun x => Atom.object (f x)) t) := by
  intro row
  rw [union_rows _ (by intro r hr; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr; exact .var _) _ (.empty _)]
  have hempty : (Rel.empty .unary).eval (schema v) w τ (objects.map fun x => Atom.object (f x)) t = [] := rfl
  rw [hempty]
  simp only [List.not_mem_nil, false_or, List.mem_map, List.mem_range, exists_exists_and_eq_and]
  constructor
  · rintro ⟨i, hi, hr⟩
    have he : (Rel.var i).eval (schema v) w τ (objects.map fun x => Atom.object (f x)) t =
        [[.object (f objects[i])]] := by
      change (((objects.map fun x => Atom.object (f x))[i]?).toList.map fun x => [x]) = _
      simp [hi]
    rw [he] at hr
    exact ⟨objects[i], List.getElem_mem hi, List.mem_singleton.mp hr⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i, hi, ?_⟩
    change [Atom.object (f x)] ∈ (((objects.map fun x => Atom.object (f x))[i]?).toList.map fun x => [x])
    simp [hi, he]

-- [proof->req~compiler-behavioral-correctness~1]
theorem coverPool_meaning (rep : TraceRep v source target) (w capacity : Nat)
    (body : Formula) (hb : body.Built) :
    (coverPool capacity body).Holds (schema v) w target.unfold [] 0 ↔
      ∃ objects : List (Fin o), objects.length = capacity ∧ (∀ x, x ∈ objects) ∧
        body.Holds (schema v) w target.unfold (objects.map fun x => .object (rep.label x)) 0 := by
  unfold coverPool
  rw [exists_many_meaning rep w capacity _ (.binary .conj (.equal _ _) hb)]
  constructor
  · rintro ⟨objects, hn, h⟩
    simp only [List.append_nil] at h
    rw [← hn] at h
    change (Formula.binary .conj _ body).Holds _ _ _ _ _ at h
    simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ (.equal _ _) hb] at h
    change (Formula.equal _ _).Holds _ _ _ _ _ ∧ body.Holds _ _ _ _ _ at h
    have he := (Relations.unary_equal rep.label_injective
      (aliases_meaning v w target.unfold rep.label objects 0)
      (rep.objects_meaning w (objects.map fun x => .object (rep.label x)) 0)).mp h.1
    refine ⟨objects, hn, ?_, h.2⟩
    intro x
    have hx : x ∈ ({y | y ∈ objects} : Set (Fin o)) := he.symm ▸ Set.mem_univ x
    exact hx
  · rintro ⟨objects, hn, hc, hp⟩
    refine ⟨objects, hn, ?_⟩
    simp only [List.append_nil]
    rw [← hn]
    simp only [Formula.Holds, Formula.fold_binary _ _ _ _ _ (.equal _ _) hb]
    change (Formula.equal _ _).Holds _ _ _ _ _ ∧ body.Holds _ _ _ _ _
    refine ⟨?_, hp⟩
    apply (Relations.unary_equal rep.label_injective
      (aliases_meaning v w target.unfold rep.label objects 0)
      (rep.objects_meaning w (objects.map fun x => .object (rep.label x)) 0)).mpr
    ext x
    simp [hc x]

theorem padded_enumeration (source : IR.Behavioral.Lasso k o steps) (capacity : Nat) (h : o ≤ capacity) :
    ∃ objects : List (Fin o), objects.length = capacity ∧ ∀ x, x ∈ objects := by
  refine ⟨List.finRange o ++ List.replicate (capacity - o) source.identities.root, ?_, ?_⟩
  · simp only [List.length_append, List.length_finRange, List.length_replicate]
    omega
  · intro x
    exact List.mem_append_left _ (List.mem_finRange x)

-- [proof->req~compiler-behavioral-correctness~1]
/-- The exact initial context generated by `attached`. Every alias denotes one
fixed identity, and the finite enumeration may repeat entries for scope padding. -/
theorem attachmentContext (v : IR.Structural.Layout k) (w : Nat) (τ : Trace)
    (f : U → Nat) (owner : U) (objects : List U) (covers : ∀ x, x ∈ objects) :
    ContextRep v w τ f
      ⟨.var 0, Fin.elim0, (List.range objects.length).map fun i => .var (i + 1)⟩
      ⟨owner, Fin.elim0⟩ (.object (f owner) :: objects.map fun x => Atom.object (f x)) := by
  have aliasAt (i : Nat) (hi : i < objects.length) :
      Frozen v w τ f (.object (f owner) :: objects.map fun x => Atom.object (f x))
        (.var (i + 1)) {objects[i]} := by
    refine ⟨.var _, ?_⟩
    intro t row
    change row ∈ (((.object (f owner) :: objects.map fun x => Atom.object (f x))[i + 1]?).toList.map
      fun x => [x]) ↔ ∃ x ∈ ({objects[i]} : Set U), row = [.object (f x)]
    simp [hi]
  constructor
  · refine ⟨.var 0, ?_⟩
    intro t
    exact Relations.unary_singleton owner
  · intro i
    exact Fin.elim0 i
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact ⟨objects[i]'(List.mem_range.mp hi), aliasAt i (List.mem_range.mp hi)⟩
  · intro x
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp (covers x)
    refine ⟨.var (i + 1), List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_⟩
    simpa [hx] using aliasAt i hi

end ClaferCompiler.Correctness.Behavioral
