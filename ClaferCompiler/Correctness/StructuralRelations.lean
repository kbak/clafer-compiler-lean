module

public import ClaferCompiler.Correctness.StructuralSatisfaction

public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

theorem eraseDups_nodup [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp, eraseDups_nodup (xs.filter fun b => !b == x)⟩
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun b => !b == x) xs
  simp only [List.length_cons]
  omega

theorem eraseDups_card (xs : Relation) : xs.eraseDups.length = xs.toFinset.card := by
  have he : xs.eraseDups.toFinset = xs.toFinset := by ext; simp
  rw [← List.toFinset_card_of_nodup (eraseDups_nodup xs), he]

/-- Count source objects through a concrete injective atom map. The hypothesis
is an exact tuple equation, independent of any constraint truth. -/
theorem unary_card {U : Type} [Fintype U] (P : U → Prop) [DecidablePred P]
    (f : U → Nat) (hf : Function.Injective f) (xs : Relation)
    (hm : ∀ t, t ∈ xs ↔ ∃ x, P x ∧ t = [f x]) :
    xs.eraseDups.length = Fintype.card {x // P x} := by
  classical
  let emb : U ↪ Tuple := ⟨fun x => [f x], by intro x y h; exact hf (by simpa using h)⟩
  have he : xs.toFinset = (Finset.univ.filter P).map emb := by
    ext t
    simp only [List.mem_toFinset, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change t ∈ xs ↔ ∃ x, P x ∧ [f x] = t
    simpa only [eq_comm] using hm t
  rw [eraseDups_card, he, Finset.card_map, Fintype.card_subtype]

theorem unary_one {U : Type} [Fintype U] (P : U → Prop) [DecidablePred P]
    (f : U → Nat) (hf : Function.Injective f) (xs : Relation)
    (hm : ∀ t, t ∈ xs ↔ ∃ x, P x ∧ t = [f x]) :
    xs.eraseDups.length = 1 ↔ ∃! x, P x := by
  classical
  rw [unary_card P f hf xs hm, Fintype.card_subtype,
    Finset.card_eq_one_iff_existsUnique]
  simp

theorem field_binary (s : Schema) (i : Instance) (h : i.wellFormed s = true)
    (k : Nat) (t : Tuple) (ht : t ∈ i.fields[k]?.getD []) : ∃ a b, t = [a, b] := by
  cases hk : i.fields[k]? with
  | none => simp [hk] at ht
  | some ts =>
    have hw := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 ts
      (List.mem_of_getElem? hk)
    have hl := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 t (by simpa [hk] using ht)
    have hl : t.length = 2 := beq_iff_eq.mp hl
    cases t with
    | nil => simp at hl
    | cons a t => cases t with
      | nil => simp at hl
      | cons b t =>
        have he : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        exact ⟨a, b, by simp [he]⟩

theorem mem_join_singleton (r : Rel) (hr : r.Term) (i : Instance) (env : List Nat)
    (k a : Nat) (ha : env[k]? = some a)
    (hb : ∀ t ∈ r.eval i env, ∃ x y, t = [x, y]) (t : Tuple) :
    t ∈ (Rel.join (.var k) r).eval i env ↔ ∃ b, [a, b] ∈ r.eval i env ∧ t = [b] := by
  rw [Rel.eval_join (.var _) hr]
  simp only [Rel.eval_var, ha, Option.toList_some, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_eraseDups,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, he⟩, ht⟩
    obtain ⟨x, y, rfl⟩ := hb q hq
    have hx : a = x := by simpa using he
    subst x
    exact ⟨y, hq, by simpa using ht.symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨[a, b], ⟨hb, by simp⟩, by simp⟩

theorem field_atom_live (i : Instance) (hl : Live i) (k a b : Nat)
    (ht : [a, b] ∈ i.fields[k]?.getD []) :
    a ∈ i.signatures[0]?.getD [] ∧ b ∈ i.signatures[0]?.getD [] := by
  cases hk : i.fields[k]? with
  | none => simp [hk] at ht
  | some ts =>
    have ht' : [a, b] ∈ ts := by simpa [hk] using ht
    exact ⟨hl.2 ts (List.mem_of_getElem? hk) [a, b] ht' a (by simp),
      hl.2 ts (List.mem_of_getElem? hk) [a, b] ht' b (by simp)⟩

theorem represented_contains_fiber {U : Type} (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (d c : Fin n) (hp : (v.core.get d).parent = some c)
    (p : U) (env : List Nat) (k : Nat) (hk : env[k]? = some (r.objects p).val) (t : Tuple) :
    t ∈ (Rel.join (.var k) (contains v.core d)).eval i env ↔
      ∃ x, s.contains d p x ∧ t = [(r.objects x).val] := by
  unfold contains
  rw [mem_join_singleton _ (.field _) i env k _ hk
    (by intro t ht; exact field_binary _ _ r.wellFormed _ t ht)]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hm := (field_atom_live i r.live _ _ b hb).2
    let x := r.objects.symm ⟨b, hm⟩
    have hx : (r.objects x).val = b := by simp [x]
    refine ⟨x, (r.containment d p x).mpr ⟨by simp [hp], ?_⟩, by simp [hx]⟩
    simpa [hx] using hb
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(r.objects x).val, (r.containment d p x).mp hx |>.2, rfl⟩

theorem represented_parent_fiber {U : Type} (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (d c : Fin n) (hp : (v.core.get d).parent = some c)
    (x : U) (t : Tuple) :
    t ∈ (Rel.join (.var 0) (Rel.transpose (contains v.core d))).eval i [(r.objects x).val] ↔
      ∃ p, s.contains d p x ∧ t = [(r.objects p).val] := by
  have hb : ∀ t ∈ (Rel.transpose (contains v.core d)).eval i [(r.objects x).val],
      ∃ a b, t = [a, b] := by
    intro t ht
    rw [Rel.eval_transpose (show (contains v.core d).Term from .field _)] at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp ht)
    obtain ⟨a, b, rfl⟩ := field_binary _ _ r.wellFormed _ q hq
    exact ⟨b, a, rfl⟩
  rw [mem_join_singleton _ (Rel.Term.transpose (show (contains v.core d).Term from .field _))
    i _ 0 _ rfl hb]
  have ht (b : Nat) :
      [(r.objects x).val, b] ∈ (Rel.transpose (contains v.core d)).eval i [(r.objects x).val] ↔
        [b, (r.objects x).val] ∈ i.fields[fieldId v.core d .containment]?.getD [] := by
    rw [Rel.eval_transpose (show (contains v.core d).Term from .field _)]
    simp only [List.mem_eraseDups, List.mem_map]
    constructor
    · rintro ⟨q, hq, he⟩
      have he := congrArg List.reverse he
      have he' : q = [b, (r.objects x).val] := by simpa using he
      simpa only [he', contains, Rel.eval_field] using hq
    · intro h; exact ⟨[b, (r.objects x).val], h, rfl⟩
  simp_rw [ht]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hm := (field_atom_live i r.live _ b _ hb).1
    let p := r.objects.symm ⟨b, hm⟩
    have hh : (r.objects p).val = b := by simp [p]
    refine ⟨p, (r.containment d p x).mpr ⟨by simp [hp], ?_⟩, by simp [hh]⟩
    simpa [hh] using hb
  · rintro ⟨p, h, rfl⟩
    exact ⟨(r.objects p).val, (r.containment d p x).mp h |>.2, rfl⟩

end ClaferCompiler.Correctness.Structural
