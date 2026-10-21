module

public import ClaferCompiler.Correctness.StructuralCardinality

public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

theorem field_functional (s : Schema) (i : Instance)
    (hw : i.wellFormed s = true) (hd : i.declarations s = true)
    (k : Nat) (f : Field) (hk : s.fields[k]? = some f)
    (hm : f.multiplicity = .one) (a : Nat) (ha : a ∈ i.signatures[f.owner]?.getD []) :
    ∃! b, [a, b] ∈ i.fields[k]?.getD [] := by
  have hf := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hd).2
    (f, k) (List.mk_mem_zipIdx_iff_getElem?.mpr hk)
  have hc := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hf).2 a ha
  have hn : ((i.fields[k]?.getD []).filter fun t => t.head? == some a).length = 1 := by
    simpa [hm, Multiplicity.holds] using hc
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hn
  have hmem : t ∈ (i.fields[k]?.getD []).filter (fun t => t.head? == some a) := by simp [ht]
  have hmem := List.mem_filter.mp hmem
  obtain ⟨x, b, rfl⟩ := field_binary s i hw k t hmem.1
  have he : x = a := by simpa using hmem.2
  subst x
  refine ⟨b, hmem.1, ?_⟩
  intro c hc
  have hc' : [a, c] ∈ (i.fields[k]?.getD []).filter (fun t => t.head? == some a) :=
    List.mem_filter.mpr ⟨hc, by simp⟩
  simpa [ht] using hc'

theorem represented_references {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : i.declarations (schema v) = true) :
    s.References (interpret v.core) := by
  intro d c hc x hx
  have hc : (v.core.get d).reference.target = some c := by simpa [interpret] using hc
  obtain ⟨b, hb, hu⟩ := field_functional (schema v) i r.wellFormed h _ _
    (dereference_direction v d c hc) rfl (r.objects x).val ((r.heads d x).mp hx)
  have hm := (field_atom_live i r.live _ _ b hb).2
  let y := r.objects.symm ⟨b, hm⟩
  have hy : (r.objects y).val = b := by simp [y]
  refine ⟨y, (r.dereference d x y).mpr ⟨by simp [hc], by simpa [hy] using hb⟩, ?_⟩
  intro z hz
  apply r.objects.injective
  apply Subtype.ext
  exact (hu _ ((r.dereference d x z).mp hz).2).trans hy.symm

theorem represented_deref_fiber {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (d c : Fin n) (hc : (v.core.get d).reference.target = some c)
    (x : U) (env : List Nat) (k : Nat) (hk : env[k]? = some (r.objects x).val) (t : Tuple) :
    t ∈ (Rel.join (.var k) (deref v.core d)).eval i env ↔
      ∃ y, s.deref d x y ∧ t = [(r.objects y).val] := by
  unfold deref
  rw [mem_join_singleton _ (.field _) i env k _ hk
    (by intro t ht; exact field_binary _ _ r.wellFormed _ t ht)]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hm := (field_atom_live i r.live _ _ b hb).2
    let y := r.objects.symm ⟨b, hm⟩
    have hy : (r.objects y).val = b := by simp [y]
    refine ⟨y, (r.dereference d x y).mpr ⟨by simp [hc], ?_⟩, by simp [hy]⟩
    simpa [hy] using hb
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(r.objects y).val, (r.dereference d x y).mp hy |>.2, rfl⟩

theorem Formula_eval_implies_true (ha : Formula.Term a) (hb : Formula.Term b)
    (w : Nat) (i : Instance) (env : List Nat)
    (h : (a.implies b).eval w i env = some true) (ht : a.eval w i env = some true) :
    b.eval w i env = some true := by
  simp only [Formula.eval, Formula.fold_implies_term ha hb] at h
  change (do let x ← a.eval w i env; let y ← b.eval w i env; pure (!x || y)) = some true at h
  simpa [ht] using h

theorem represented_keys {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) : s.Keys (interpret v.core) := by
  intro d hd p t x y hpx hxt hpy hyt
  have ty := represented_typed v s i r h.2.2.2.1
  have refs := represented_references v s i r h.2.2.2.1
  obtain ⟨hx, c, hc, hp⟩ := ty.1 d p x hpx
  have hr : ∃ target, (v.core.get d).reference = .set target := by
    cases he : (v.core.get d).reference with
    | basic => simp [interpret, reference, he, Clafer.MCS.ReferenceTo.kind] at hd
    | bag target => simp [interpret, reference, he, Clafer.MCS.ReferenceTo.kind] at hd
    | set target => exact ⟨target, rfl⟩
  obtain ⟨target, hr⟩ := hr
  have hderef : (v.core.get d).reference.target = some target := by simp [hr, IR.Structural.Reference.target]
  have hf := Module.fact_true _ _ h.2.2.2.2.2 _
    (List.mem_map.mpr ⟨_, set_key_generated v d c target hc hr, rfl⟩)
  have hu := (Formula.eval_all_true (.all _ (.all _ (.implies (.equal _ _) (.equal _ _))))
    w i [] _).mp hf [(r.objects p).val] (by simpa [head] using (r.heads c p).mp hp)
  have hv := (Formula.eval_all_true (.all _ (.implies (.equal _ _) (.equal _ _))) w i _ _).mp hu
    [(r.objects x).val] ((represented_contains_fiber v s i r d c hc p _ 0 rfl _).mpr ⟨x, hpx, rfl⟩)
  have hw := (Formula.eval_all_true (.implies (.equal _ _) (.equal _ _)) w i _ _).mp hv
    [(r.objects y).val] ((represented_contains_fiber v s i r d c hc p _ 1 rfl _).mpr ⟨y, hpy, rfl⟩)
  have heq : (Formula.equal (Rel.join (.var 1) (deref v.core d))
      (Rel.join (.var 0) (deref v.core d))).eval w i
      [(r.objects y).val, (r.objects x).val, (r.objects p).val] = some true := by
    apply (equal_eval_true _ _ _ _ _).mpr
    intro tuple
    rw [represented_deref_fiber v s i r d target hderef x _ 1 rfl,
      represented_deref_fiber v s i r d target hderef y _ 0 rfl]
    have rx := refs d target (by simpa [interpret] using hderef) x hx
    have ry := refs d target (by simpa [interpret] using hderef) y (ty.1 d p y hpy).1
    constructor
    · rintro ⟨z, hz, ht⟩
      exact ⟨t, hyt, rx.unique hz hxt ▸ ht⟩
    · rintro ⟨z, hz, ht⟩
      exact ⟨t, hxt, ry.unique hz hyt ▸ ht⟩
  have he := Formula_eval_implies_true (.equal _ _) (.equal _ _) w i _ hw heq
  have he := (equal_eval_true _ _ _ _ _).mp he [(r.objects x).val]
  have hx' : [(r.objects x).val] ∈ (Rel.var 1).eval i
      [(r.objects y).val, (r.objects x).val, (r.objects p).val] := by simp
  have he' : (r.objects x).val = (r.objects y).val := by simpa using he.mp hx'
  exact r.objects.injective (Subtype.ext he')

/-- Every independent target model of the actual generated module satisfies all
ten upstream structural clauses under its concrete representation equations. -/
theorem represented_sound {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) :
    Clafer.Semantics.StructuralSatisfies (interpret v.core) s :=
  ⟨represented_typed v s i r h.2.2.2.1, represented_rooted v s i r scopes w h,
    represented_inherits v s i r h.2.2.2.1, represented_abstracts v s i r scopes w h,
    represented_parents v s i r scopes w h, represented_references v s i r h.2.2.2.1,
    represented_keys v s i r scopes w h, represented_multiplicities v s i r scopes w h,
    represented_groups v s i r scopes w h, represented_disjoint v s i r
      ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h.1).1).1) h.2.2.2.1⟩

/-- Soundness constructs decoding, representation and source satisfaction. No
source truth, successful decoding or arbitrary preservation bridge is assumed. -/
theorem compiled_sound (v : IR.Structural.Validated n) (b : Structural.Bounds)
    (c : Compiled) (hc : compile v b = .ok c) (i : Instance)
    (h : Satisfies c.module.raw i) :
    ∃ o, decode v i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Represents v (realize o hr) i) ∧
      Clafer.Semantics.StructuralSatisfies (interpret v.core) (realize o hr) := by
  obtain ⟨o, ho, hr, ⟨r⟩⟩ := compiled_representation v b c hc i h
  obtain ⟨scopes, _, he, _, _⟩ := compile_output v b c hc
  rw [he] at h
  exact ⟨o, ho, hr, ⟨r⟩, represented_sound v _ i r scopes b.bitwidth h⟩

end ClaferCompiler.Correctness.Structural
