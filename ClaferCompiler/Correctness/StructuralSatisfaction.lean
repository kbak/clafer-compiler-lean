module

public import ClaferCompiler.Correctness.StructuralHierarchy

public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural
open SemanticsBridge.Structural

theorem field_typed (s : Schema) (i : Instance)
    (h : i.declarations s = true) (k : Nat) (f : Field)
    (hk : s.fields[k]? = some f) (a b : Nat)
    (ht : [a, b] ∈ i.fields[k]?.getD []) :
    a ∈ i.signatures[f.owner]?.getD [] ∧ b ∈ i.signatures[f.target]?.getD [] := by
  have hf := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2
    (f, k) (List.mk_mem_zipIdx_iff_getElem?.mpr hk)
  have ht := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hf).1 [a, b] ht
  simpa only [Bool.and_eq_true, List.contains_iff_mem] using ht

/-- Typed endpoints follow from target field declarations and concrete tuple
equations, without a source well-typedness premise. -/
theorem represented_typed {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : i.declarations (schema v) = true) :
    s.Typed (interpret v.core) := by
  constructor
  · intro d p x hx
    obtain ⟨hp, ht⟩ := (r.containment d p x).mp hx
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hp
    have hs := field_typed (schema v) i h _ _ (containment_direction v d c hc) _ _ ht
    exact ⟨(r.heads d x).mpr hs.2, c, hc, (r.heads c p).mpr hs.1⟩
  · intro d x t hx
    obtain ⟨hp, ht⟩ := (r.dereference d x t).mp hx
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hp
    have hs := field_typed (schema v) i h _ _ (dereference_direction v d c hc) _ _ ht
    refine ⟨(r.heads d x).mpr hs.1, c, ?_, (r.heads c t).mpr hs.2⟩
    simpa [interpret] using hc

theorem represented_inherits {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : i.declarations (schema v) = true) :
    s.Inherits (interpret v.core) := by
  intro d c hc x hx
  apply (r.heads c x).mpr
  exact declaration_included (schema v) i h _ _ _ (schema_signature v d)
    (by simpa [interpret] using congrArg (fun q => some (q.map (signatureId v) |>.getD 0)) hc)
    _ ((r.heads d x).mp hx)

theorem union_term (rs : List Rel) (h : ∀ r ∈ rs, r.Term) : (union rs).Term := by
  unfold union
  have go : ∀ (xs : List Rel) (a : Rel), a.Term → (∀ r ∈ xs, r.Term) →
      (xs.foldl Rel.union a).Term := by
    intro xs
    induction xs with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hx
      exact ih _ (.union ha (hx x (by simp))) (fun r hr => hx r (by simp [hr]))
  exact go rs _ (.empty _) h

theorem mem_union_eval (rs : List Rel) (h : ∀ r ∈ rs, r.Term)
    (i : Instance) (env : List Nat) (t : Tuple) :
    t ∈ (union rs).eval i env ↔ ∃ r ∈ rs, t ∈ r.eval i env := by
  have go : ∀ (xs : List Rel) (a : Rel), a.Term → (∀ r ∈ xs, r.Term) →
      (t ∈ (xs.foldl Rel.union a).eval i env ↔
        t ∈ a.eval i env ∨ ∃ r ∈ xs, t ∈ r.eval i env) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro a ha hx
      rw [List.foldl_cons, ih _ (.union ha (hx x (by simp)))
        (fun r hr => hx r (by simp [hr])), Rel.eval_union ha (hx x (by simp))]
      simp only [List.mem_eraseDups, List.mem_append, List.mem_cons]
      aesop
  simpa [union] using go rs (.empty .unary) (.empty _) h

theorem equal_eval_true (a b : Rel) (w : Nat) (i : Instance) (env : List Nat) :
    (Formula.equal a b).eval w i env = some true ↔
      ∀ t, t ∈ a.eval i env ↔ t ∈ b.eval i env := by
  change some (relationSubset _ _ && relationSubset _ _) = some true ↔ _
  simp only [Option.some.injEq, Bool.and_eq_true, relationSubset, List.all_eq_true,
    List.contains_iff_mem]
  aesop

/-- Explicit generated abstract coverage includes the empty-family case, which
Alloy's bare abstract-leaf declaration alone does not enforce. -/
theorem represented_abstract_cover {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) (d : Fin n)
    (ha : (v.core.get d).isAbstract = true) :
    ∀ x ∈ s.head d, ∃ c, (v.core.get c).super = some d ∧ x ∈ s.head c := by
  intro x hx
  have hf := Module.fact_true _ _ h.2.2.2.2.2 _
    (List.mem_map.mpr ⟨_, abstract_cover_generated v d ha, rfl⟩)
  have he := (equal_eval_true _ _ _ _ _).mp hf [(r.objects x).val]
  have hm : [(r.objects x).val] ∈ (head v d).eval i [] := by
    simpa [head] using (r.heads d x).mp hx
  have hu := (mem_union_eval _ (by
    intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    exact .sig _) i [] _).mp (he.mp hm)
  obtain ⟨q, hq, hxq⟩ := hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
  exact ⟨c, (subtype_inventory v.core d c).mp hc,
    (r.heads c x).mpr (by simpa [head] using hxq)⟩

theorem ancestor_root_iff (v : IR.Structural.Validated n) (d : Fin n) :
    (interpret v.core).Ancestor d v.core.root ↔ d = v.core.root := by
  constructor
  · intro h
    rcases h.cases_tail with he | ⟨e, _, he⟩
    · exact he.symm
    · have ha := (v.supportChecked.2.2.1 e v.core.root he).1
      have hr := v.coreChecked.2.2.1.2.2.2
      simp [hr] at ha
  · rintro rfl; exact .refl

theorem root_ancestor_iff (v : IR.Structural.Validated n) (d : Fin n) :
    (interpret v.core).Ancestor v.core.root d ↔ d = v.core.root := by
  constructor
  · intro h
    rcases h.cases_head with he | ⟨e, he, _⟩
    · exact he.symm
    · have hr := v.coreChecked.2.2.1.2.2.1
      change (v.core.get v.core.root).super = some e at he
      simp [hr] at he
  · rintro rfl; exact .refl

theorem represented_rooted {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) : s.Rooted (interpret v.core) := by
  have disj := represented_disjoint v s i r
    ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h.1).1).1) h.2.2.2.1
  have root : ∀ x, x ∈ s.head v.core.root ↔ x = s.root := by
    intro x
    rw [r.heads v.core.root x, r.root]
    change (r.objects x).val ∈ [(r.objects s.root).val] ↔ x = s.root
    rw [List.mem_singleton]
    exact ⟨fun he => r.objects.injective (Subtype.ext he), fun he => he ▸ rfl⟩
  refine ⟨root, ?_, ?_⟩
  · intro d hd hx
    rcases disj d v.core.root s.root hx ((root s.root).mpr rfl) with ha | ha
    · exact hd ((ancestor_root_iff v d).mp ha)
    · exact hd ((root_ancestor_iff v d).mp ha)
  · intro x
    have hf := Module.fact_true _ _ h.2.2.2.2.2 _
      (List.mem_map.mpr ⟨_, object_cover_generated v, rfl⟩)
    have hx : [(r.objects x).val] ∈ (Rel.sig 0).eval i [] := by
      simpa using (r.objects x).property
    have hu := ((equal_eval_true _ _ _ _ _).mp hf _).mp hx
    obtain ⟨q, hq, hqx⟩ := (mem_union_eval _ (by
      intro q hq
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
      exact .sig _) i [] _).mp hu
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    have hd : x ∈ s.head d := (r.heads d x).mpr (by simpa [head] using hqx)
    by_cases he : d = v.core.root
    · exact Or.inl ((root x).mp (he ▸ hd))
    · exact Or.inr ⟨d, he, hd⟩

theorem represented_abstracts {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (scopes : List Scope) (w : Nat)
    (h : Satisfies (target v scopes w) i) : s.Abstracts (interpret v.core) := by
  intro d hd
  refine ⟨represented_abstract_cover v s i r scopes w h d hd, ?_⟩
  intro c e hc he hne x hx
  apply hne
  apply signatureId_injective v
  exact declaration_siblings (schema v) i h.2.2.2.1 _ _ _ _
    (schema_signature v c) (schema_signature v e)
    (by change (v.core.get c).super = some d at hc
        change (v.core.get e).super = some d at he
        simp [hc, he])
    _ ((r.heads c x).mp hx.1) ((r.heads e x).mp hx.2)

end ClaferCompiler.Correctness.Structural
