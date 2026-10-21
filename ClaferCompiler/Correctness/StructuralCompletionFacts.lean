module

public import ClaferCompiler.Correctness.StructuralReferences

@[expose] public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

theorem represented_head_membership {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (d : Fin n) (env : List Nat) (t : Tuple) :
    t ∈ (head v d).eval i env ↔ ∃ x, x ∈ s.head d ∧ t = [(r.objects x).val] := by
  simp only [head, Rel.eval_sig, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hm : a ∈ i.signatures[0]?.getD [] := by
      cases hk : i.signatures[signatureId v d]? with
      | none => simp [hk] at ha
      | some xs => exact r.live.1 xs (List.mem_of_getElem? hk) a (by simpa [hk] using ha)
    let x := r.objects.symm ⟨a, hm⟩
    have hx : (r.objects x).val = a := by simp [x]
    exact ⟨x, (r.heads d x).mpr (by simpa [hx] using ha), by simp [hx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (r.heads d x).mp hx, rfl⟩

theorem all_represented_iff {U : Type} (P : U → Prop) (f : U → Nat) (domain : Rel)
    (body : Formula) (hb : body.Term) (w : Nat) (i : Instance) (env : List Nat)
    (hm : ∀ t, t ∈ domain.eval i env ↔ ∃ x, P x ∧ t = [f x]) :
    (Formula.all domain body).eval w i env = some true ↔
      ∀ x, P x → body.eval w i (f x :: env) = some true := by
  rw [Formula.eval_all_true hb]
  constructor
  · intro h x hx
    exact h [f x] ((hm _).mpr ⟨x, hx, rfl⟩)
  · intro h t ht
    obtain ⟨x, hx, rfl⟩ := (hm t).mp ht
    exact h x hx

/-- Bounds on the actual finite source fibers, separate from source truth and
from target truth. Empty quantifier domains impose no dynamic observations. -/
def SourceCountFits {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (w : Nat) : Prop := by
  classical
  exact (∀ d c, (v.core.get d).parent = some c → ∀ p ∈ s.head c,
    IntervalFits w (v.core.get d).localBounds (Fintype.card {x // s.contains d p x})) ∧
    (∀ d, (v.core.get d).isAbstract = false → ∀ p ∈ s.head d,
    IntervalFits w (v.core.get d).groupBounds (Fintype.card {x // s.Child (interpret v.core) d p x}))

theorem source_ownership {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.Parents (interpret v.core))
    (d c : Fin n) (hc : (v.core.get d).parent = some c) (w : Nat) :
    (ownership v d).eval w i [] = some true := by
  classical
  apply (all_represented_iff _ _ _ _ (.mult _ _) w i []
    (represented_head_membership v s i r d [])).mpr
  intro x hx
  change some (((Rel.join (.var 0) (.transpose (contains v.core d))).eval i
    [(r.objects x).val]).eraseDups.length == 1) = some true
  apply congrArg some
  apply beq_iff_eq.mpr
  exact (unary_one (fun p => s.contains d p x) (fun p => (r.objects p).val)
    (Subtype.val_injective.comp r.objects.injective) _
    (represented_parent_fiber v s i r d c hc x)).mpr (h d c hc x hx)

theorem source_local_bounds {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.Multiplicities (interpret v.core))
    (w : Nat) (fits : SourceCountFits v s w)
    (d c : Fin n) (hc : (v.core.get d).parent = some c) :
    (Formula.all (head v c) (interval (v.core.get d).localBounds
      (Rel.join (.var 0) (contains v.core d)))).eval w i [] = some true := by
  classical
  apply (all_represented_iff _ _ _ _ (interval_term _ _) w i []
    (represented_head_membership v s i r c [])).mpr
  intro p hp
  apply (interval_eval_iff _ _ _ _ _).mpr
  rw [unary_card (fun x => s.contains d p x) (fun x => (r.objects x).val)
    (Subtype.val_injective.comp r.objects.injective) _
    (represented_contains_fiber v s i r d c hc p _ 0 rfl)]
  exact ⟨fits.1 d c hc p hp, (DPGraph.Predicates.inRange_card _ _).mp (h d c hc p hp)⟩

theorem source_group_bounds {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.Groups (interpret v.core))
    (w : Nat) (fits : SourceCountFits v s w) (d : Fin n)
    (hd : (v.core.get d).isAbstract = false) :
    (Formula.all (head v d) (interval (v.core.get d).groupBounds
      (childHeads v.core d))).eval w i [] = some true := by
  classical
  apply (all_represented_iff _ _ _ _ (interval_term _ _) w i []
    (represented_head_membership v s i r d [])).mpr
  intro p hp
  apply (interval_eval_iff _ _ _ _ _).mpr
  rw [unary_card (s.Child (interpret v.core) d p) (fun x => (r.objects x).val)
    (Subtype.val_injective.comp r.objects.injective) _ (represented_children v s i r d p)]
  exact ⟨fits.2 d hd p hp, (DPGraph.Predicates.inRange_card _ _).mp (h d hd p hp)⟩

theorem source_abstract_cover {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (hi : s.Inherits (interpret v.core))
    (ha : s.Abstracts (interpret v.core)) (w : Nat) (d : Fin n)
    (hd : (v.core.get d).isAbstract = true) :
    (Formula.equal (head v d) (union ((subtypes v.core d).map (head v)))).eval w i [] = some true := by
  apply (equal_eval_true _ _ _ _ _).mpr
  intro t
  rw [represented_head_membership v s i r d [], mem_union_eval _ (by
    intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    exact .sig _)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hcx⟩ := (ha d hd).1 x hx
    exact ⟨head v c, List.mem_map.mpr ⟨c, (subtype_inventory _ _ _).mpr hc, rfl⟩,
      (represented_head_membership v s i r c [] _).mpr ⟨x, hcx, rfl⟩⟩
  · rintro ⟨q, hq, ht⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    obtain ⟨x, hx, ht⟩ := (represented_head_membership v s i r c [] t).mp ht
    exact ⟨x, hi c d ((subtype_inventory _ _ _).mp hc) x hx, ht⟩

theorem source_object_cover {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : s.Rooted (interpret v.core)) (w : Nat) :
    (Formula.equal (.sig 0) (union ((List.finRange n).map (head v)))).eval w i [] = some true := by
  apply (equal_eval_true _ _ _ _ _).mpr
  intro t
  rw [mem_union_eval _ (by
    intro q hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    exact .sig _)]
  constructor
  · intro ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    let x := r.objects.symm ⟨a, ha⟩
    have hx : (r.objects x).val = a := by simp [x]
    obtain ⟨d, hd⟩ : ∃ d, x ∈ s.head d := by
      rcases h.2.2 x with he | ⟨d, _, hd⟩
      · exact ⟨v.core.root, h.1 x |>.mpr he⟩
      · exact ⟨d, hd⟩
    exact ⟨head v d, List.mem_map.mpr ⟨d, List.mem_finRange d, rfl⟩,
      (represented_head_membership v s i r d [] _).mpr ⟨x, hd, by simp [hx]⟩⟩
  · rintro ⟨q, hq, ht⟩
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨x, _, rfl⟩ := (represented_head_membership v s i r d [] _).mp ht
    exact List.mem_map.mpr ⟨_, (r.objects x).property, rfl⟩

theorem equal_implies_true (a b c d : Rel) (w : Nat) (i : Instance) (env : List Nat) :
    ((Formula.equal a b).implies (.equal c d)).eval w i env = some true ↔
      ((Formula.equal a b).eval w i env = some true →
        (Formula.equal c d).eval w i env = some true) := by
  simp only [Formula.eval, Formula.fold_implies_term (.equal _ _) (.equal _ _)]
  dsimp only [Formula.equal, Formula.fold, List.foldl_cons, List.foldl_nil, FormulaAlgebra.step]
  change some (!(relationSubset (a.eval i env) (b.eval i env) &&
    relationSubset (b.eval i env) (a.eval i env)) ||
    (relationSubset (c.eval i env) (d.eval i env) && relationSubset (d.eval i env) (c.eval i env))) = some true ↔ _
  generalize (relationSubset (a.eval i env) (b.eval i env) &&
    relationSubset (b.eval i env) (a.eval i env)) = p
  generalize (relationSubset (c.eval i env) (d.eval i env) &&
    relationSubset (d.eval i env) (c.eval i env)) = q
  cases p <;> cases q <;> decide

theorem source_set_key {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s)
    (d p t : Fin n) (hp : (v.core.get d).parent = some p)
    (ht : (v.core.get d).reference = .set t) (w : Nat) :
    (setKey v d p).eval w i [] = some true := by
  have hderef : (v.core.get d).reference.target = some t := by simp [ht, IR.Structural.Reference.target]
  apply (all_represented_iff _ _ _ _ (.all _ (.all _ (.implies (.equal _ _) (.equal _ _))))
    w i [] (represented_head_membership v s i r p [])).mpr
  intro owner _
  apply (all_represented_iff _ _ _ _ (.all _ (.implies (.equal _ _) (.equal _ _)))
    w i _ (represented_contains_fiber v s i r d p hp owner _ 0 rfl)).mpr
  intro x hx
  apply (all_represented_iff _ _ _ _ (.implies (.equal _ _) (.equal _ _))
    w i _ (represented_contains_fiber v s i r d p hp owner _ 1 rfl)).mpr
  intro y hy
  apply (equal_implies_true _ _ _ _ _ _ _).mpr
  intro he
  obtain ⟨z, hz, _⟩ := h.2.2.2.2.2.1 d t (by simpa [interpret] using hderef)
    x (h.1.1 d owner x hx).1
  have he := (equal_eval_true _ _ _ _ _).mp he [(r.objects z).val]
  have hz' := he.mp ((represented_deref_fiber v s i r d t hderef x _ 1 rfl _).mpr ⟨z, hz, rfl⟩)
  obtain ⟨z', hz', he'⟩ := (represented_deref_fiber v s i r d t hderef y _ 0 rfl _).mp hz'
  have he' : z = z' := r.objects.injective (Subtype.ext (by simpa using he'))
  have hxy := h.2.2.2.2.2.2.1 d (by simp [interpret, reference, ht, Clafer.MCS.ReferenceTo.kind])
    owner z x y hx hz hy (he' ▸ hz')
  subst y
  apply (equal_eval_true _ _ _ _ _).mpr
  simp

theorem source_facts {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s)
    (w : Nat) (fits : SourceCountFits v s w) :
    ∀ f ∈ facts v, f.2.eval w i [] = some true := by
  have decls : ∀ d f, f ∈ declarationFacts v d → f.2.eval w i [] = some true := by
    intro d f hf
    unfold declarationFacts at hf
    rw [List.mem_append] at hf
    rcases hf with hf | hf
    · cases ha : (v.core.get d).isAbstract <;> simp only [ha, Bool.false_eq_true,
        ↓reduceIte, List.mem_singleton] at hf
      · subst f
        exact source_group_bounds v s i r h.2.2.2.2.2.2.2.2.1 w fits d ha
      · subst f
        exact source_abstract_cover v s i r h.2.2.1 h.2.2.2.1 w d ha
    · cases hp : (v.core.get d).parent with
      | none => simp [hp] at hf
      | some p =>
        simp only [hp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with (rfl | rfl) | hf
        · exact source_ownership v s i r h.2.2.2.2.1 d p hp w
        · exact source_local_bounds v s i r h.2.2.2.2.2.2.2.1 w fits d p hp
        · cases ht : (v.core.get d).reference <;> simp only [ht, List.not_mem_nil,
            List.mem_singleton] at hf
          subst f
          exact source_set_key v s i r h d p _ hp ht w
  intro f hf
  simp only [facts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hf
  rcases hf with (rfl | rfl) | ⟨d, _, hd⟩
  · change some (((i.signatures[signatureId v v.core.root]?.getD []).map
      fun x => [x]).eraseDups.length == 1) = some true
    simp [r.root, List.eraseDups_cons]
  · exact source_object_cover v s i r h.2.1 w
  · exact decls d f hd

theorem source_module_eval {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s)
    (scopes : List Scope) (w : Nat) (fits : SourceCountFits v s w) :
    (target v scopes w).eval i = some true := by
  have hf := (mapM_all_true ((facts v).map Prod.snd) (fun f => f.eval w i [])).mpr (by
    intro f hf
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    exact source_facts v s i r h w fits q hq)
  change (do let fs ← ((facts v).map Prod.snd).mapM (fun f => f.eval w i [])
             let body ← some true
             pure (fs.all id && body == true)) = some true
  simpa using hf

end ClaferCompiler.Correctness.Structural
