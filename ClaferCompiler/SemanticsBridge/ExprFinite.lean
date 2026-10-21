module

public import ClaferCompiler.SemanticsBridge.ExprObservation

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Expr
open IR.Expr
open Clafer.Constraints

/-- Local collection finiteness, with no finite ambient-universe assumption. -/
def FiniteResult {s : Clafer.Constraints.Support} : (t : Clafer.Constraints.Ty s) →
    Option (Value Atom t) → Prop
  | .collection _, r => ∃ S, r = some S ∧ S.Finite
  | _, _ => True

theorem finite_result {s : Clafer.Constraints.Support}
    (model : IntegerBinding.{0,0} s Atom) {Γ t} (e : Clafer.Constraints.Expr s Γ t)
    (hv : ∀ x ∈ e.extents, (model.model.obj x : Set Atom).Finite)
    (hm : ∀ f ∈ e.maps, (ambientRelation (model.model.map (s.arrow f))).Finite)
    (ρ : Clafer.Constraints.Environment s Atom Γ) : FiniteResult t (e.denote model ρ) := by
  induction e with
  | this => exact ⟨_, rfl, Set.finite_singleton _⟩
  | var v => exact ⟨_, rfl, Set.finite_singleton _⟩
  | extent x => exact ⟨_, rfl, hv x (Set.mem_singleton x)⟩
  | map f => exact ⟨_, rfl, hm f (Set.mem_singleton f)⟩
  | @setOp Γ k op a b iha ihb =>
    simp only [Clafer.Constraints.Expr.extents, Clafer.Constraints.Expr.maps, Set.forall_mem_union] at hv hm
    obtain ⟨A, ha, hA⟩ := iha hv.1 hm.1 ρ
    obtain ⟨B, hb, hB⟩ := ihb hv.2 hm.2 ρ
    refine ⟨collectionOp op A B, by simp [Clafer.Constraints.Expr.denote, ha, hb, lift₂], ?_⟩
    cases op with
    | union => exact hA.union hB
    | difference => exact hA.subset Set.sdiff_subset
    | intersection => exact hA.subset Set.inter_subset_left
  | image a b iha ihb =>
    simp only [Clafer.Constraints.Expr.extents, Clafer.Constraints.Expr.maps, Set.forall_mem_union] at hv hm
    obtain ⟨A, ha, _⟩ := iha hv.1 hm.1 ρ
    obtain ⟨B, hb, hB⟩ := ihb hv.2 hm.2 ρ
    refine ⟨relationalImage A B, by simp [Clafer.Constraints.Expr.denote, ha, hb, lift₂], ?_⟩
    apply (hB.image Prod.snd).subset
    rintro y ⟨x, _, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩
  | join a b iha ihb =>
    simp only [Clafer.Constraints.Expr.extents, Clafer.Constraints.Expr.maps, Set.forall_mem_union] at hv hm
    obtain ⟨A, ha, hA⟩ := iha hv.1 hm.1 ρ
    obtain ⟨B, hb, hB⟩ := ihb hv.2 hm.2 ρ
    refine ⟨relationalJoin A B, by simp [Clafer.Constraints.Expr.denote, ha, hb, lift₂], ?_⟩
    apply ((hA.image Prod.fst).prod (hB.image Prod.snd)).subset
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact ⟨⟨(x, y), hxy, rfl⟩, ⟨(y, z), hyz, rfl⟩⟩
  | widenObjects p a ih => exact ih hv hm ρ
  | widenRelation p q a ih => exact ih hv hm ρ
  | _ => trivial

theorem observed_relation_finite (xs : List Link) : (observedRelation xs).Finite := by
  apply ((List.finite_toSet xs).image (fun l => (l.source, l.target))).subset
  rintro p ⟨l, hl, hs, ht⟩
  exact ⟨l, hl, Prod.ext hs ht⟩

/-!
[proof->req~compiler-arithmetic~1]
-/
/-- Every admitted unary/binary observation is finite, including navigation to
integers. Consequently cardinality operands and quantifier domains are finite. -/
theorem checked_collection_finite {s : Support n m} (c : Checked s Γ (.collection k))
    (h : ObservationValid s o)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s))) :
    ∃ S, denote c (extend s o h) ρ = some S ∧ S.Finite := by
  apply finite_result (extend s o h) (interpret s c.term.raw c.typed)
  · intro x hx
    have hn := checked_nonprimitive c x hx
    simp [fullExtent, hn, atomSet]
  · intro e _
    rw [extend_map]
    exact observed_relation_finite _

end ClaferCompiler.SemanticsBridge.Expr
