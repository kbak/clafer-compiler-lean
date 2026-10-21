module

public import ClaferCompiler.Correctness.ExpressionMeaning

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction Expressions

theorem dedup_singleton [BEq α] [LawfulBEq α] (xs : List α) (a : α)
    (h : ∀ x, x ∈ xs ↔ x = a) : xs.eraseDups = [a] := by
  have hm : ∀ x, x ∈ xs.eraseDups ↔ x = a := fun x => (List.mem_eraseDups).trans (h x)
  have hn := Structural.eraseDups_nodup xs
  cases he : xs.eraseDups with
  | nil => have := (hm a).mpr rfl; simp [he] at this
  | cons x rest =>
    have hx : x = a := (hm x).mp (by simp [he])
    have hr : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      have hyx := (hm y).mp (by simp [he, hy])
      simp only [he, List.nodup_cons] at hn
      exact hn.1 (hx.symm ▸ hyx ▸ hy)
    simp [hx, hr]

theorem scalar_rows_singleton {s : Support n m} {l : Layout n m} {o i f}
    (hl : LayoutRep s l o i f) (x : Fin n) (hx : s.integer[x] = true)
    {z : Int} (hz : Atom.integer z ∈ o.objects[x]) :
    (((i.values[l.scalarOwners[x]]?.getD []).filter
      (fun row => row.1 == f (.integer z))).map Prod.snd).eraseDups = [z] := by
  apply dedup_singleton
  intro value
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨row, ⟨hr, he⟩, rfl⟩
    obtain ⟨k, _, rfl⟩ := (hl.scalarRows x hx row).mp hr
    exact Atom.integer.inj (hl.injective he)
  · intro he
    subst value
    exact ⟨(f (.integer z), z), ⟨(hl.scalarRows x hx _).mpr ⟨z, hz, rfl⟩, rfl⟩, rfl⟩

theorem scalar_value_exact {s : Support n m} {l : Layout n m} {o i f}
    (hl : LayoutRep s l o i f) (x : Fin n) (hx : s.integer[x] = true)
    {z : Int} (hz : Atom.integer z ∈ o.objects[x]) {env r lo hi}
    (hr : Unary f {Atom.integer z} (r.eval i env)) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    i.scalarValue env l.scalarOwners[x] lo hi r = z := by
  unfold Instance.scalarValue
  simp only [represented_singleton hr]
  rw [scalar_rows_singleton hl x hx hz]
  simp [hlo, hhi]

theorem extract_defined_card {s : Support n m} {o : Observation n m} {b : IR.Expr.Bounds n}
    (hb : o.withinBounds s b = true) {x : Fin n} (hx : s.integer[x] = true)
    {S : Set Atom} (hs : S ⊆ atomSet o.objects[x]) :
    (integers.extract S).isSome = (decide (S.ncard = 1)) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, Option.isSome_iff_exists]
  constructor
  · rintro ⟨z, hz⟩
    rw [(integers.extract_eq_some_iff S z).mp hz]
    exact Set.ncard_singleton _
  · intro hone
    obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp hone
    have ha := (withinBounds_objects hb x).2.2 a (hs (Set.mem_singleton a))
    cases a with
    | object id => simp [hx] at ha
    | integer z => exact ⟨z, (integers.extract_eq_some_iff _ _).mpr rfl⟩

theorem agrees_integerOf {s : Support n m} {l : Layout n m} {o i f}
    {b : IR.Expr.Bounds n} (hl : LayoutRep s l o i f) (hb : o.withinBounds s b = true)
    (hw : 1 ≤ b.width ∧ b.width ≤ 16) (x : Fin n) (hx : s.integer[x] = true)
    {env} {S : Set Atom} (hs : S ⊆ atomSet o.objects[x])
    (c : Code (.collection (.objects x))) (hc : Built c)
    (ha : Agrees s f b.width i env (some S) c)
    (hfit : ResultFits b.width ((integers.extract S).map ULift.up)) :
    Agrees s f b.width i env (t := .integer) ((integers.extract S).map ULift.up)
      ⟨.conj c.defined (.conj (.mult .one c.value) (.subset c.value (.sig l.scalarOwners[x]))),
        .scalar l.scalarOwners[x] b.integers[x].lower b.integers[x].upper c.value⟩ := by
  have hr : Unary f S (c.value.eval i env) := ha.2 S rfl
  have hsub : relationSubset (c.value.eval i env) ((Rel.sig l.scalarOwners[x]).eval i env) = true :=
    (represented_subset (unary_injective hl.injective) hr (hl.scalarOwners x hx env)).mpr hs
  constructor
  · rw [Formula.eval_conj hc.1 (.conj (.mult _ _) (.subset _ _)), ha.1]
    rw [Formula.eval_conj (.mult _ _) (.subset _ _)]
    change (do let a ← some true
               let c ← (do let d ← some (decide ((c.value.eval i env).eraseDups.length = 1))
                           let e ← some (relationSubset (c.value.eval i env) ((Rel.sig l.scalarOwners[x]).eval i env))
                           pure (d && e))
               pure (a && c)) = some _
    simp only [hsub, represented_card (unary_injective hl.injective) hr,
      bind, Option.bind, pure, Pure.pure, Bool.and_true, Bool.true_and, Option.isSome_map]
    congr 1
    exact (extract_defined_card hb hx hs).symm
  · intro value hv
    cases he : integers.extract S with
    | none => simp [he] at hv
    | some z =>
      have hvz : value = ⟨z⟩ := (Option.some.inj (by simpa only [he, Option.map_some] using hv)).symm
      subst value
      have hS := (integers.extract_eq_some_iff S z).mp he
      have hz : Atom.integer z ∈ o.objects[x] := hs (hS ▸ Set.mem_singleton _)
      have hbounds := (withinBounds_objects hb x).2.2 (.integer z) hz
      change boundedInt b.width (i.scalarValue env l.scalarOwners[x]
        b.integers[x].lower b.integers[x].upper c.value) = some z
      rw [scalar_value_exact hl x hx hz (hS ▸ hr) hbounds.2.2.1 hbounds.2.2.2]
      apply source_range_target_int hw
      exact hfit ⟨z⟩ (by simp only [he, Option.map_some])

end ClaferCompiler.Correctness.ExpressionMeaning
