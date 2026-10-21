module

public import ClaferCompiler.Correctness.ExpressionMeaning

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction Expressions
open Clafer.Constraints (Value)

variable {s : Support n m} {f : Atom → Nat} {w : Nat} {i : Instance} {env : List Nat}

theorem eval_implies (ha : a.Term) (hb : b.Term) :
    (Formula.implies a b).eval w i env = (do
      let x ← a.eval w i env
      let y ← b.eval w i env
      pure (!x || y)) := by
  simp only [Formula.eval, Formula.fold_implies_term ha hb]

theorem eval_neg (ha : a.Term) :
    (Formula.neg a).eval w i env = (do pure (!(← a.eval w i env))) := by
  simp only [Formula.eval, Formula.fold_neg_term ha]

theorem equal_value (t : Ty n) {a b : Value Atom (type s t)} {ca cb : ValueCode t}
    (hca : ValueBuilt t ca) (hcb : ValueBuilt t cb) (hf : Function.Injective f)
    (ha : ValueAgrees s f w i env t a ca) (hb : ValueAgrees s f w i env t b cb) :
    (equalCode t ca cb).eval w i env = some (propBool (a = b)) := by
  classical
  cases t with
  | boolean =>
    change ca.eval w i env = some (propBool a.down) at ha
    change cb.eval w i env = some (propBool b.down) at hb
    rw [equalCode, Formula.eval_conj (.implies hca hcb) (.implies hcb hca),
      eval_implies hca hcb, eval_implies hcb hca, ha, hb]
    simp only [bind, Option.bind, pure, Pure.pure]
    congr 1
    apply Bool.eq_iff_iff.mpr
    cases a with | up p => cases b with | up q =>
      by_cases hp : p <;> by_cases hq : q <;> simp [propBool, hp, hq]
  | integer =>
    cases a with | up a => cases b with | up b =>
      change ca.eval w i env = some a at ha
      change cb.eval w i env = some b at hb
      change (do let x ← ca.eval w i env
                 let y ← cb.eval w i env
                 pure (Comparison.eq.holds x y)) = _
      rw [ha, hb]
      change some (a == b) = some (propBool ((⟨a⟩ : ULift Int) = ⟨b⟩))
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, propBool_true, ULift.up.injEq]
  | collection k =>
    change some (relationSubset (ca.eval i env) (cb.eval i env) &&
      relationSubset (cb.eval i env) (ca.eval i env)) = _
    congr 1
    exact Bool.eq_iff_iff.mpr ((represented_equal (tuple_injective s k hf) ha hb).trans
      (propBool_true _).symm)

theorem agrees_and {a b : Option (ULift Prop)} {ca cb : Code (.boolean : Ty n)}
    (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb) (hca : Built ca) (hcb : Built cb) :
    Agrees s f w i env (t := .boolean) (Clafer.Constraints.lift₂ (fun p q => ⟨p.down ∧ q.down⟩) a b)
      ⟨.conj ca.defined cb.defined, .conj ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y _ _ hx hy
  change ca.value.eval w i env = some (propBool x.down) at hx
  change cb.value.eval w i env = some (propBool y.down) at hy
  change (ca.value.conj cb.value).eval w i env = _
  rw [Formula.eval_conj hca.2 hcb.2, hx, hy]
  simp only [bind, Option.bind, pure, Pure.pure, propBool_and]

theorem agrees_not {a : Option (ULift Prop)} {ca : Code (.boolean : Ty n)}
    (ha : Agrees s f w i env a ca) (hca : Built ca) :
    Agrees s f w i env (t := .boolean) (a.map (fun p => ⟨¬ p.down⟩)) ⟨ca.defined, .neg ca.value⟩ := by
  refine ⟨by simpa only [Option.isSome_map] using ha.1, ?_⟩
  intro p hp
  cases a with
  | none => cases hp
  | some q =>
    have he : (⟨¬ q.down⟩ : ULift Prop) = p := Option.some.inj hp
    subst p
    have hq := ha.2 q rfl
    change ca.value.eval w i env = some (propBool q.down) at hq
    change ca.value.neg.eval w i env = _
    rw [eval_neg hca.2, hq]
    simp [propBool]

theorem agrees_equal {t : Ty n} {a b : Option (Value Atom (type s t))} {ca cb : Code t}
    (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb) (hca : Built ca) (hcb : Built cb)
    (hf : Function.Injective f) :
    Agrees s f w i env (t := .boolean) (Clafer.Constraints.lift₂ (fun p q => ⟨p = q⟩) a b)
      ⟨.conj ca.defined cb.defined, equalCode t ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y _ _ hx hy
  exact equal_value t hca.2 hcb.2 hf hx hy

theorem agrees_less {a b : Option (ULift Int)} {ca cb : Code (.integer : Ty n)}
    (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb) (hca : Built ca) (hcb : Built cb) :
    Agrees s f w i env (t := .boolean) (Clafer.Constraints.lift₂ (fun p q => ⟨p.down < q.down⟩) a b)
      ⟨.conj ca.defined cb.defined, .compare .lt ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y _ _ hx hy
  change ca.value.eval w i env = some x.down at hx
  change cb.value.eval w i env = some y.down at hy
  change (do let a ← ca.value.eval w i env
             let b ← cb.value.eval w i env
             pure (Comparison.lt.holds a b)) = _
  rw [hx, hy]
  simp [Comparison.holds, propBool]

theorem agrees_arithmetic (op : Arithmetic) {a b : Option (ULift Int)}
    {ca cb : Code (.integer : Ty n)} (ha : Agrees s f w i env a ca)
    (hb : Agrees s f w i env b cb) (hca : Built ca) (hcb : Built cb)
    (hw : 1 ≤ w ∧ w ≤ 16)
    (hfit : ResultFits w (Clafer.Constraints.lift₂
      (fun p q => ⟨match op with | .add => p.down + q.down | .subtract => p.down - q.down⟩) a b)) :
    Agrees s f w i env (t := .integer) (Clafer.Constraints.lift₂
      (fun p q => ⟨match op with | .add => p.down + q.down | .subtract => p.down - q.down⟩) a b)
      ⟨.conj ca.defined cb.defined, match op with
        | .add => .add ca.value cb.value | .subtract => .subtract ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y hx hy hxa hyb
  have hfits := hfit ⟨match op with | .add => x.down + y.down | .subtract => x.down - y.down⟩
    (by cases op <;> simp only [Clafer.Constraints.lift₂, hx, hy, Option.bind_some, Option.map_some])
  change ca.value.eval w i env = some x.down at hxa
  change cb.value.eval w i env = some y.down at hyb
  cases op with
  | add =>
    change (ca.value.add cb.value).eval w i env = _
    rw [Integer.eval_add hca.2 hcb.2, hxa, hyb]
    exact source_range_target_int hw hfits
  | subtract =>
    change (ca.value.subtract cb.value).eval w i env = _
    rw [Integer.eval_subtract hca.2 hcb.2, hxa, hyb]
    exact source_range_target_int hw hfits

theorem agrees_setOp (op : SetOp) (k : Collection n)
    {a b : Option (Value Atom (type s (.collection k)))} {ca cb : Code (.collection k)}
    (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb)
    (hca : Built ca) (hcb : Built cb) (hf : Function.Injective f) :
    Agrees s f w i env (t := .collection k)
      (Clafer.Constraints.lift₂ (Clafer.Constraints.collectionOp (setOp op)) a b)
      ⟨.conj ca.defined cb.defined, match op with
        | .union => .union ca.value cb.value | .difference => .diff ca.value cb.value
        | .intersection => .inter ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y _ _ hx hy
  cases op with
  | union => exact represents_union hca.2 hcb.2 hx hy
  | difference => exact represents_diff (tuple_injective s k hf) hca.2 hcb.2 hx hy
  | intersection => exact represents_inter (tuple_injective s k hf) hca.2 hcb.2 hx hy

theorem agrees_subset (k : Collection n)
    {a b : Option (Value Atom (type s (.collection k)))} {ca cb : Code (.collection k)}
    (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb)
    (hca : Built ca) (hcb : Built cb) (hf : Function.Injective f) :
    Agrees s f w i env (t := .boolean)
      (Clafer.Constraints.lift₂ (fun p q => ⟨p ⊆ q⟩) a b)
      ⟨.conj ca.defined cb.defined, .subset ca.value cb.value⟩ := by
  apply agrees_binary ha hb hca.1 hcb.1
  intro x y _ _ hx hy
  change some (relationSubset (ca.value.eval i env) (cb.value.eval i env)) = _
  congr 1
  exact Bool.eq_iff_iff.mpr ((represented_subset (tuple_injective s k hf) hx hy).trans
    (propBool_true _).symm)

theorem agrees_cardinality (k : Collection n) {S : Value Atom (type s (.collection k))}
    {ca : Code (.collection k)} (ha : Agrees s f w i env (some S) ca)
    (hf : Function.Injective f) (hfin : S.Finite) (hw : 1 ≤ w ∧ w ≤ 16)
    (hfit : ResultFits w (Clafer.Constraints.finiteCard S)) :
    Agrees s f w i env (t := .integer) (Clafer.Constraints.finiteCard S)
      ⟨ca.defined, .count ca.value⟩ := by
  rw [Clafer.Constraints.finiteCard_finite S hfin]
  refine ⟨ha.1, ?_⟩
  intro z hz
  cases Option.some.inj hz
  change boundedInt w (Int.ofNat (ca.value.eval i env).eraseDups.length) = some _
  rw [represented_card (tuple_injective s k hf) (ha.2 S rfl)]
  exact source_range_target_int hw (hfit _ (Clafer.Constraints.finiteCard_finite S hfin))

end ClaferCompiler.Correctness.ExpressionMeaning
