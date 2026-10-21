module

public import ClaferCompiler.Correctness.ExpressionOperators
public import ClaferCompiler.Correctness.ExpressionScalars
public import ClaferCompiler.Correctness.ExpressionQuantifiers

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction Expressions

private theorem collection_numbers_fit {s : Support n m} {Γ k w}
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (e : Clafer.Constraints.Expr (support s) Γ (.collection k)) (ρ) :
    AllNumbersFit w model e ρ := by cases e <;> trivial

/-- Every source constructor preserves partial denotation under concrete leaf
and environment equations. The numeric premise is supplied by source admission;
it contains no target evaluation or final constraint truth. -/
theorem encodeAt_agrees {s : Support n m} {l : Layout n m} {b : IR.Expr.Bounds n}
    {o : Observation n m} {i : Instance} {f : Atom → Nat}
    (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (hw : 1 ≤ b.width ∧ b.width ≤ 16) (hl : LayoutRep s l o i f) (hbuilt : LayoutBuilt l)
    (fuel : Nat) (e : Syntax n m) (h : e.depth < fuel)
    {Γ : List (Local n)} {t : Ty n} (ht : e.Typed s Γ t) (ho : e.Observed s)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) (env : List Nat) (hen : EnvironmentRep s f ρ env)
    (hfit : AllNumbersFit b.width (extend s o hv) (interpret s e ht) ρ) :
    Agrees s f b.width i env ((interpret s e ht).denote (extend s o hv) ρ)
      (encodeAt s l b fuel e h ht) := by
  induction fuel generalizing e Γ t ρ env with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ fuel ih =>
    cases e with
    | boolean v =>
      subst t
      refine ⟨rfl, ?_⟩
      intro p hp
      cases Option.some.inj hp
      change (if v then Formula.truth else Formula.falsity).eval b.width i env = some (propBool (v = true))
      cases v <;> change some _ = _ <;> simp [propBool]
    | integer z =>
      subst t
      refine ⟨rfl, ?_⟩
      intro v hvz
      cases Option.some.inj hvz
      exact source_range_target_int hw hfit
    | this =>
      subst t
      refine ⟨rfl, ?_⟩
      intro S hS
      cases Option.some.inj hS
      change Unary f {ρ.this} ((Rel.var Γ.length).eval i env)
      rw [Rel.eval_var, hen.1]
      exact unary_singleton _
    | extent x =>
      subst t
      refine ⟨rfl, ?_⟩
      intro S hS
      cases Option.some.inj hS
      have hx : s.integer[x] = false := ho x (by simp [Syntax.extents])
      change Unary f (fullExtent s o x) (l.extents[x].eval i env)
      simpa only [fullExtent, hx, Bool.false_eq_true, ↓reduceIte] using hl.extents x env
    | map e =>
      subst t
      refine ⟨rfl, ?_⟩
      intro S hS
      cases Option.some.inj hS
      change Represents (tupleOf f s (.relation s.maps[e].source s.maps[e].target))
        _ (l.maps[e].eval i env)
      rw [extend_map]
      exact binary_rep (hl.maps e env)
    | var pos =>
      cases hp : Γ[pos]? with
      | none => simp [Syntax.Typed, hp] at ht
      | some v =>
        simp only [Syntax.Typed, hp] at ht
        subst t
        simp only [interpret]
        split
        · rename_i hn; simp [hp] at hn
        · rename_i v' hp'
          have he : v' = v := Option.some.inj (hp'.symm.trans hp)
          subst v'
          refine ⟨rfl, ?_⟩
          intro S hS
          cases Option.some.inj hS
          change Unary f {ρ.lookup (lexical s Γ pos v hp')} ((Rel.var pos).eval i env)
          have hlookup := hen.2 _ (lexical s Γ pos v hp')
          rw [lexical_index s Γ pos v hp'] at hlookup
          rw [Rel.eval_var, hlookup]
          exact unary_singleton _
    | and a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      exact agrees_and (ih a hfa ha hoa ρ hρ env hen hfit.1)
        (ih c hfc hc hoc ρ hρ env hen hfit.2) ba bc
    | equal k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      exact agrees_equal (ih a hfa ha hoa ρ hρ env hen hfit.1)
        (ih c hfc hc hoc ρ hρ env hen hfit.2) ba bc hl.injective
    | less a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      exact agrees_less (ih a hfa ha hoa ρ hρ env hen hfit.1)
        (ih c hfc hc hoc ρ hρ env hen hfit.2) ba bc
    | arithmetic op a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      cases op with
      | add =>
        exact agrees_arithmetic .add (ih a hfa ha hoa ρ hρ env hen hfit.1)
          (ih c hfc hc hoc ρ hρ env hen hfit.2.1) ba bc hw hfit.2.2
      | subtract =>
        exact agrees_arithmetic .subtract (ih a hfa ha hoa ρ hρ env hen hfit.1)
          (ih c hfc hc hoc ρ hρ env hen hfit.2.1) ba bc hw hfit.2.2
    | setOp op k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      have hh := agrees_setOp op k (ih a hfa ha hoa ρ hρ env hen (collection_numbers_fit _ _ _))
        (ih c hfc hc hoc ρ hρ env hen (collection_numbers_fit _ _ _)) ba bc hl.injective
      cases op <;> exact hh
    | subset k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      exact agrees_subset k (ih a hfa ha hoa ρ hρ env hen (collection_numbers_fit _ _ _))
        (ih c hfc hc hoc ρ hρ env hen (collection_numbers_fit _ _ _)) ba bc hl.injective
    | image x y a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      apply agrees_binary (ih a hfa ha hoa ρ hρ env hen (collection_numbers_fit _ _ _))
        (ih c hfc hc hoc ρ hρ env hen (collection_numbers_fit _ _ _)) ba.1 bc.1
      intro A R _ _ hA hR
      have hRb : Binary f R ((encodeAt s l b fuel c hfc hc).value.eval i env) := by
        simpa only [ValueAgrees, Represents, tupleOf, Prod.exists, Binary] using hR
      exact unary_image hl.injective ba.2 bc.2 hA hRb
    | join x y z a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have ba := encodeAt_built s l b hbuilt fuel a hfa ha
      have bc := encodeAt_built s l b hbuilt fuel c hfc hc
      apply agrees_binary (ih a hfa ha hoa ρ hρ env hen (collection_numbers_fit _ _ _))
        (ih c hfc hc hoc ρ hρ env hen (collection_numbers_fit _ _ _)) ba.1 bc.1
      intro A R _ _ hA hR
      apply binary_rep
      apply binary_join hl.injective ba.2 bc.2
      · simpa only [ValueAgrees, Represents, tupleOf, Prod.exists, Binary] using hA
      · simpa only [ValueAgrees, Represents, tupleOf, Prod.exists, Binary] using hR
    | not a =>
      obtain ⟨rfl, ha⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      exact agrees_not (ih a hfa ha ho ρ hρ env hen hfit) (encodeAt_built s l b hbuilt fuel a hfa ha)
    | integerOf x a =>
      obtain ⟨rfl, hx, ha⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      obtain ⟨S, hS, hrec⟩ := interpreted_recorded a ha ho hv hb ρ hρ
      have hi := ih a hfa ha ho ρ hρ env hen (collection_numbers_fit _ _ _)
      rw [hS] at hi
      have hh := agrees_integerOf hl hb hw x hx hrec _ (encodeAt_built s l b hbuilt fuel a hfa ha) hi
      change ResultFits b.width (((interpret s a ha).denote (extend s o hv) ρ).bind
        (fun S => (integers.extract S).map ULift.up)) at hfit
      rw [hS, Option.bind_some] at hfit
      change Agrees s f b.width i env (t := .integer)
        (((interpret s a ha).denote (extend s o hv) ρ).bind (fun S => (integers.extract S).map ULift.up)) _
      rw [hS, Option.bind_some]
      exact hh hfit
    | cardinality k a =>
      obtain ⟨rfl, ha⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      obtain ⟨S, hS, hrec⟩ := interpreted_recorded a ha ho hv hb ρ hρ
      have hi := ih a hfa ha ho ρ hρ env hen (collection_numbers_fit _ _ _)
      rw [hS] at hi
      change ResultFits b.width (((interpret s a ha).denote (extend s o hv) ρ).bind
        Clafer.Constraints.finiteCard) at hfit
      rw [hS, Option.bind_some] at hfit
      change Agrees s f b.width i env (t := .integer)
        (((interpret s a ha).denote (extend s o hv) ρ).bind Clafer.Constraints.finiteCard) _
      rw [hS, Option.bind_some]
      exact agrees_cardinality k hi hl.injective (recorded_finite hrec) hw hfit
    | widenObjects x y p a =>
      obtain ⟨rfl, hp, ha⟩ := ht
      have hh := ih a (by simp only [Syntax.depth] at h; omega) ha ho ρ hρ env hen
        (collection_numbers_fit _ _ _)
      exact hh
    | widenRelation x y x' y' p q a =>
      obtain ⟨rfl, hp, hq, ha⟩ := ht
      exact ih a (by simp only [Syntax.depth] at h; omega) ha ho ρ hρ env hen
        (collection_numbers_fit _ _ _)
    | all v d a =>
      obtain ⟨rfl, hfresh, hd, ha⟩ := ht
      have hfd : d.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at h; omega
      have hod : d.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      obtain ⟨S, hS, hrec⟩ := interpreted_recorded d hd hod hv hb ρ hρ
      have hi := ih d hfd hd hod ρ hρ env hen (collection_numbers_fit _ _ _)
      rw [hS] at hi
      have hh := agrees_all (encodeAt_built s l b hbuilt fuel d hfd hd)
        (encodeAt_built s l b hbuilt fuel a hfa ha) hi
        (fun x => (interpret s a ha).denote (extend s o hv) (ρ.push (binder s v) x))
        (fun x hx => ih a hfa ha hoa (ρ.push (binder s v) x) (recorded_push hρ v (hrec hx))
          (f x :: env) (environment_push hen v x) (hfit S hS x hx))
      change Agrees s f b.width i env (t := .boolean)
        (((interpret s d hd).denote (extend s o hv) ρ).bind fun S => Clafer.Constraints.universal S
          (fun x => (interpret s a ha).denote (extend s o hv) (ρ.push (binder s v) x))) _
      rw [hS, Option.bind_some]
      exact hh
    | located _ a => exact ih a (by simp only [Syntax.depth] at h; omega) ht.2 ho ρ hρ env hen hfit

/-- Source admission discharges every numeric intermediate premise. -/
theorem admitted_agrees {s : Support n m} {l : Layout n m} {b : IR.Expr.Bounds n}
    {o : Observation n m} {i : Instance} {f : Atom → Nat} {Γ t}
    (a : Admitted s b Γ t) (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (hl : LayoutRep s l o i f) (hbuilt : LayoutBuilt l)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) (env : List Nat) (hen : EnvironmentRep s f ρ env) :
    Agrees s f b.width i env (denote a.checked (extend s o hv) ρ) (encode l a) :=
  encodeAt_agrees hv hb a.width hl hbuilt a.checked.term.budget a.checked.term.raw
    a.checked.term.bound a.checked.typed a.checked.observed ρ hρ env hen
    (admitted_all_numbers_fit a hv hb ρ hρ)

/-- The same constructor correspondence holds in every full mathematical integer
extension of the recorded objects and original links. -/
theorem admitted_full_agrees {s : Support n m} {l : Layout n m} {b : IR.Expr.Bounds n}
    {o : Observation n m} {i : Instance} {f : Atom → Nat} {Γ t}
    (a : Admitted s b Γ t) (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (hl : LayoutRep s l o i f) (hbuilt : LayoutBuilt l)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hm : ExtendsObservation s o hv model)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) (env : List Nat) (hen : EnvironmentRep s f ρ env) :
    Agrees s f b.width i env (denote a.checked model ρ) (encode l a) := by
  rw [finite_observation_agreement a.checked hv model hm ρ]
  exact admitted_agrees a hv hb hl hbuilt ρ hρ env hen

/-- An attached hard constraint is defined and true at every original owner,
including abstract/inherited owners selected by the head relation. The owner
relation equation is independent of constraint truth. -/
theorem attachment_iff {s : Support n m} {l : Layout n m} {b : IR.Expr.Bounds n}
    {o : Observation n m} {i : Instance} {f : Atom → Nat}
    (a : Admitted s b [] .boolean) (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (hl : LayoutRep s l o i f) (hbuilt : LayoutBuilt l)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hm : ExtendsObservation s o hv model) (owners : Rel)
    (howners : Unary f (atomSet o.objects[s.context]) (owners.eval i [])) :
    (attach owners (encode l a)).eval b.width i [] = some true ↔
      ∀ owner ∈ atomSet o.objects[s.context],
        denote a.checked model (Clafer.Constraints.Environment.closed owner) = some ⟨True⟩ := by
  have hc := encodeAt_built s l b hbuilt a.checked.term.budget a.checked.term.raw
    a.checked.term.bound a.checked.typed
  have hpoint : ∀ owner ∈ atomSet o.objects[s.context],
      (encode l a).holds.eval b.width i [f owner] = some true ↔
      denote a.checked model (Clafer.Constraints.Environment.closed owner) = some ⟨True⟩ := by
    intro owner ho
    apply agrees_holds
    · apply admitted_full_agrees a hv hb hl hbuilt model hm
      · exact ⟨ho, fun _ v => (Clafer.Constraints.Var.closed.false v).elim⟩
      · exact ⟨rfl, fun _ v => (Clafer.Constraints.Var.closed.false v).elim⟩
    · exact hc
  have hholds : (encode l a).holds.Term := .conj hc.1 hc.2
  rw [attach, Formula.eval_all_true hholds]
  constructor
  · intro h owner ho
    exact (hpoint owner ho).mp (h [f owner] ((howners _).mpr ⟨owner, ho, rfl⟩))
  · intro h tuple ht
    obtain ⟨owner, ho, rfl⟩ := (howners tuple).mp ht
    exact (hpoint owner ho).mpr (h owner ho)

end ClaferCompiler.Correctness.ExpressionMeaning
