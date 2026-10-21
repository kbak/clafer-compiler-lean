module

public import ClaferCompiler.Correctness.ExprRanges

@[expose] public section
namespace ClaferCompiler.Correctness.Expressions
open IR.Expr SemanticsBridge.Expr

/-! The guarantee includes every numeric intermediate and both Boolean branches.
Quantifier bodies use actual domain objects, with `this` unchanged.
[proof->req~compiler-arithmetic~1] -/

variable {s : Support n m} {o : Observation n m} {b : Bounds n}

/-- A property of the independent source meaning, not a second evaluator.
The partial singleton operation may still be undefined. -/
def ResultFits (width : Nat) (v : Option (ULift Int)) : Prop :=
  ∀ z, v = some z → (signedRange width).Contains z.down

noncomputable def AllNumbersFit (width : Nat)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom) :
    {Γ : List (Clafer.Constraints.Local (support s))} → {t : Clafer.Constraints.Ty (support s)} →
    Clafer.Constraints.Expr (support s) Γ t →
    Clafer.Constraints.Environment (support s) Atom Γ → Prop
  | _, _, .integer z, _ => (signedRange width).Contains z
  | _, _, .arithmetic op a c, ρ => AllNumbersFit width model a ρ ∧ AllNumbersFit width model c ρ ∧
      ResultFits width ((Clafer.Constraints.Expr.arithmetic op a c).denote model ρ)
  | _, _, .integerOf hp a, ρ => ResultFits width ((Clafer.Constraints.Expr.integerOf hp a).denote model ρ)
  | _, _, .cardinality a, ρ => ResultFits width ((Clafer.Constraints.Expr.cardinality a).denote model ρ)
  | _, _, .and a c, ρ => AllNumbersFit width model a ρ ∧ AllNumbersFit width model c ρ
  | _, _, .equal a c, ρ => AllNumbersFit width model a ρ ∧ AllNumbersFit width model c ρ
  | _, _, .less a c, ρ => AllNumbersFit width model a ρ ∧ AllNumbersFit width model c ρ
  | _, _, .not a, ρ => AllNumbersFit width model a ρ
  | _, _, .all v _ domain body, ρ => ∀ S, domain.denote model ρ = some S →
      ∀ x ∈ S, AllNumbersFit width model body (ρ.push v x)
  | _, _, _, _ => True

theorem analyzed_integer_fits (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (fuel : Nat) (e : Syntax n m) (hf : e.depth < fuel)
    {Γ} (ht : e.Typed s Γ .integer) (ho : e.Observed s) {est : Estimate}
    (he : analyzeAt s b fuel e hf = .ok est)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    ResultFits b.width ((interpret s e ht).denote (extend s o hv) ρ) := by
  have hs := analyzeAt_sound hv hb fuel e hf ht ho he ρ hρ
  cases est <;> simp only [EstimateSound] at hs
  intro z hz
  exact fits_representable hs.1 (hs.2 z hz)

/-- Accepted syntax checks every numeric subtree even if a Boolean branch is
false. Empty universal domains need no body evaluation, while their syntax was
still conservatively analyzed. No final truth or successful extraction is assumed. -/
theorem analyzeAt_all_numbers_fit (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (fuel : Nat) (e : Syntax n m) (hf : e.depth < fuel)
    {Γ t} (ht : e.Typed s Γ t) (ho : e.Observed s) {est : Estimate}
    (he : analyzeAt s b fuel e hf = .ok est)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    AllNumbersFit b.width (extend s o hv) (interpret s e ht) ρ := by
  induction fuel generalizing e Γ t est with
  | zero => exact (Nat.not_lt_zero _ hf).elim
  | succ fuel ih =>
    cases e with
    | boolean v => subst t; trivial
    | integer z =>
      subst t
      exact analyzed_integer_fits hv hb _ _ hf rfl ho he ρ hρ ⟨z⟩ rfl
    | this => subst t; trivial
    | extent x => subst t; trivial
    | map e => subst t; trivial
    | var pos =>
      cases hp : Γ[pos]? with
      | none => simp [Syntax.Typed, hp] at ht
      | some v =>
        simp only [Syntax.Typed, hp] at ht
        subst t
        simp only [interpret]
        split
        · rename_i hn; simp [hp] at hn
        · rename_i w hw
          have hwv : w = v := Option.some.inj (hw.symm.trans hp)
          subst w
          trivial
    | integerOf x a =>
      obtain ⟨rfl, hx, ha⟩ := ht
      exact analyzed_integer_fits hv hb _ _ hf ⟨rfl, hx, ha⟩ ho he ρ hρ
    | cardinality k a =>
      obtain ⟨rfl, ha⟩ := ht
      exact analyzed_integer_fits hv hb _ _ hf ⟨rfl, ha⟩ ho he ρ hρ
    | setOp op k a c | subset k a c | image x y a c | join x y z a c =>
      obtain ⟨rfl, _⟩ := ht
      trivial
    | widenObjects x y p a =>
      obtain ⟨rfl, _, _⟩ := ht
      trivial
    | widenRelation x y x' y' p q a =>
      obtain ⟨rfl, _, _, _⟩ := ht
      trivial
    | located loc a => exact ih a (by simp only [Syntax.depth] at hf; omega) ht.2 ho he ρ hρ
    | not a =>
      obtain ⟨rfl, ha⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      change (do let _ ← analyzeAt s b fuel a hfa; pure Estimate.truth) = .ok est at he
      cases hres : analyzeAt s b fuel a hfa with
      | error err => simp [hres, bind, Except.bind] at he
      | ok ea => exact ih a hfa ha ho hres ρ hρ
    | and a c | equal k a c | less a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do
        let _ ← analyzeAt s b fuel a hfa
        let _ ← analyzeAt s b fuel c hfc
        pure Estimate.truth) = .ok est at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec => exact ⟨ih a hfa ha hoa hresA ρ hρ, ih c hfc hc hoc hresC ρ hρ⟩
    | arithmetic op a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfit := analyzed_integer_fits hv hb _ _ hf ⟨rfl, ha, hc⟩ ho he ρ hρ
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do
        combineNumbers b op (← analyzeAt s b fuel a hfa) (← analyzeAt s b fuel c hfc)) = .ok est at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec => exact ⟨ih a hfa ha hoa hresA ρ hρ, ih c hfc hc hoc hresC ρ hρ, hfit⟩
    | all v domain body =>
      obtain ⟨rfl, _, hd, hbody⟩ := ht
      have hfd : domain.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfb : body.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hod : domain.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hob : body.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do
        let _ ← analyzeAt s b fuel domain hfd
        let _ ← analyzeAt s b fuel body hfb
        pure Estimate.truth) = .ok est at he
      cases hresD : analyzeAt s b fuel domain hfd with
      | error err => simp [hresD, bind, Except.bind] at he
      | ok ed =>
        cases hresB : analyzeAt s b fuel body hfb with
        | error err => simp [hresD, hresB, bind, Except.bind] at he
        | ok eb =>
          intro S hS x hx
          obtain ⟨T, hT, hrec⟩ := interpreted_recorded domain hd hod hv hb ρ hρ
          have heq : T = S := Option.some.inj (hT.symm.trans hS)
          subst T
          exact ih body hfb hbody hob hresB (ρ.push (binder s v) x) (recorded_push hρ v (hrec hx))

theorem admitted_all_numbers_fit (a : Admitted s b Γ t) (hv : ObservationValid s o)
    (hb : o.withinBounds s b = true)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    AllNumbersFit b.width (extend s o hv) (interpret s a.checked.term.raw a.checked.typed) ρ :=
  analyzeAt_all_numbers_fit hv hb a.checked.term.budget a.checked.term.raw a.checked.term.bound
    a.checked.typed a.checked.observed a.analyzed ρ hρ

/-- The range result is unchanged in every full mathematical integer extension,
using the previously proved observation bridge. It never truncates Int. -/
theorem admitted_extension_sound (a : Admitted s b Γ t) (hv : ObservationValid s o)
    (hb : o.withinBounds s b = true)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hm : ExtendsObservation s o hv model)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    EstimateSound s b.width t a.estimate (denote a.checked model ρ) := by
  rw [finite_observation_agreement a.checked hv model hm ρ]
  exact admitted_sound a hv hb ρ hρ

/-- Public executable candidate checks discharge the finite environment and
observation premises. Structural binding validity is still explicit. -/
theorem bounded_environment_sound (a : Admitted s b Γ t) (hv : ObservationValid s o)
    (ρ : Environment) (hρ : ρ.bounded s b o Γ = true) :
    EstimateSound s b.width t a.estimate (denote a.checked (extend s o hv) (environment s Γ ρ)) ∧
    AllNumbersFit b.width (extend s o hv) (interpret s a.checked.term.raw a.checked.typed)
      (environment s Γ ρ) := by
  have hr := environment_recorded Γ ρ hρ
  have hb : o.withinBounds s b = true := by
    simp only [Environment.bounded, Bool.and_eq_true] at hρ
    exact hρ.1.1.2
  exact ⟨admitted_sound a hv hb _ hr, admitted_all_numbers_fit a hv hb _ hr⟩

theorem source_range_target_int {width : Nat} {z : Int}
    (hw : 1 ≤ width ∧ width ≤ 16) (hz : (signedRange width).Contains z) :
    Backend.Alloy.boundedInt width z = some z := by
  apply (Backend.Alloy.boundedInt_some_iff width z).mpr
  simp only [Backend.Alloy.fitsInt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hw.1, hw.2⟩, ?_⟩, ?_⟩
  · simpa [Backend.Alloy.minInt, signedRange, Interval.Contains] using hz.1
  · simpa [Backend.Alloy.maxInt, signedRange, Interval.Contains] using hz.2

/-- The same mathematical value can be admitted by the independent target's
bounded integer operation. This is a scalar bridge, not an encoding theorem. -/
theorem admitted_integer_target (a : Admitted s b Γ .integer) (hv : ObservationValid s o)
    (hb : o.withinBounds s b = true)
    (full : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hfull : ExtendsObservation s o hv full)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) {z : Int} (hz : denote a.checked full ρ = some ⟨z⟩) :
    Backend.Alloy.boundedInt b.width z = some z := by
  have h := admitted_extension_sound a hv hb full hfull ρ hρ
  cases he : a.estimate <;> simp only [he, EstimateSound] at h
  exact source_range_target_int a.width (fits_representable h.1 (h.2 ⟨z⟩ hz))

end ClaferCompiler.Correctness.Expressions
