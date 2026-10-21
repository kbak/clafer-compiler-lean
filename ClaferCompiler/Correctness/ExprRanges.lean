module

public import ClaferCompiler.Correctness.ExprObservationBounds

@[expose] public section
namespace ClaferCompiler.Correctness.Expressions
open IR.Expr SemanticsBridge.Expr
open Clafer.Constraints (relationalImage relationalJoin)

/-! Soundness of the existing executable source range analyzer against the
independent upstream denotation, with no source-truth premise.
[proof->req~compiler-arithmetic~1] -/

variable {s : Support n m} {o : Observation n m} {b : Bounds n}

/-- An undefined number stays undefined. Collections are total, finite sets;
their bound counts distinct objects/tuples, not link occurrences. -/
def EstimateSound (s : Support n m) (width : Nat) : (t : Ty n) → Estimate →
    Option (Clafer.Constraints.Value Atom (type s t)) → Prop
  | .boolean, .truth, _ => True
  | .integer, .number r, v => r.fits width = true ∧ ∀ z, v = some z → r.Contains z.down
  | .collection _, .collection budget, v => ∃ S, v = some S ∧ S.Finite ∧ S.ncard ≤ budget
  | _, _, _ => False

theorem number_ok {r : Interval} {est : Estimate} (h : number b r = .ok est) :
    est = .number r ∧ r.fits b.width = true := by
  unfold number at h
  split at h <;> simp_all

theorem interpreted_recorded {Γ k} (e : Syntax n m)
    (ht : e.Typed s Γ (.collection k)) (ho : e.Observed s)
    (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    ∃ S, (interpret s e ht).denote (extend s o hv) ρ = some S ∧
      RecordedCollection o (collection s k) S := by
  apply recorded_result hv hb (interpret s e ht) _ ρ hρ
  intro x hx
  exact ho x (((interpret_footprint s e ht).1 x).mp hx)

theorem analyzeAt_sound (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (fuel : Nat) (e : Syntax n m) (hf : e.depth < fuel)
    {Γ t} (ht : e.Typed s Γ t) (ho : e.Observed s) {est : Estimate}
    (he : analyzeAt s b fuel e hf = .ok est)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    EstimateSound s b.width t est ((interpret s e ht).denote (extend s o hv) ρ) := by
  induction fuel generalizing e Γ t est with
  | zero => exact (Nat.not_lt_zero _ hf).elim
  | succ fuel ih =>
    cases e with
    | boolean v =>
      subst t
      have : est = .truth := by simpa [analyzeAt] using he.symm
      subst est; trivial
    | integer v =>
      subst t
      obtain ⟨rfl, hfit⟩ := number_ok he
      refine ⟨hfit, ?_⟩
      intro z hz
      have : z = ⟨v⟩ := (Option.some.inj hz).symm
      subst z
      exact ⟨le_refl _, le_refl _⟩
    | this =>
      subst t
      have : est = .collection 1 := by simpa [analyzeAt] using he.symm
      subst est
      exact ⟨_, rfl, Set.finite_singleton _, by simp⟩
    | var pos =>
      cases hp : Γ[pos]? with
      | none => simp [Syntax.Typed, hp] at ht
      | some v =>
        simp only [Syntax.Typed, hp] at ht
        subst t
        have : est = .collection 1 := by simpa [analyzeAt] using he.symm
        subst est
        refine ⟨{ρ.lookup (lexical s Γ pos v hp)}, ?_, Set.finite_singleton _, by simp⟩
        simp only [interpret]
        split
        · rename_i hnone; simp [hp] at hnone
        · rename_i w hw
          have hwv : w = v := Option.some.inj (hw.symm.trans hp)
          subst w
          rfl
    | extent x =>
      subst t
      have : est = .collection b.extents[x] := by simpa [analyzeAt] using he.symm
      subst est
      have hn : s.integer[x] = false := ho x (by simp [Syntax.extents])
      refine ⟨atomSet o.objects[x], ?_, atomSet_finite _, withinBounds_card hb x⟩
      simp [interpret, fullExtent, hn]
    | map e =>
      subst t
      have : est = .collection (b.extents[s.maps[e].source] * b.extents[s.maps[e].target]) :=
        by simpa [analyzeAt] using he.symm
      subst est
      have hsub : observedRelation o.links[e] ⊆
          (atomSet o.objects[s.maps[e].source]) ×ˢ (atomSet o.objects[s.maps[e].target]) := by
        rintro p ⟨l, hl, hs, ht⟩
        have hh := withinBounds_links hb e l hl
        exact ⟨hs ▸ hh.1, ht ▸ hh.2⟩
      refine ⟨observedRelation o.links[e], by exact congrArg some (extend_map hv e),
        observed_relation_finite _, ?_⟩
      exact (Set.ncard_le_ncard hsub ((atomSet_finite _).prod (atomSet_finite _))).trans
        (by simpa using Nat.mul_le_mul (withinBounds_card hb _) (withinBounds_card hb _))
    | and a c | equal k a c | less a c | subset k a c | all v a c =>
      obtain ⟨rfl, _⟩ := ht
      have hest : est = .truth := by
        change (do
          let _ ← analyzeAt s b fuel a (by simp only [Syntax.depth] at hf; omega)
          let _ ← analyzeAt s b fuel c (by simp only [Syntax.depth] at hf; omega)
          pure Estimate.truth) = .ok est at he
        simp only [bind, Except.bind] at he
        split at he <;> simp_all [pure, Except.pure]
        split at he <;> simp_all
      subst est; trivial
    | not a =>
      obtain ⟨rfl, _⟩ := ht
      have hest : est = .truth := by
        change (do
          let _ ← analyzeAt s b fuel a (by simp only [Syntax.depth] at hf; omega)
          pure Estimate.truth) = .ok est at he
        simp only [bind, Except.bind] at he
        split at he <;> simp_all [pure, Except.pure]
      subst est; trivial
    | located loc a =>
      exact ih a (by simp only [Syntax.depth] at hf; omega) ht.2 ho he ρ hρ
    | widenObjects x y path a =>
      obtain ⟨rfl, hp, ha⟩ := ht
      cases est <;> exact ih a (by simp only [Syntax.depth] at hf; omega) ha ho he ρ hρ
    | widenRelation x y x' y' p q a =>
      obtain ⟨rfl, hp, hq, ha⟩ := ht
      cases est <;> exact ih a (by simp only [Syntax.depth] at hf; omega) ha ho he ρ hρ
    | integerOf x a =>
      obtain ⟨rfl, hx, ha⟩ := ht
      have hnum : number b b.integers[x] = .ok est := by
        change (do
          let _ ← analyzeAt s b fuel a (by simp only [Syntax.depth] at hf; omega)
          number b b.integers[x]) = .ok est at he
        simp only [bind, Except.bind] at he
        split at he <;> simp_all
      obtain ⟨rfl, hfit⟩ := number_ok hnum
      obtain ⟨S, hS, hrec⟩ := interpreted_recorded a ha ho hv hb ρ hρ
      refine ⟨hfit, ?_⟩
      intro z hz
      change ((interpret s a ha).denote (extend s o hv) ρ).bind
        (fun S => (integers.extract S).map ULift.up) = some z at hz
      rw [hS] at hz
      cases hex : integers.extract S with
      | none => simp [hex] at hz
      | some value =>
        have heq : S = {Atom.integer value} := (integers.extract_eq_some_iff S value).mp hex
        have hr : Atom.integer value ∈ atomSet o.objects[x] :=
          hrec (by simp [heq])
        have hz' : z = ⟨value⟩ := by simpa [hex] using hz.symm
        subst z
        exact (withinBounds_objects hb x).2.2 _ hr |>.2.2
    | cardinality k a =>
      obtain ⟨rfl, ha⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      change (do
        match ← analyzeAt s b fuel a hfa with
        | .collection cap => number b ⟨0, cap⟩
        | _ => .error boundsError) = .ok est at he
      cases hres : analyzeAt s b fuel a hfa with
      | error err => simp [hres, bind, Except.bind] at he
      | ok ea =>
        have hi := ih a hfa ha ho hres ρ hρ
        cases ea with
        | truth => exact hi.elim
        | number r => exact hi.elim
        | collection cap =>
          have hn : number b ⟨0, cap⟩ = .ok est := by simpa [hres, bind, Except.bind] using he
          obtain ⟨rfl, hfit⟩ := number_ok hn
          obtain ⟨S, hS, hfinite, hcard⟩ := hi
          refine ⟨hfit, ?_⟩
          intro z hz
          have hz' : z = ⟨(S.ncard : Int)⟩ := by
            simpa [interpret, Clafer.Constraints.Expr.denote, hS,
              Clafer.Constraints.finiteCard, hfinite] using hz.symm
          subst z
          exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hcard⟩
    | arithmetic op a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do combineNumbers b op (← analyzeAt s b fuel a hfa) (← analyzeAt s b fuel c hfc)) = .ok est at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec =>
          have hiA := ih a hfa ha hoa hresA ρ hρ
          have hiC := ih c hfc hc hoc hresC ρ hρ
          cases ea <;> cases ec <;> simp only [EstimateSound] at hiA hiC
          rename_i ra rc
          have hn : number b (match (generalizing := false) op with | .add => ra.add rc | .subtract => ra.subtract rc) = .ok est :=
            by cases op <;> simpa [hresA, hresC, combineNumbers, bind, Except.bind] using he
          obtain ⟨rfl, hfit⟩ := number_ok hn
          refine ⟨hfit, ?_⟩
          intro z hz
          change Clafer.Constraints.lift₂ _ _ _ = some z at hz
          cases hvA : (interpret s a ha).denote (extend s o hv) ρ with
          | none => simp [Clafer.Constraints.lift₂, hvA] at hz
          | some va =>
            cases hvC : (interpret s c hc).denote (extend s o hv) ρ with
            | none => simp [Clafer.Constraints.lift₂, hvA, hvC] at hz
            | some vc =>
              have ha := hiA.2 va hvA
              have hc := hiC.2 vc hvC
              cases op <;>
                simp [Clafer.Constraints.lift₂, hvA, hvC, arithmetic] at hz
              · subst z; exact add_contains ha hc
              · subst z; exact subtract_contains ha hc
    | setOp op k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hstep : analyzeAt s b (fuel + 1) (.setOp op k a c) hf = (do match (← analyzeAt s b fuel a hfa), (← analyzeAt s b fuel c hfc) with
        | .collection ca, .collection cc => pure (Estimate.collection (match (generalizing := false) op with
            | .union => ca + cc | .difference => ca | .intersection => min ca cc))
        | _, _ => .error boundsError) := by cases op <;> rfl
      rw [hstep] at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec =>
          have hiA := ih a hfa ha hoa hresA ρ hρ
          have hiC := ih c hfc hc hoc hresC ρ hρ
          cases ea <;> cases ec <;> simp only [EstimateSound] at hiA hiC
          rename_i ca cc
          have hest : est = .collection (match (generalizing := false) op with
              | .union => ca + cc | .difference => ca | .intersection => min ca cc) :=
            by cases op <;> simpa [hresA, hresC, bind, Except.bind, pure, Except.pure] using he.symm
          subst est
          obtain ⟨A, hA, hfA, hcA⟩ := hiA
          obtain ⟨C, hC, hfC, hcC⟩ := hiC
          refine ⟨Clafer.Constraints.collectionOp (setOp op) A C,
            by simp [interpret, hA, hC, Clafer.Constraints.lift₂], ?_⟩
          cases op with
          | union => exact ⟨hfA.union hfC, (Set.ncard_union_le A C).trans (Nat.add_le_add hcA hcC)⟩
          | difference => exact ⟨hfA.subset Set.sdiff_subset,
              (Set.ncard_le_ncard Set.sdiff_subset hfA).trans hcA⟩
          | intersection => exact ⟨hfA.subset Set.inter_subset_left,
              le_min ((Set.ncard_le_ncard Set.inter_subset_left hfA).trans hcA)
                ((Set.ncard_le_ncard Set.inter_subset_right hfC).trans hcC)⟩
    | image x y a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do
        let _ ← analyzeAt s b fuel a hfa
        match ← analyzeAt s b fuel c hfc with
        | .collection cap => pure (Estimate.collection cap)
        | _ => .error boundsError) = .ok est at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec =>
          have hiC := ih c hfc hc hoc hresC ρ hρ
          cases ec <;> simp only [EstimateSound] at hiC
          rename_i cap
          have hest : est = .collection cap := by simpa [hresA, hresC, bind, Except.bind, pure, Except.pure] using he.symm
          subst est
          obtain ⟨A, hA, _⟩ := interpreted_recorded a ha hoa hv hb ρ hρ
          obtain ⟨C, hC, hfC, hcC⟩ := hiC
          have hsub : relationalImage A C ⊆ Prod.snd '' C := by
            rintro y ⟨x, _, hxy⟩; exact ⟨(x, y), hxy, rfl⟩
          exact ⟨_, by simp [interpret, hA, hC, Clafer.Constraints.lift₂],
            (hfC.image _).subset hsub, (image_card hfC).trans hcC⟩
    | join x y z a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      have hfa : a.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hfc : c.depth < fuel := by simp only [Syntax.depth] at hf; omega
      have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      have hoc : c.Observed s := fun x hx => ho x (by simp [Syntax.extents, hx])
      change (do match (← analyzeAt s b fuel a hfa), (← analyzeAt s b fuel c hfc) with
        | .collection ca, .collection cc => pure (Estimate.collection (ca * cc))
        | _, _ => .error boundsError) = .ok est at he
      cases hresA : analyzeAt s b fuel a hfa with
      | error err => simp [hresA, bind, Except.bind] at he
      | ok ea =>
        cases hresC : analyzeAt s b fuel c hfc with
        | error err => simp [hresA, hresC, bind, Except.bind] at he
        | ok ec =>
          have hiA := ih a hfa ha hoa hresA ρ hρ
          have hiC := ih c hfc hc hoc hresC ρ hρ
          cases ea <;> cases ec <;> simp only [EstimateSound] at hiA hiC
          rename_i ca cc
          have hest : est = .collection (ca * cc) := by simpa [hresA, hresC, bind, Except.bind, pure, Except.pure] using he.symm
          subst est
          obtain ⟨A, hA, hfA, hcA⟩ := hiA
          obtain ⟨C, hC, hfC, hcC⟩ := hiC
          have hsub : relationalJoin A C ⊆ (Prod.fst '' A) ×ˢ (Prod.snd '' C) := by
            rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
            exact ⟨⟨(x,y), hxy, rfl⟩, ⟨(y,z), hyz, rfl⟩⟩
          exact ⟨_, by simp [interpret, hA, hC, Clafer.Constraints.lift₂],
            ((hfA.image _).prod (hfC.image _)).subset hsub,
            (join_card hfA hfC).trans (Nat.mul_le_mul hcA hcC)⟩

theorem admitted_sound (a : Admitted s b Γ t) (hv : ObservationValid s o)
    (hb : o.withinBounds s b = true)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    EstimateSound s b.width t a.estimate (denote a.checked (extend s o hv) ρ) :=
  analyzeAt_sound hv hb a.checked.term.budget a.checked.term.raw a.checked.term.bound
    a.checked.typed a.checked.observed a.analyzed ρ hρ

end ClaferCompiler.Correctness.Expressions
