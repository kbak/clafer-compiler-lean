module

public import ClaferCompiler.Correctness.PipelineQueries
public import ClaferCompiler.Correctness.ExprRanges

@[expose] public section
/-! Query-local agreement permits full primitive maps to be infinite.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr SemanticsBridge.Expr Expressions
open Clafer.Constraints (IntegerBinding)
open DPGraph.Predicates (relationalImage ambientRelation)

theorem universal_on_congr (S : Set Atom)
    (f g : Atom → Option (ULift.{0} Prop)) (h : ∀ x ∈ S, f x = g x) :
    Clafer.Constraints.universal S f = Clafer.Constraints.universal S g := by
  have hd : (∀ x ∈ S, (f x).isSome = true) = (∀ x ∈ S, (g x).isSome = true) :=
    propext (forall_congr' fun x => forall_congr' fun hx => by rw [h x hx])
  have ht : (∀ x ∈ S, f x = some ⟨True⟩) = (∀ x ∈ S, g x = some ⟨True⟩) :=
    propext (forall_congr' fun x => forall_congr' fun hx => by rw [h x hx])
  unfold Clafer.Constraints.universal
  rw [hd,ht]

structure QueryAgreement (c : IR.Structural.Core n) (s : Support n m)
    (o : Observation n m) (hv : ObservationValid s o)
    (model : IntegerBinding.{0,0} (support s) Atom) : Prop where
  objects : ∀ x : Fin n, s.integer[x] = false → model.model.obj x = (extend s o hv).model.obj x
  extraction : ∀ (x : Fin n) (S : Set Atom), S ⊆ atomSet o.objects[x] →
    model.realization.extract S = integers.extract S
  navigation : ∀ e : Fin m, HeadSafe c s e → ∀ (S : Set Atom), S ⊆ atomSet o.objects[s.maps[e].source] →
    relationalImage S (ambientRelation (model.model.map ((support s).arrow e))) =
      relationalImage S (observedRelation o.links[e])

/-- Denotation agreement only asks about map images of recorded input sets.
It never equates the full primitive containment/parent relation with a finite
table, and preserves undefined extraction as well as true/false results. -/
theorem query_agreement {c : IR.Structural.Core n} {s : Support n m}
    {o : Observation n m} {bounds : Bounds n} (hv : ObservationValid s o)
    (hb : o.withinBounds s bounds = true) (model : IntegerBinding.{0,0} (support s) Atom)
    (hm : QueryAgreement c s o hv model) (e : Syntax n m) {Γ t}
    (ht : e.Typed s Γ t) (hn : NavigationOnly c s e) (ho : e.Observed s)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    (interpret s e ht).denote model ρ = (interpret s e ht).denote (extend s o hv) ρ := by
  induction e generalizing Γ t with
  | boolean b => subst t; rfl
  | integer z => subst t; rfl
  | this => subst t; rfl
  | extent x =>
    subst t
    exact congrArg Option.some (hm.objects x (ho x (by simp [Syntax.extents])))
  | var v =>
    cases he : Γ[v]? with
    | none => simp [Syntax.Typed,he] at ht
    | some b =>
      simp only [Syntax.Typed,he] at ht
      subst t
      simp only [interpret]
      split
      · rename_i hnone; simp [he] at hnone
      · rename_i b' he'
        have hb' : b' = b := Option.some.inj (he'.symm.trans he)
        subst b'
        rfl
  | map e => exact hn.elim
  | and a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | not a ih =>
    obtain ⟨rfl,ha⟩ := ht
    simp only [interpret,Clafer.Constraints.Expr.denote,ih ha hn ho ρ hρ]
  | equal k a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | less a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | arithmetic op a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | integerOf x a ih =>
    obtain ⟨rfl,hint,ha⟩ := ht
    obtain ⟨S,hS,hrec⟩ := interpreted_recorded a ha ho hv hb ρ hρ
    simp only [interpret,Clafer.Constraints.Expr.denote,ih ha hn ho ρ hρ,hS,Option.bind_some]
    exact congrArg (Option.map ULift.up) (hm.extraction x S hrec)
  | cardinality k a ih =>
    obtain ⟨rfl,ha⟩ := ht
    simp only [interpret,Clafer.Constraints.Expr.denote,ih ha hn ho ρ hρ]
  | setOp op k a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | subset k a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hob : b.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    simp only [interpret,Clafer.Constraints.Expr.denote,
      iha ha hn.1 hoa ρ hρ,ihb hb' hn.2 hob ρ hρ]
  | image x y a b iha ihb =>
    obtain ⟨rfl,ha,hb'⟩ := ht
    clear ihb
    cases b <;> try exact hn.elim
    rename_i e
    have hsource : s.maps[e].source = x := by
      have := congrArg (fun t => match t with
        | Ty.collection (.relation x _) => some x | _ => none) hb'
      exact Option.some.inj this.symm
    have htarget : s.maps[e].target = y := by
      have := congrArg (fun t => match t with
        | Ty.collection (.relation _ y) => some y | _ => none) hb'
      exact Option.some.inj this.symm
    subst x; subst y
    have hoa : a.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    obtain ⟨S,hS,hrec⟩ := interpreted_recorded a ha hoa hv hb ρ hρ
    simp only [interpret,Clafer.Constraints.Expr.denote,iha ha hn.1 hoa ρ hρ,hS,
      Clafer.Constraints.lift₂,Option.bind_some,Option.map_some,extend_map]
    exact congrArg Option.some (hm.navigation e hn.2 S hrec)
  | join => exact hn.elim
  | widenObjects x y p a ih =>
    obtain ⟨rfl,hpath,ha⟩ := ht
    exact ih ha hn ho ρ hρ
  | widenRelation => exact hn.elim
  | all b domain body ihd ihbody =>
    obtain ⟨rfl,fresh,hd,ha⟩ := ht
    have hod : domain.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    have hoa : body.Observed s := fun x hx => ho x (by simp [Syntax.extents,hx])
    obtain ⟨S,hS,hrec⟩ := interpreted_recorded domain hd hod hv hb ρ hρ
    change ((interpret s domain hd).denote model ρ).bind (fun S =>
        Clafer.Constraints.universal S (fun x => (interpret s body ha).denote model (ρ.push (binder s b) x))) =
      ((interpret s domain hd).denote (extend s o hv) ρ).bind (fun S =>
        Clafer.Constraints.universal S (fun x => (interpret s body ha).denote (extend s o hv) (ρ.push (binder s b) x)))
    rw [ihd hd hn.1 hod ρ hρ,hS,Option.bind_some]
    exact universal_on_congr S _ _ (fun x hx =>
      ihbody ha hn.2 hoa (ρ.push (binder s b) x) (recorded_push hρ b (hrec hx)))
  | located span a ih => exact ih ht.2 hn ho ρ hρ

end ClaferCompiler.Correctness.Pipeline
