module

public import ClaferCompiler.SemanticsBridge.Inherited
public import ClaferCompiler.SemanticsBridge.ExprObservation
public import ClaferCompiler.Frontend.ConstraintsSupport

@[expose] public section
/-! Full support bindings reuse semantic relation spans and pullback composition.
Composite target links retain both original occurrences.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr SemanticsBridge.Expr Frontend.Constraints
open Clafer.Semantics CategoryTheory DPGraph DPGraph.Predicates

noncomputable def mapOwner {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (e : Fin m) : Fin n := Classical.choose (resolved.2.2 e)

theorem mapOwner_resolved {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (e : Fin m) :
    s.maps[e].owner = (c.get (mapOwner resolved e)).id ∧
      (match s.maps[e].kind with
       | .head => (c.get (mapOwner resolved e)).parent = some s.maps[e].source ∧
           mapOwner resolved e = s.maps[e].target
       | .parent => mapOwner resolved e = s.maps[e].source ∧
           (c.get (mapOwner resolved e)).parent = some s.maps[e].target
       | .dereference => mapOwner resolved e = s.maps[e].source ∧
           (c.get (mapOwner resolved e)).reference.target = some s.maps[e].target
       | .inclusion => mapOwner resolved e = s.maps[e].source ∧
           (c.get (mapOwner resolved e)).super = some s.maps[e].target
       | .target => (c.get (mapOwner resolved e)).parent = some s.maps[e].source ∧
           (c.get (mapOwner resolved e)).reference.target = some s.maps[e].target) :=
  Classical.choose_spec (resolved.2.2 e)

noncomputable def fullSpan {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (state : Configuration (Fin n) Atom) (e : Fin m) :
    Span (state.head s.maps[e].source) (state.head s.maps[e].target) :=
  match s.maps[e].kind with
  | .head => Span.ofRelation (fun a b => state.contains s.maps[e].target a.val b.val)
  | .parent => Span.ofRelation (fun a b => state.contains s.maps[e].source b.val a.val)
  | .dereference => Span.ofRelation (fun a b => state.deref s.maps[e].source a.val b.val)
  | .inclusion => Span.ofRelation (fun a b => a.val = b.val)
  | .target =>
    (Span.ofRelation (fun (a : state.head s.maps[e].source) (b : state.head (mapOwner resolved e)) =>
      state.contains (mapOwner resolved e) a.val b.val)).comp
    (Span.ofRelation (fun (a : state.head (mapOwner resolved e)) (b : state.head s.maps[e].target) =>
      state.deref (mapOwner resolved e) a.val b.val))

noncomputable def fullSupportModel {c : IR.Structural.Core n} {s : Support n m}
    (resolved : Resolved c s) (state : Configuration (Fin n) Atom) :
    (support s).graph ⥤q semanticGraph.{0,0} Atom where
  obj := state.head
  map := by
    rintro a b ⟨e,hs,ht⟩
    subst a; subst b
    exact fullSpan resolved state e

noncomputable def fullBinding (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (state : Configuration (Fin n) Atom)
    (hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core) state)
    (R : FormalCD.IntegerRealization Atom)
    (primitives : ∀ d, (v.core.structural.get d).origin = .integer → state.head d = R.domain) :
    Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom where
  realization := R
  model := fullSupportModel resolved state
  same_id := by
    intro x y he
    have hi : s.classes[x] = s.classes[y] := congrArg Clafer.DeclId.value he
    rw [resolved.1 x,resolved.1 y] at hi
    exact congrArg state.head (v.coreChecked.1 x y hi)
  inclusion := by
    intro e he
    have hk : s.maps[e].kind = .inclusion := by
      change mapKind s.maps[e].kind = .inclusion at he
      cases hkind : s.maps[e].kind <;> simp_all [mapKind]
    change Inclusion (fullSpan resolved state e)
    rw [fullSpan,hk]
    apply (identity_inclusion_iff _ _).mpr
    have hr := (mapOwner_resolved resolved e).2
    simp only [hk] at hr
    apply hs.2.2.1.1
    change (v.core.structural.get s.maps[e].source).super = some s.maps[e].target
    exact hr.1 ▸ hr.2
  integer_domain := by
    intro x hx
    change s.integer[x] = true at hx
    rw [resolved.2.1 x] at hx
    exact primitives x (of_decide_eq_true hx)

/-- The full model has the original structural extents, not their truncated
primitive observations. -/
theorem fullBinding_head (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (state : Configuration (Fin n) Atom)
    (hs : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret v.core) state)
    (R : FormalCD.IntegerRealization Atom) (primitives) (x : Fin n) :
    (fullBinding v s resolved state hs R primitives).model.obj x = state.head x := rfl

end ClaferCompiler.Correctness.Pipeline
