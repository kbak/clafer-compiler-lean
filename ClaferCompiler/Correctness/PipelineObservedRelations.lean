module

public import ClaferCompiler.Correctness.PipelineFullRelations
public import ClaferCompiler.Correctness.PipelineLayout

@[expose] public section
/-! Observed relation equations contain data only, including the distinct
intermediate reference occurrence in target composition.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr Frontend.Constraints SemanticsBridge.Expr Backend.Alloy Backend.Alloy.Expressions

structure ObservationLive (o : Structural.Observation n) : Prop where
  heads : ∀ d x, x ∈ o.heads d → x ∈ o.objects
  containment : ∀ d x y, (x,y) ∈ o.containment d → x ∈ o.objects ∧ y ∈ o.objects
  dereference : ∀ d x y, (x,y) ∈ o.dereference d → x ∈ o.objects ∧ y ∈ o.objects

theorem originalPairs_owner (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (o : Structural.Observation n) (e : Fin m) :
    originalPairs v o s.maps[e] =
      match s.maps[e].kind with
      | .head => o.containment (mapOwner resolved e)
      | .parent => (o.containment (mapOwner resolved e)).map Prod.swap
      | .dereference => o.dereference (mapOwner resolved e)
      | .inclusion => (o.heads (mapOwner resolved e)).map fun a => (a,a)
      | .target => (o.containment (mapOwner resolved e)).flatMap fun (a,h) =>
        ((o.dereference (mapOwner resolved e)).filter fun row => row.1 == h).map fun (_,b) => (a,b) := by
  have hid := (mapOwner_resolved resolved e).1
  unfold originalPairs
  cases hf : (List.finRange n).find? (fun d => (v.core.structural.get d).id == s.maps[e].owner) with
  | none =>
    have hh := (List.find?_eq_none.mp hf) (mapOwner resolved e) (List.mem_finRange _)
    simp only [← hid,beq_self_eq_true] at hh
    contradiction
  | some d =>
    have hh : (v.core.structural.get d).id = s.maps[e].owner := by simpa using List.find?_some hf
    have he : d = mapOwner resolved e := v.coreChecked.1 d _ (hh.trans hid)
    subst d
    rfl

theorem originalPairs_live (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (o : Structural.Observation n)
    (live : ObservationLive o) (e : Fin m) (a b : Nat)
    (h : (a,b) ∈ originalPairs v o s.maps[e]) : a ∈ o.objects ∧ b ∈ o.objects := by
  rw [originalPairs_owner v s resolved o e] at h
  cases hk : s.maps[e].kind <;> simp only [hk] at h
  · exact live.containment _ _ _ h
  · obtain ⟨⟨x,y⟩,hxy,he⟩ := List.mem_map.mp h
    cases he
    exact (live.containment _ _ _ hxy).symm
  · exact live.dereference _ _ _ h
  · obtain ⟨⟨x,y⟩,hxy,hrest⟩ := List.mem_flatMap.mp h
    obtain ⟨⟨z,t⟩,hzt,he⟩ := List.mem_map.mp hrest
    cases he
    exact ⟨(live.containment _ _ _ hxy).1,(live.dereference _ _ _ (List.mem_filter.mp hzt).1).2⟩
  · obtain ⟨x,hx,he⟩ := List.mem_map.mp h
    cases he
    exact ⟨live.heads _ _ hx,live.heads _ _ hx⟩

theorem originalPairs_source (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (o : Structural.Observation n)
    (root : o.root ∈ o.objects) (live : ObservationLive o)
    (e : Fin m) (x y : Structural.Objects o) :
    sourceRelation resolved (Structural.realize o root) e x y ↔
      (x.val,y.val) ∈ originalPairs v o s.maps[e] := by
  rw [originalPairs_owner v s resolved o e]
  have hr := (mapOwner_resolved resolved e).2
  cases hk : s.maps[e].kind <;> simp only [hk] at hr
  · simp only [sourceRelation,hk,Structural.realize,hr.2]
  · simp only [sourceRelation,hk,Structural.realize,hr.1,List.mem_map]
    constructor
    · intro h; exact ⟨(y.val,x.val),h,rfl⟩
    · rintro ⟨⟨a,b⟩,h,he⟩
      cases he
      exact h
  · simp only [sourceRelation,hk,Structural.realize,hr.1]
  · simp only [sourceRelation,hk,Structural.realize,List.mem_flatMap,List.mem_map,List.mem_filter,
      beq_iff_eq]
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨(x.val,z.val),hxz,(z.val,y.val),⟨hzy,rfl⟩,rfl⟩
    · rintro ⟨⟨a,b⟩,hab,⟨c,d⟩,⟨hcd,hcb⟩,he⟩
      cases he
      have hcb : c = b := hcb
      subst c
      exact ⟨⟨b,(live.containment _ _ _ hab).2⟩,hab,hcd⟩
  · simp only [sourceRelation,hk,Structural.realize,hr.1,Set.mem_ofPred_eq,List.mem_map]
    constructor
    · rintro ⟨hx,rfl⟩; exact ⟨x.val,hx,rfl⟩
    · rintro ⟨a,ha,he⟩
      have hx : a = x.val := congrArg Prod.fst he
      have hy : a = y.val := congrArg Prod.snd he
      exact ⟨hx ▸ ha,Subtype.ext (hx.symm.trans hy)⟩

theorem observed_relation_source (v : IR.Inherited.Validated n) (s : Support n m)
    (resolved : Resolved v.core.structural s) (o : Structural.Observation n)
    (root : o.root ∈ o.objects) (live : ObservationLive o)
    (rows : List (Nat × Int)) (g : Structural.Objects o ↪ Atom)
    (labels : ∀ x, g x = decodeAtom rows x.val) (e : Fin m) (a b : Atom) :
    (a,b) ∈ observedRelation (observe v s o rows).links[e] ↔
      ∃ x y, sourceRelation resolved (Structural.realize o root) e x y ∧ g x = a ∧ g y = b := by
  rw [observe_links,observeMap,observed_links_iff]
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    have hh := originalPairs_live v s resolved o live e x y hxy
    refine ⟨⟨x,hh.1⟩,⟨y,hh.2⟩,?_,?_,?_⟩
    · exact (originalPairs_source v s resolved o root live e _ _).mpr hxy
    · exact (labels _).trans hx
    · exact (labels _).trans hy
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    exact ⟨x.val,y.val,(originalPairs_source v s resolved o root live e x y).mp hxy,
      (labels x).symm,(labels y).symm⟩

theorem observed_objects_source (v : IR.Inherited.Validated n) (s : Support n m)
    (o : Structural.Observation n) (root : o.root ∈ o.objects) (live : ObservationLive o)
    (rows : List (Nat × Int)) (g : Structural.Objects o ↪ Atom)
    (labels : ∀ x, g x = decodeAtom rows x.val) (d : Fin n) :
    atomSet (observe v s o rows).objects[d] = g '' (Structural.realize o root).head d := by
  rw [observe_objects]
  ext a
  simp only [atomSet,Set.mem_ofPred_eq,List.mem_map]
  constructor
  · rintro ⟨x,hx,hxa⟩
    exact ⟨⟨x,live.heads d x hx⟩,hx,(labels _).trans hxa⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,(labels _).symm⟩

end ClaferCompiler.Correctness.Pipeline
