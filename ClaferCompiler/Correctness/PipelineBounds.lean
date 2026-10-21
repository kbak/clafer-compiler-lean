module

public import ClaferCompiler.Correctness.PipelineObservation

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionRelations ExpressionMeaning

theorem primitive_ancestors (v : IR.Inherited.Validated n) (d e : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) :
    ((SemanticsBridge.Inherited.interpret v.core).toEffectiveCore.Ancestor d e → e = d) ∧
    ((SemanticsBridge.Inherited.interpret v.core).toEffectiveCore.Ancestor e d → e = d) := by
  constructor
  · intro h
    rcases h.cases_head with he | ⟨c,hc,_⟩
    · exact he.symm
    · have hh := (v.selectedChecked.2.2.2.2.2.2.2.1 d hd).2.2
      change (v.core.structural.get d).super = some c at hc
      rw [hh] at hc
      cases hc
  · intro h
    rcases h.cases_tail with he | ⟨c,_,hc⟩
    · exact he.symm
    · change (v.core.structural.get c).super = some d at hc
      have ha := (v.selectedChecked.2.2.1 c d hc).1
      rw [primitive_explicit_false v d hd] at ha
      cases ha

/-- Ordinary object identity cannot be confused with an integer payload: target
sibling disjointness and the selected primitive's inheritance shape enforce it. -/
theorem decoded_nonprimitive (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (d : Fin p.prepared.resolved.count)
    (hd : (p.validated.core.structural.get d).origin ≠ .integer) (a : Nat)
    (ha : a ∈ i.signatures[Structural.signatureId p.validated.layout d]?.getD []) :
    decodeAtom (scalarRows p.validated i) a = .object a := by
  apply atom_object
  intro z hz
  by_cases hp : ∃ e, (p.validated.core.structural.get e).origin = .integer
  · obtain ⟨e,he⟩ := hp
    have hr : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout e]?.getD [] := by
      simp [scalarRows, scalarIds_singleton p.validated e he]
    rw [hr] at hz
    have ht := ((scalar_rows p i hs e he).1 (a,z) hz).1
    obtain ⟨o,_,hroot,⟨rep⟩,hsource⟩ := observed_structure p i hs
    let x := rep.objects.symm ⟨a, signature_live i rep.live _ a ha⟩
    have hx : (rep.objects x).val = a := by simp [x]
    have hx1 := (rep.heads d x).mpr (by simpa only [hx] using ha)
    have hx2 := (rep.heads e x).mpr (by simpa only [hx] using ht)
    have hab := hsource.2.2.2.2.2 d e x hx1 hx2
    have heq : d = e := hab.elim (primitive_ancestors p.validated e d he).2
      (primitive_ancestors p.validated e d he).1
    exact hd (heq ▸ he)
  · have hr : scalarRows p.validated i = [] := by
      simp [scalarRows, scalarIds_empty p.validated (by simpa using hp)]
    simp [hr] at hz

/-- Original-ID scope lookup agrees with the emitted target signature order. -/
theorem resolved_scope (v : IR.Structural.Layout n) (b : Structural.Bounds) (qs : List Scope)
    (h : Structural.resolveScopes v b = .ok qs) (d : Fin n) :
    ∃ row, b.declarations.find? (fun row => row.1 == (v.core.get d).id) = some row ∧
      qs[Structural.signatureId v d]? = some row.2 := by
  dsimp only [Structural.resolveScopes] at h
  split at h
  · simp [bind, Except.bind] at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i scopes hm
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst qs
      have hp := mapM_pairs _ _ hm
      have hidx := List.idxOf_lt_length_iff.mpr (Structural.mem_order v d)
      have hlen := hp.length_eq
      have he := (List.forall₂_iff_get.mp hp).2 ((Structural.order v).idxOf d) hidx (by omega)
      simp only [List.get_eq_getElem, List.getElem_idxOf hidx] at he
      cases hf : b.declarations.find? (fun row => row.1 == (v.core.get d).id) with
      | none => simp [hf] at he
      | some row =>
        have hval : row.2 = scopes[(Structural.order v).idxOf d] := by simpa [hf] using he
        refine ⟨row,rfl,?_⟩
        simp [Structural.signatureId, Nat.add_comm 1, hval]


theorem scope_size_bound (qs : List Scope) (i : Instance) (h : i.inScope qs = true)
    (k : Nat) (q : Scope) (hq : qs[k]? = some q) : (i.signatures[k]?.getD []).length ≤ q.size := by
  cases hx : i.signatures[k]? with
  | none => simp
  | some xs =>
    have hm : (q,xs) ∈ qs.zip i.signatures := List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hq,hx⟩)
    have hh := List.all_eq_true.mp h (q,xs) hm
    cases he : q.exact with
    | false => simpa [hx, he] using hh
    | true => have hlen : xs.length = q.size := by simpa [he] using hh
              simp [hlen]

def observationBounds (p : Driver.Source.Product) : IR.Expr.Bounds p.prepared.resolved.count :=
  sourceBounds p.validated (Driver.Source.targetBounds p.validated p.bounds) p.intervals

theorem target_extent_bound (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (d : Fin p.prepared.resolved.count) :
    (i.signatures[Structural.signatureId p.validated.layout d]?.getD []).length ≤
      (observationBounds p).extents[d] := by
  obtain ⟨base,hb,hbase⟩ := hs.structural
  obtain ⟨qs,hqs,hraw,_⟩ := Inherited.compile_output _ _ _ hb
  obtain ⟨row,hfind,hrow⟩ := resolved_scope p.validated.layout _ _ hqs d
  have hscope : i.inScope qs = true := by simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbase.2.2.2.2.1
  have hh := scope_size_bound qs i hscope _ row.2 hrow
  have hfind' : p.bounds.structural.declarations.find?
      (fun row => row.1 == (p.validated.core.structural.get d).id) = some row := by
    simpa only [Driver.Source.targetBounds, IR.Inherited.Validated.layout, IR.Inherited.layout_get] using hfind
  simpa [observationBounds, sourceBounds, Vector.get, Vector.ofFn, Driver.Source.targetBounds, hfind'] using hh

theorem target_width (p : Driver.Source.Product) :
    1 ≤ (observationBounds p).width ∧ (observationBounds p).width ≤ 16 := by
  have hb := p.encoded.module.bounded
  simp only [Module.safeBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
  simpa only [compiled_width p, observationBounds, sourceBounds, Driver.Source.targetBounds] using hb.1.1.1.1

/-- Scope and numeric range obligations are consequences of the structural and
scalar facts. Constraint truth is deliberately absent from this derivation. -/
theorem target_observation_bounded (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (root : Nat)
    (s : Support p.prepared.resolved.count m) (owner) (l)
    (hb : bindSupport p.validated s owner = .ok l) :
    (observe p.validated s (Structural.observation p.validated.layout i root)
      (scalarRows p.validated i)).withinBounds s (observationBounds p) = true := by
  obtain ⟨base,hbase,hbaseSat⟩ := hs.structural
  obtain ⟨scopes,_,hraw,_⟩ := Inherited.compile_output _ _ _ hbase
  have ht : i.declarations (Structural.schema p.validated.layout) = true := by
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbaseSat.2.2.2.1
  have hw : i.wellFormed (Structural.schema p.validated.layout) = true := by
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbaseSat.2.2.1
  let g := decodeAtom (scalarRows p.validated i)
  have hg := decoded_atoms_injective p i hs
  have hflags := bound_support_flags _ _ _ _ hb
  have hmaps := (bound_layout_data _ _ _ _ hb).2
  simp only [Observation.withinBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨target_width p, ?_⟩, ?_⟩
  · intro x _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro y _
      by_cases he : s.classes[x] = s.classes[y]
      · have hxy : x = y := p.validated.coreChecked.1 x y (by
          rw [← (hflags x).1, ← (hflags y).1]; exact he)
        subst y
        simp
      · rw [Bool.or_eq_true]
        exact Or.inl (by simpa only [bne_iff_ne] using he)
    · simp only [observe_objects, Structural.observation]
      rw [ eraseDups_of_nodup ((signature_nodup _ i hw _).map hg), List.length_map]
      exact target_extent_bound p i hs x
    · intro a ha
      rw [observe_objects] at ha
      obtain ⟨b,hb',rfl⟩ := List.mem_map.mp ha
      by_cases hi : (p.validated.core.structural.get x).origin = .integer
      · have hflag : s.integer[x] = true := by rw [(hflags x).2]; exact decide_eq_true hi
        obtain ⟨htyped,hkeys,hall,_⟩ := scalar_rows p i hs x hi
        obtain ⟨z,hz⟩ := hall b hb'
        have he : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout x]?.getD [] := by
          simp [scalarRows, scalarIds_singleton p.validated x hi]
        have hd : decodeAtom (scalarRows p.validated i) b = .integer z := by
          rw [he]; exact (atom_integer _ hkeys b z).mpr hz
        obtain ⟨base,_,_,hn,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
        have hfit := (numericFacts_member _ _ _ _ hn x hi).1
        have hrange := (htyped (b,z) hz).2
        rw [hd]
        rw [hflag]
        change (true && p.intervals[x].fits p.bounds.structural.bitwidth &&
          decide (p.intervals[x].lower ≤ z ∧ z ≤ p.intervals[x].upper)) = true
        simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by simpa only [Driver.Source.targetBounds] using hfit, hrange⟩
      · rw [decoded_nonprimitive p i hs x hi b hb']
        rw [(hflags x).2]
        simp [hi]
  · intro e _ link hlink
    rw [observe_links] at hlink
    have hm : (link.source,link.target) ∈ observedRelation
        (observeMap p.validated (Structural.observation p.validated.layout i root) g s.maps[e]) :=
      ⟨link,hlink,rfl,rfl⟩
    obtain ⟨a,b,hab,ha,hb'⟩ := (observed_links_iff _ _ _ _).mp hm
    have he := original_pairs_typed p.validated i root s.maps[e] l.maps[e] (hmaps e) ht a b hab
    simp only [List.contains_iff_mem, observe_objects]
    exact ⟨List.mem_map.mpr ⟨a,he.1,ha⟩, List.mem_map.mpr ⟨b,he.2,hb'⟩⟩

end ClaferCompiler.Correctness.Pipeline
