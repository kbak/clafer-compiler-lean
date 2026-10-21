module

public import ClaferCompiler.Correctness.PipelineLayout

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionRelations ExpressionMeaning

theorem original_pairs_typed (v : IR.Inherited.Validated n) (i : Instance)
    (root : Nat) (e : MapRef n) (r : Rel) (hb : bindMap v e = .ok r)
    (ht : i.declarations (Structural.schema v.layout) = true) (a b : Nat)
    (hm : (a,b) ∈ originalPairs v (Structural.observation v.layout i root) e) :
    a ∈ i.signatures[Structural.signatureId v.layout e.source]?.getD [] ∧
    b ∈ i.signatures[Structural.signatureId v.layout e.target]?.getD [] := by
  have hc (d p : Fin n) (hp : (v.core.structural.get d).parent = some p) (x y : Nat)
      (hm : (x,y) ∈ (Structural.observation v.layout i root).containment d) :
      x ∈ i.signatures[Structural.signatureId v.layout p]?.getD [] ∧
      y ∈ i.signatures[Structural.signatureId v.layout d]?.getD [] := by
    have hp' : (v.layout.core.get d).parent = some p := by
      simpa [IR.Inherited.Validated.layout] using hp
    simp only [Structural.observation, hp', Option.bind_some] at hm
    exact Structural.field_typed _ i ht _ _ (Structural.containment_direction v.layout d p hp')
      x y ((Structural.mem_readPairs _ _ _).mp hm)
  have hd (d p : Fin n) (hp : (v.core.structural.get d).reference.target = some p) (x y : Nat)
      (hm : (x,y) ∈ (Structural.observation v.layout i root).dereference d) :
      x ∈ i.signatures[Structural.signatureId v.layout d]?.getD [] ∧
      y ∈ i.signatures[Structural.signatureId v.layout p]?.getD [] := by
    have hp' : (v.layout.core.get d).reference.target = some p := by
      simpa [IR.Inherited.Validated.layout] using hp
    simp only [Structural.observation, hp', Option.bind_some] at hm
    exact Structural.field_typed _ i ht _ _ (Structural.dereference_direction v.layout d p hp')
      x y ((Structural.mem_readPairs _ _ _).mp hm)
  cases hf : (List.finRange n).find? (fun d => (v.core.structural.get d).id == e.owner) with
  | none => cases e.kind <;> simp [bindMap, hf] at hb
  | some d =>
    cases hk : e.kind <;> simp only [bindMap, hf, hk] at hb
    all_goals split at hb
    all_goals try { simp_all [bind, Except.bind] }
    all_goals rename_i hg
    all_goals simp only [Bool.or_eq_true, not_or, bne_iff_ne, not_not] at hg
    all_goals simp only [originalPairs, hf, hk] at hm
    · simpa only [hg.2] using hc d e.source hg.1 a b hm
    · obtain ⟨⟨x,y⟩,hpair,he⟩ := List.mem_map.mp hm
      cases he
      simpa only [hg.1] using (hc d e.target hg.2 x y hpair).symm
    · simpa only [hg.1] using hd d e.target hg.2 a b hm
    · obtain ⟨⟨x,y⟩,hpair,hr⟩ := List.mem_flatMap.mp hm
      obtain ⟨⟨z,t⟩,hd',he⟩ := List.mem_map.mp hr
      cases he
      exact ⟨(hc d e.source hg.1 x y hpair).1,
        (hd d e.target hg.2 z t (List.mem_filter.mp hd').1).2⟩
    · obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
      cases he
      refine ⟨by simpa only [hg.1, Structural.observation] using hx, ?_⟩
      exact Structural.declaration_included _ i ht _ _ _
        (Structural.schema_signature v.layout d)
        (by simp [IR.Inherited.Validated.layout, hg.2]) _ hx

/-- Each observed primitive object decodes to an actual mathematical integer. -/
theorem observed_member_full (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (root : Nat) (s : Support p.prepared.resolved.count m)
    (owner) (l) (hb : bindSupport p.validated s owner = .ok l)
    (d : Fin p.prepared.resolved.count) (a : Nat)
    (ha : a ∈ i.signatures[Structural.signatureId p.validated.layout d]?.getD []) :
    decodeAtom (scalarRows p.validated i) a ∈ fullExtent s
      (observe p.validated s (Structural.observation p.validated.layout i root) (scalarRows p.validated i)) d := by
  cases hi : s.integer[d] with
  | false =>
    simp only [fullExtent, hi, Bool.false_eq_true, ↓reduceIte]
    simpa [observe, Vector.get, Vector.ofFn, Structural.observation, atomSet] using
      List.mem_map.mpr ⟨a,ha,rfl⟩
  | true =>
    have hd : (p.validated.core.structural.get d).origin = .integer := by
      simpa only [(bound_support_flags _ _ _ _ hb d).2, decide_eq_true_eq] using hi
    obtain ⟨_,hk,hall,_⟩ := scalar_rows p i hs d hd
    obtain ⟨z,hz⟩ := hall a ha
    have he : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
      simp [scalarRows, scalarIds_singleton p.validated d hd]
    have hg : decodeAtom (scalarRows p.validated i) a = .integer z := by
      rw [he]
      exact (atom_integer _ hk a z).mpr hz
    simp only [fullExtent, hi, ↓reduceIte, hg, FormalCD.IntegerRealization.domain,
      Set.mem_range, integers]
    exact ⟨z,rfl⟩


theorem signature_nodup (schema : Schema) (i : Instance)
    (hw : i.wellFormed schema = true) (k : Nat) : (i.signatures[k]?.getD []).Nodup := by
  apply List.Nodup.of_map (fun x : Nat => [x])
  apply List.nodup_iff_length_dedup_eq.mpr
  rw [← List.card_toFinset, ← Structural.eraseDups_card, Structural.extent_card schema i hw]
  simp

theorem inclusion_pairs (v : IR.Inherited.Validated n) (o : Structural.Observation n)
    (e : MapRef n) (r : Rel) (hb : bindMap v e = .ok r) (hk : e.kind = .inclusion) :
    originalPairs v o e = (o.heads e.source).map (fun a => (a,a)) ∧
      (v.core.structural.get e.source).super = some e.target := by
  cases hf : (List.finRange n).find? (fun d => (v.core.structural.get d).id == e.owner) with
  | none => simp [bindMap, hf] at hb
  | some d =>
    simp only [bindMap, hf, hk] at hb
    split at hb
    · simp [bind, Except.bind] at hb
    · rename_i hg
      simp only [Bool.or_eq_true, not_or, bne_iff_ne, not_not] at hg
      exact ⟨by simp only [originalPairs, hf, hk, hg.1], hg.1 ▸ hg.2⟩

theorem diagonal_sources (g : Nat → Atom) (xs : List Nat) :
    (observeLinks g (xs.map fun a => (a,a))).map Link.source = xs.map g := by
  have h := congrArg (List.map (fun p : Nat × Nat => g p.1))
    (List.zipIdx_map_fst 0 (xs.map fun a => (a,a)))
  simpa only [observeLinks, List.map_map, Function.comp_def] using h

/-- Actual successful compilation supplies a well-typed finite observation for
all original maps. Infinite primitive extents enter only at `fullExtent`. -/
theorem target_observation_valid (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (root : Nat)
    (s : Support p.prepared.resolved.count m) (owner) (l)
    (hb : bindSupport p.validated s owner = .ok l) :
    ObservationValid s (observe p.validated s
      (Structural.observation p.validated.layout i root) (scalarRows p.validated i)) := by
  obtain ⟨base,hbase,hbaseSat⟩ := hs.structural
  obtain ⟨scopes,_,hraw,_⟩ := Inherited.compile_output _ _ _ hbase
  have ht : i.declarations (Structural.schema p.validated.layout) = true := by
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbaseSat.2.2.2.1
  have hw : i.wellFormed (Structural.schema p.validated.layout) = true := by
    simpa only [hraw, Backend.Alloy.Inherited.target, Structural.target] using hbaseSat.2.2.1
  let o := Structural.observation p.validated.layout i root
  let g := decodeAtom (scalarRows p.validated i)
  have hg := decoded_atoms_injective p i hs
  have hmaps := (bound_layout_data _ _ _ _ hb).2
  have hflags := bound_support_flags _ _ _ _ hb
  have hinclusion (e : Fin m) (hk : s.maps[e].kind = .inclusion) :
      s.integer[s.maps[e].source] = false := by
    have hs := (inclusion_pairs p.validated o _ _ (hmaps e) hk).2
    have hn : (p.validated.core.structural.get s.maps[e].source).origin ≠ .integer := by
      intro hprim
      have hh := (p.validated.selectedChecked.2.2.2.2.2.2.2.1 _ hprim).2.2
      rw [hs] at hh
      cases hh
    rw [(hflags _).2]
    exact decide_eq_false hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [observe_links]
  · intro x y hxy
    have he : x = y := p.validated.coreChecked.1 x y (by
      rw [← (hflags x).1, ← (hflags y).1]; exact hxy)
    subst y
    rfl
  · intro e link hlink
    have hm : (link.source,link.target) ∈ observedRelation (observeMap p.validated o g s.maps[e]) :=
      ⟨link,hlink,rfl,rfl⟩
    obtain ⟨a,b,hab,ha,hb'⟩ := (observed_links_iff _ _ _ _).mp hm
    have he := original_pairs_typed p.validated i root s.maps[e] l.maps[e] (hmaps e) ht a b hab
    exact ⟨ha ▸ observed_member_full p i hs root s owner l hb _ a he.1,
      hb' ▸ observed_member_full p i hs root s owner l hb _ b he.2⟩
  · intro e
    exact observed_links_ids g (originalPairs p.validated o s.maps[e])
  · intro e f ho hk link
    change link ∈ observeMap p.validated o g s.maps[e] ↔ link ∈ observeMap p.validated o g s.maps[f]
    simp only [observeMap, originalPairs, ho, hk]
  · intro e hk a ha
    have hp := (inclusion_pairs p.validated o _ _ (hmaps e) hk).1
    have hfinite : a ∈ (o.heads s.maps[e].source).map g := by
      simp only [fullExtent, hinclusion e hk, Bool.false_eq_true, ↓reduceIte] at ha
      simpa only [observe_objects, atomSet, Set.mem_ofPred_eq] using ha
    obtain ⟨x,hx,hxa⟩ := List.mem_map.mp hfinite
    have hm : (a,a) ∈ observedRelation (observeLinks g (originalPairs p.validated o s.maps[e])) :=
      (observed_links_iff _ _ _ _).mpr ⟨x,x,by rw [hp]; exact List.mem_map.mpr ⟨x,hx,rfl⟩,hxa,hxa⟩
    obtain ⟨link,hlink,hl,_⟩ := hm
    refine ⟨link,⟨hlink,hl⟩,?_⟩
    rintro other ⟨hother,ho⟩
    have hn : ((observeLinks g (originalPairs p.validated o s.maps[e])).map Link.source).Nodup := by
      rw [hp, diagonal_sources]
      exact (signature_nodup _ i hw _).map hg
    exact List.inj_on_of_nodup_map hn hother hlink (ho.trans hl.symm)
  · intro e hk link hm
    have hp := (inclusion_pairs p.validated o _ _ (hmaps e) hk).1
    have hr : (link.source,link.target) ∈ observedRelation (observeLinks g (originalPairs p.validated o s.maps[e])) :=
      ⟨link,hm,rfl,rfl⟩
    obtain ⟨a,b,hab,ha,hb'⟩ := (observed_links_iff _ _ _ _).mp hr
    rw [hp] at hab
    obtain ⟨x,_,he⟩ := List.mem_map.mp hab
    cases he
    exact hb'.symm.trans ha

end ClaferCompiler.Correctness.Pipeline
