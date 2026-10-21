module

public import ClaferCompiler.Correctness.PipelineScalars

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr
open SemanticsBridge.Expr ExpressionRelations ExpressionMeaning

@[simp] theorem observe_objects (v : IR.Inherited.Validated n) (s : Support n m)
    (o : Structural.Observation n) (rows) (d : Fin n) :
    (observe v s o rows).objects[d] = (o.heads d).map (decodeAtom rows) := by
  simp [observe, Vector.ofFn]

@[simp] theorem observe_links (v : IR.Inherited.Validated n) (s : Support n m)
    (o : Structural.Observation n) (rows) (e : Fin m) :
    (observe v s o rows).links[e] = observeMap v o (decodeAtom rows) s.maps[e] := by
  simp [observe, Vector.ofFn]

/-- Successful binding records each original map, not merely a well-formed
layout of the right length. -/
theorem bound_layout_data (v : IR.Inherited.Validated n) (s : Support n m)
    (owner : Fin n) (l : Layout n m) (h : bindSupport v s owner = .ok l) :
    l.scalarOwners = Vector.ofFn (Structural.signatureId v.layout) ∧
    (∀ e : Fin m, bindMap v s.maps[e] = .ok l.maps[e]) := by
  dsimp only [bindSupport] at h
  split at h
  · simp [bind, Except.bind] at h
  · cases hm : (List.finRange m).mapM (fun edge => bindMap v (s.maps.get edge)) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok maps =>
      simp only [hm, bind, Except.bind] at h
      split at h
      · rename_i hlen
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst l
        refine ⟨rfl, ?_⟩
        intro e
        have hp := mapM_pairs _ _ hm
        have he := (List.forall₂_iff_get.mp hp).2 e.val (by simp [e.isLt]) (by omega)
        simpa [List.get_eq_getElem, Vector.get] using he
      · cases h

theorem observed_links_iff (g : Nat → Atom) (pairs : List (Nat × Nat)) (x y : Atom) :
    (x, y) ∈ observedRelation (observeLinks g pairs) ↔
      ∃ a b, (a, b) ∈ pairs ∧ g a = x ∧ g b = y := by
  simp only [observedRelation, Set.mem_ofPred_eq, observeLinks, List.mem_map]
  constructor
  · rintro ⟨l, ⟨⟨⟨a,b⟩,k⟩, hm, rfl⟩, hx, hy⟩
    exact ⟨a, b, List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hm), hx, hy⟩
  · rintro ⟨a,b,hm,hx,hy⟩
    obtain ⟨k,hlt,hk⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨k,g a,g b⟩, ⟨((a,b),k), ?_, rfl⟩, hx, hy⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨_, hk⟩)

/-- The decoder gives each original occurrence a distinct ID even when endpoints
coincide. The reduction below forgets IDs only where set meaning requires it. -/
theorem observed_links_ids (g : Nat → Atom) (pairs : List (Nat × Nat)) :
    ((observeLinks g pairs).map Link.id).Nodup := by
  simp only [observeLinks, List.map_map]
  change (pairs.zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem decoded_unary (xs live : List Nat) (g : Nat → Atom) (f : Atom → Nat)
    (hl : ∀ a ∈ xs, a ∈ live) (hf : ∀ a ∈ live, f (g a) = a) :
    Unary f (atomSet (xs.map g)) (xs.map fun a => [a]) := by
  intro t
  simp only [List.mem_map, atomSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨g a, ⟨a,ha,rfl⟩, by rw [hf a (hl a ha)]⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,by rw [hf a (hl a ha)]⟩

theorem decoded_binary (pairs : List (Nat × Nat)) (r : Relation) (live : List Nat)
    (g : Nat → Atom) (f : Atom → Nat)
    (hr : ∀ t, t ∈ r ↔ ∃ a b, (a,b) ∈ pairs ∧ t = [a,b])
    (hl : ∀ a b, (a,b) ∈ pairs → a ∈ live ∧ b ∈ live)
    (hf : ∀ a ∈ live, f (g a) = a) :
    Binary f (observedRelation (observeLinks g pairs)) r := by
  intro t
  rw [hr]
  constructor
  · rintro ⟨a,b,hm,rfl⟩
    exact ⟨g a,g b,(observed_links_iff _ _ _ _).mpr ⟨a,b,hm,rfl,rfl⟩,
      by rw [hf a (hl a b hm).1, hf b (hl a b hm).2]⟩
  · rintro ⟨x,y,hm,rfl⟩
    obtain ⟨a,b,hpair,rfl,rfl⟩ := (observed_links_iff _ _ _ _).mp hm
    exact ⟨a,b,hpair,by rw [hf a (hl a b hpair).1, hf b (hl a b hpair).2]⟩


theorem read_pairs_relation (ts : Relation)
    (h : ∀ t ∈ ts, ∃ a b, t = [a,b]) (t : Tuple) :
    t ∈ ts ↔ ∃ a b, (a,b) ∈ Structural.readPairs ts ∧ t = [a,b] := by
  constructor
  · intro ht
    obtain ⟨a,b,rfl⟩ := h t ht
    exact ⟨a,b,(Structural.mem_readPairs _ _ _).mpr ht,rfl⟩
  · rintro ⟨a,b,hm,rfl⟩
    exact (Structural.mem_readPairs _ _ _).mp hm

/-- Original declaration-role observations have exactly the tuples of the bound
relation. This proof inspects binding and table data, never a constraint value. -/
theorem original_pairs_relation (v : IR.Inherited.Validated n) (i : Instance)
    (root : Nat) (e : MapRef n) (r : Rel) (hb : bindMap v e = .ok r)
    (hw : i.wellFormed (Structural.schema v.layout) = true) (env : List Nat) (t : Tuple) :
    t ∈ r.eval i env ↔ ∃ a b,
      (a,b) ∈ originalPairs v (Structural.observation v.layout i root) e ∧ t = [a,b] := by
  cases hf : (List.finRange n).find? (fun d => (v.core.structural.get d).id == e.owner) with
  | none => cases e.kind <;> simp [bindMap, hf] at hb
  | some d =>
    cases hk : e.kind <;> simp only [bindMap, hf, hk] at hb
    all_goals split at hb
    all_goals try { simp_all [bind, Except.bind] }
    all_goals simp only [pure, Except.pure, Except.ok.injEq] at hb
    all_goals subst r
    all_goals rename_i hg
    all_goals simp only [Bool.or_eq_true, not_or, bne_iff_ne, not_not] at hg
    · simp only [originalPairs, hf, hk, Structural.observation, IR.Inherited.Validated.layout, IR.Inherited.layout_get,
        hg.1, Option.bind_some, Structural.contains, Rel.eval_field]
      exact read_pairs_relation _ (Structural.field_binary _ _ hw _) t
    · simp only [originalPairs, hf, hk, Structural.observation, IR.Inherited.Validated.layout, IR.Inherited.layout_get,
        hg.2, Option.bind_some]
      unfold Structural.contains
      rw [Rel.eval_transpose (.field _)]
      simp only [List.mem_eraseDups, List.mem_map]
      constructor
      · rintro ⟨q,hq,he⟩
        obtain ⟨a,b,rfl⟩ := Structural.field_binary _ _ hw _ q hq
        exact ⟨b,a,⟨(a,b),(Structural.mem_readPairs _ _ _).mpr hq,rfl⟩,he.symm⟩
      · rintro ⟨a,b,⟨⟨x,y⟩,hm,he⟩,rfl⟩
        cases he
        exact ⟨[x,y],(Structural.mem_readPairs _ _ _).mp hm,rfl⟩
    · simp only [originalPairs, hf, hk, Structural.observation, IR.Inherited.Validated.layout, IR.Inherited.layout_get,
        hg.2, Option.bind_some, Structural.deref, Rel.eval_field]
      exact read_pairs_relation _ (Structural.field_binary _ _ hw _) t
    · simp only [originalPairs, hf, hk, Structural.observation, IR.Inherited.Validated.layout, IR.Inherited.layout_get,
        hg.1, hg.2, Option.bind_some]
      unfold Structural.contains Structural.deref
      rw [Rel.eval_join (.field _) (.field _)]
      simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_filter]
      constructor
      · rintro ⟨q,hq,z,⟨hz,hh⟩,he⟩
        obtain ⟨a,b,rfl⟩ := Structural.field_binary _ _ hw _ q hq
        obtain ⟨c,d,rfl⟩ := Structural.field_binary _ _ hw _ z hz
        have hbc : b = c := by simpa using hh
        subst c
        exact ⟨a,d,⟨(a,b),(Structural.mem_readPairs _ _ _).mpr hq,
          (b,d),⟨(Structural.mem_readPairs _ _ _).mpr hz,by simp⟩,rfl⟩,by simpa using he.symm⟩
      · rintro ⟨a,b,⟨⟨p,h⟩,hc,⟨x,y⟩,⟨hd,he⟩,hp⟩,rfl⟩
        have hxh : x = h := by simpa using he
        cases hp
        subst x
        exact ⟨[p,h],(Structural.mem_readPairs _ _ _).mp hc,
          [h,y],⟨(Structural.mem_readPairs _ _ _).mp hd,by simp⟩,by simp⟩
    · simp only [originalPairs, hf, hk, Structural.observation]
      change t ∈ (((i.signatures[Structural.signatureId v.layout d]?.getD []).map
        fun a => [a]).filterMap (fun q => match q with
          | [a] => some [a,a] | _ => none)).eraseDups ↔ _
      simp [eq_comm]


theorem signature_live (i : Instance) (h : Structural.Live i) (k a : Nat)
    (ha : a ∈ i.signatures[k]?.getD []) : a ∈ i.signatures[0]?.getD [] := by
  cases hk : i.signatures[k]? with
  | none => simp [hk] at ha
  | some xs => exact h.1 xs (List.mem_of_getElem? hk) a (by simpa [hk] using ha)

theorem observation_pairs_live (v : IR.Inherited.Validated n) (i : Instance)
    (root : Nat) (e : MapRef n) (h : Structural.Live i) (a b : Nat)
    (hm : (a,b) ∈ originalPairs v (Structural.observation v.layout i root) e) :
    a ∈ i.signatures[0]?.getD [] ∧ b ∈ i.signatures[0]?.getD [] := by
  have contains (d : Fin n) (x y : Nat)
      (hm : (x,y) ∈ (Structural.observation v.layout i root).containment d) :
      x ∈ i.signatures[0]?.getD [] ∧ y ∈ i.signatures[0]?.getD [] := by
    simp only [Structural.observation] at hm
    cases hp : (v.layout.core.get d).parent with
    | none => simp [hp, Structural.readPairs] at hm
    | some p =>
      simp only [hp, Option.bind_some] at hm
      exact Structural.field_atom_live i h _ x y ((Structural.mem_readPairs _ _ _).mp hm)
  have deref (d : Fin n) (x y : Nat)
      (hm : (x,y) ∈ (Structural.observation v.layout i root).dereference d) :
      x ∈ i.signatures[0]?.getD [] ∧ y ∈ i.signatures[0]?.getD [] := by
    simp only [Structural.observation] at hm
    cases hp : (v.layout.core.get d).reference.target with
    | none => simp [hp, Structural.readPairs] at hm
    | some p =>
      simp only [hp, Option.bind_some] at hm
      exact Structural.field_atom_live i h _ x y ((Structural.mem_readPairs _ _ _).mp hm)
  unfold originalPairs at hm
  split at hm
  · simp at hm
  · rename_i d hd
    cases hk : e.kind <;> simp only [hk] at hm
    case head => exact contains d a b hm
    case parent =>
      obtain ⟨⟨x,y⟩,hp,he⟩ := List.mem_map.mp hm
      cases he
      exact (contains d x y hp).symm
    case dereference => exact deref d a b hm
    case inclusion =>
      obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
      cases he
      exact ⟨signature_live i h _ _ hx, signature_live i h _ _ hx⟩
    case target =>
      obtain ⟨⟨x,y⟩,hc,ht⟩ := List.mem_flatMap.mp hm
      obtain ⟨⟨z,t⟩,hd,he⟩ := List.mem_map.mp ht
      cases he
      exact ⟨(contains d x y hc).1, (deref d z t (List.mem_filter.mp hd).1).2⟩

/-- The finite leaf equations required by expression preservation are derived
from the actual binding and decoded target tables. No final truth is consulted. -/
theorem decoded_layout_relations (v : IR.Inherited.Validated n) (i : Instance)
    (root : Nat) (s : Support n m) (owner : Fin n) (l : Layout n m)
    (hb : bindSupport v s owner = .ok l)
    (hw : i.wellFormed (Structural.schema v.layout) = true) (hl : Structural.Live i)
    (g : Nat → Atom) (f : Atom → Nat)
    (hf : ∀ a ∈ i.signatures[0]?.getD [], f (g a) = a) :
    (∀ (x : Fin n) env, Unary f (atomSet ((Structural.observation v.layout i root).heads x |>.map g))
      (l.extents[x].eval i env)) ∧
    (∀ (e : Fin m) env, Binary f
      (observedRelation (observeMap v (Structural.observation v.layout i root) g s.maps[e]))
      (l.maps[e].eval i env)) := by
  have hext := (bindSupport_output v s owner l hb).2.2
  have hmap := (bound_layout_data v s owner l hb).2
  constructor
  · intro x env
    rw [hext]
    simpa [Structural.observation, Structural.head] using
      decoded_unary (i.signatures[Structural.signatureId v.layout x]?.getD []) _ g f
        (signature_live i hl _) hf
  · intro e env
    exact decoded_binary _ _ _ g f
      (original_pairs_relation v i root s.maps[e] l.maps[e] (hmap e) hw env)
      (observation_pairs_live v i root s.maps[e] hl) hf


theorem bound_support_flags (v : IR.Inherited.Validated n) (s : Support n m)
    (owner : Fin n) (l : Layout n m) (h : bindSupport v s owner = .ok l) :
    ∀ x : Fin n, s.classes[x] = (v.core.structural.get x).id ∧
      s.integer[x] = decide ((v.core.structural.get x).origin = .integer) := by
  dsimp only [bindSupport] at h
  split at h
  · simp [bind, Except.bind] at h
  · rename_i hg
    simp only [Bool.or_eq_true, not_or] at hg
    have hh : (List.finRange n).all (fun x => s.classes[x] == (v.core.structural.get x).id &&
      s.integer[x] == decide ((v.core.structural.get x).origin = .integer)) = true := by
      simpa using hg.2
    intro x
    simpa only [Bool.and_eq_true, beq_iff_eq] using List.all_eq_true.mp hh x (List.mem_finRange x)

/-- Scalar representation follows from generated scalar facts and actual decode
rows, including distinct values and totality on the observed primitive extent. -/
theorem decoded_scalar_rows (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) (hl : Structural.Live i)
    (d : Fin p.prepared.resolved.count) (hd : (p.validated.core.structural.get d).origin = .integer)
    (f : Atom → Nat)
    (hf : ∀ a ∈ i.signatures[0]?.getD [], f (decodeAtom (scalarRows p.validated i) a) = a) :
    ∀ row, row ∈ i.values[Structural.signatureId p.validated.layout d]?.getD [] ↔
      ∃ z, Atom.integer z ∈ (i.signatures[Structural.signatureId p.validated.layout d]?.getD []).map
        (decodeAtom (scalarRows p.validated i)) ∧ row = (f (.integer z), z) := by
  have he : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
    simp [scalarRows, scalarIds_singleton p.validated d hd]
  obtain ⟨ht,hk,_,_⟩ := scalar_rows p i hs d hd
  have hi (a : Nat) (z : Int) : decodeAtom (scalarRows p.validated i) a = .integer z ↔
      (a,z) ∈ i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
    rw [he]
    exact atom_integer _ hk a z
  intro row
  constructor
  · intro hr
    have ha := (ht row hr).1
    have hz := (hi row.1 row.2).mpr hr
    refine ⟨row.2, List.mem_map.mpr ⟨row.1, ha, hz⟩, ?_⟩
    have hf' := hf row.1 (signature_live i hl _ _ ha)
    rw [hz] at hf'
    exact Prod.ext hf'.symm rfl
  · rintro ⟨z,hm,rfl⟩
    obtain ⟨a,ha,hz⟩ := List.mem_map.mp hm
    have hf' := hf a (signature_live i hl _ _ ha)
    rw [hz] at hf'
    rw [hf']
    exact (hi a z).mp hz

/-- A satisfying source target constructs every expression leaf correspondence.
Neither a caller-supplied representation nor any source truth is a premise. -/
theorem target_layout_rep (p : Driver.Source.Product) (i : Instance)
    (hs : ObservationFacts p i) :
    ∃ f, Function.Injective f ∧ ∀ (root : Nat) {m} (s : Support p.prepared.resolved.count m)
      (owner : Fin p.prepared.resolved.count) (l : Layout p.prepared.resolved.count m),
      bindSupport p.validated s owner = .ok l →
      LayoutRep s l (observe p.validated s
        (Structural.observation p.validated.layout i root) (scalarRows p.validated i)) i f := by
  obtain ⟨o,ho,hr,⟨rep⟩,_⟩ := observed_structure p i hs
  obtain ⟨f,hfinj,hf⟩ := target_atom_encoding p i hs
  refine ⟨f,hfinj,?_⟩
  intro root m s owner l hb
  have hle := decoded_layout_relations p.validated i root s owner l hb rep.wellFormed rep.live
    (decodeAtom (scalarRows p.validated i)) f hf
  have hflags := bound_support_flags p.validated s owner l hb
  have howners := (bound_layout_data p.validated s owner l hb).1
  refine ⟨hfinj, ?_, ?_, ?_, ?_⟩
  · simpa [observe, Vector.get, Vector.ofFn] using hle.1
  · simpa [observe, Vector.get, Vector.ofFn] using hle.2
  · intro d hd env
    rw [howners]
    simpa [observe, Vector.get, Vector.ofFn, Structural.observation] using
      decoded_unary (i.signatures[Structural.signatureId p.validated.layout d]?.getD []) _
        (decodeAtom (scalarRows p.validated i)) f (signature_live i rep.live _) hf
  · intro d hd row
    have hd' : (p.validated.core.structural.get d).origin = .integer := by
      simpa only [(hflags d).2, decide_eq_true_eq] using hd
    rw [howners]
    simpa [observe, Vector.get, Vector.ofFn, Structural.observation] using
      decoded_scalar_rows p i hs rep.live d hd' f hf row

end ClaferCompiler.Correctness.Pipeline
