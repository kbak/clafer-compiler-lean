module

public import ClaferCompiler.Correctness.Behavioral.Full.RepresentationReading

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral (readPair readParent)

structure TargetIdentityData (v : IR.BehavioralStructural.Validated k) (state : Instance)
    (objects : Vector Nat o) (ids : IR.Behavioral.Identities k o) : Prop where
  read : readIdentities v state objects = .ok ids
  labels : ids.ids = objects
  unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y
  rootType : ids.directType[ids.root] = v.core.structural.root
  rootOnly : ∀ x : Fin o, ids.directType[x] = v.core.structural.root → x = ids.root
  pools : ∀ d label, label ∈ state.signatures[signatureId d]?.getD [] ↔
    ∃ x : Fin o, ids.directType[x] = d ∧ label = ids.ids[x]
  parents : ∀ row, row ∈ state.fields[0]?.getD [] ↔
    ∃ x p : Fin o, ids.parent[x] = some p ∧ row = [ids.ids[x], ids.ids[p]]
  rootSig : state.signatures[signatureId v.core.structural.root]?.getD [] = [ids.ids[ids.root]]

theorem targetObjects_unique (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true) :
    ∀ x y : Fin ((τ.state 0).signatures[0]?.getD []).length, (targetObjects τ)[x] = (targetObjects τ)[y] → x=y := by
  intro x y he
  apply Fin.ext
  exact (table_signature_nodup _ _ wf 0).getElem_inj_iff.mp (by simpa [targetObjects] using he)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Target declarations and identity clauses alone suffice for the actual
executable identity reader, including all pool and parent equations. -/
theorem target_readIdentities (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (decl : τ.Declarations (schema v))
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0) :
    ∃ ids, TargetIdentityData v (τ.state 0) (targetObjects τ) ids := by
  classical
  let objects := targetObjects τ
  let state := τ.state 0
  have wf := (decl.2.1 0).1
  have hd := (decl.2.1 0).2.1
  have unique := targetObjects_unique v τ wf
  have member (x : Fin objects.size) : objects[x] ∈ state.signatures[0]?.getD [] :=
    (targetObjects_members τ _).mpr ⟨x,rfl⟩
  obtain ⟨r, rootSig, rootMem⟩ := target_root_singleton v w τ wf hd facts
  obtain ⟨rootIndex, rootLabel⟩ := (targetObjects_members τ r).mp rootMem
  have typeExists (x : Fin objects.size) := target_identity_type v state hd objects[x] (member x)
  let types := fun x => (typeExists x).choose
  have typePools (x d) : objects[x] ∈ state.signatures[signatureId d]?.getD [] ↔
      types x = d := (typeExists x).choose_spec d
  have rootRead : state.signatures[signatureId v.core.structural.root]?.getD [] = [objects[rootIndex]] := by
    rw [rootSig,rootLabel]
  have rootType : types rootIndex = v.core.structural.root := by
    apply (typePools rootIndex v.core.structural.root).mp
    simp [rootRead]
  have rootOnly (x) (hx : types x = v.core.structural.root) : x=rootIndex := by
    apply unique
    have hm := (typePools x v.core.structural.root).mpr hx
    simpa [rootRead] using hm
  have typed (row) (hr : row ∈ state.fields[0]?.getD []) :
      ∃ x y : Fin objects.size, row = [objects[x],objects[y]] := by
    obtain ⟨a,b,he,ha,hb⟩ := target_parent_rows v τ 0 wf hd row hr
    obtain ⟨x,hx⟩ := (targetObjects_members τ a).mp ha
    obtain ⟨y,hy⟩ := (targetObjects_members τ b).mp hb
    exact ⟨x,y,by rw [he,hx,hy]⟩
  obtain ⟨pairs,pairsRead,pairsMap⟩ := readPairs_success objects unique (state.fields[0]?.getD []) typed
  have pairMember (x p) (h : (x,p) ∈ pairs) : [objects[x],objects[p]] ∈ state.fields[0]?.getD [] := by
    rw [← pairsMap]
    exact List.mem_map.mpr ⟨(x,p),h,rfl⟩
  have pairsNodup : pairs.Nodup := by
    apply List.Nodup.of_map (fun p : Fin objects.size × Fin objects.size => [objects[p.1],objects[p.2]])
    rw [pairsMap]
    exact table_field_nodup _ _ wf 0
  have functional (x p q) (hp : (x,p)∈pairs) (hq : (x,q)∈pairs) : p=q := by
    apply unique
    exact target_parent_unique v w τ wf hd facts r rootSig _ _ _ (pairMember x p hp) (pairMember x q hq)
  have parentExists (x) := readParent_success pairs pairsNodup functional x
  let parents := fun x => (parentExists x).choose
  have parentRead (x) : readParent pairs x = .ok (parents x) := (parentExists x).choose_spec.1
  have parentMeaning (x p) : parents x = some p ↔ (x,p) ∈ pairs := (parentExists x).choose_spec.2 p
  let ids : IR.Behavioral.Identities k objects.size :=
    { ids := objects, root := rootIndex, directType := Vector.ofFn types, parent := Vector.ofFn parents }
  have poolObject (d : Fin k) (label : Nat)
      (hm : label ∈ state.signatures[signatureId d]?.getD []) :
      label ∈ state.signatures[0]?.getD [] :=
    Structural.declaration_included (schema v).declarations state hd _ _ _
      (schema_signature v d) rfl label hm
  refine ⟨ids, ?_⟩
  refine ⟨readIdentities_success v state objects rootIndex types pairs parents unique rootRead
    (fun x => readType_exact state objects[x] (types x) (typePools x))
    pairsRead parentRead, rfl, unique, by simpa [ids] using rootType,
    by simpa [ids] using rootOnly, ?_, ?_, rootRead⟩
  · intro d label
    simp only [ids, Fin.getElem_fin, Vector.getElem_ofFn]
    change label ∈ state.signatures[signatureId d]?.getD [] ↔
      ∃ x, types x = d ∧ label = objects[x]
    constructor
    · intro hm
      obtain ⟨x,hx⟩ := (targetObjects_members τ label).mp (poolObject d label hm)
      exact ⟨x,(typePools x d).mp (hx ▸ hm),hx⟩
    · rintro ⟨x,hx,rfl⟩
      exact (typePools x d).mpr hx
  · intro row
    simp only [ids, Fin.getElem_fin, Vector.getElem_ofFn]
    change row ∈ state.fields[0]?.getD [] ↔
      ∃ x p, parents x = some p ∧ row = [objects[x],objects[p]]
    rw [← pairsMap]
    simp only [List.mem_map, Prod.exists, parentMeaning]
    constructor
    · rintro ⟨x,p,hp,he⟩
      exact ⟨x,p,hp,he.symm⟩
    · rintro ⟨x,p,hp,he⟩
      exact ⟨x,p,hp,he.symm⟩

end ClaferCompiler.Correctness.Behavioral.Full
