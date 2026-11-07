module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureReferences
public import ClaferCompiler.Correctness.Behavioral.TargetData
public import ClaferCompiler.Correctness.Behavioral.RepresentationCompletion

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem schema_signature (v : IR.BehavioralStructural.Validated k) (d : Fin k) :
    (schema v).declarations.signatures[signatureId d]? = some { parent := some 0 } := by
  simp [schema, signatureId, Nat.add_comm 1, d.isLt]

theorem table_lengths (v : IR.BehavioralStructural.Validated k) (state : Instance)
    (wf : state.wellFormed (schema v).declarations = true) :
    state.signatures.length = k + 1 ∧ state.fields.length = k + 2 := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).1)
  constructor
  · simpa [schema] using beq_iff_eq.mp h.1
  · simpa [schema, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using beq_iff_eq.mp h.2

theorem signatureId_surjective (i : Nat) (positive : 0 < i) (small : i < k + 1) :
    ∃ d : Fin k, signatureId d = i :=
  ⟨⟨i - 1, by omega⟩, by simp [signatureId]; omega⟩

theorem target_signature_static (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace)
    (decl : τ.Declarations (schema v)) (t i label : Nat) :
    label ∈ (τ.state t).signatures[i]?.getD [] ↔ label ∈ (τ.state 0).signatures[i]?.getD [] := by
  by_cases hi : i < k + 1
  · exact decl.2.2.1 i (by simp [schema, hi]) t label
  · have ht := (table_lengths v _ (decl.2.1 t).1).1
    have hz := (table_lengths v _ (decl.2.1 0).1).1
    rw [List.getElem?_eq_none (by omega : (τ.state t).signatures.length ≤ i),
      List.getElem?_eq_none (by omega : (τ.state 0).signatures.length ≤ i)]

theorem target_pool_covered (v : IR.BehavioralStructural.Validated k) (i : Instance)
    (hd : i.declarations (schema v).declarations = true) (x : Nat)
    (hx : x ∈ i.signatures[0]?.getD []) :
    ∃ d : Fin k, x ∈ i.signatures[signatureId d]?.getD [] := by
  let s := (schema v).declarations
  let children := (s.signatures.zipIdx.filter fun (child, _) => child.parent == some 0).map Prod.snd
  have hr := schema_signature v v.core.structural.root
  have rootmem : signatureId v.core.structural.root ∈ children := by
    apply List.mem_map.mpr
    exact ⟨_, List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hr, rfl⟩, rfl⟩
  have nonempty : children.isEmpty = false := by
    cases he : children with
    | nil => simp [he] at rootmem
    | cons a as => rfl
  have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hd).1
    ({ isAbstract := true, scalar := true }, 0) (by simp [schema])
  simp only [Id.run, pure, Bool.and_eq_true] at hh
  have cover : children.any (fun c => (i.signatures[c]?.getD []).contains x) = true := by
    have cov := hh.1.1.2
    change (!true || children.isEmpty || _) = true at cov
    simp only [Bool.not_true, Bool.false_or, nonempty] at cov
    exact List.all_eq_true.mp cov x hx
  obtain ⟨c, hc, hcx⟩ := List.any_eq_true.mp cover
  obtain ⟨⟨decl, c'⟩, hchild, hce⟩ := List.mem_map.mp hc
  dsimp at hce
  subst c'
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hchild).1
  have hp : decl.parent = some 0 := beq_iff_eq.mp (List.mem_filter.mp hchild).2
  have hn : c ≠ 0 := by
    intro hz
    subst c
    have he : decl = { isAbstract := true, scalar := true } := by simpa [s, schema] using hg.symm
    subst decl
    cases hp
  have small : c < k + 1 := by
    have := List.getElem?_eq_some_iff.mp hg |>.1
    simpa [s, schema] using this
  obtain ⟨d, rfl⟩ := signatureId_surjective c (by omega) small
  exact ⟨d, List.contains_iff_mem.mp hcx⟩

theorem target_identity_type (v : IR.BehavioralStructural.Validated k) (i : Instance)
    (hd : i.declarations (schema v).declarations = true) (x : Nat)
    (hx : x ∈ i.signatures[0]?.getD []) :
    ∃ d : Fin k, ∀ e, x ∈ i.signatures[signatureId e]?.getD [] ↔ d = e := by
  obtain ⟨d, hdmem⟩ := target_pool_covered v i hd x hx
  refine ⟨d, fun e => ⟨?_, ?_⟩⟩
  · intro he
    by_contra different
    have dsig : signatureId d ≠ signatureId e := by
      intro eq
      apply different
      apply Fin.ext
      simp only [signatureId] at eq
      omega
    exact dsig (Structural.declaration_siblings (schema v).declarations i hd _ _ _ _
      (schema_signature v d) (schema_signature v e) rfl x hdmem he)
  · rintro rfl
    exact hdmem

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem target_root_singleton (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (hd : (τ.state 0).declarations (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0) :
    ∃ r, (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r] ∧
      r ∈ (τ.state 0).signatures[0]?.getD [] := by
  have hf := facts (.mult .one (root v)) (by simp [identityFacts])
  have hn : ((τ.state 0).signatures[signatureId v.core.structural.root]?.getD []).length = 1 := by
    change ((((τ.state 0).signatures[signatureId v.core.structural.root]?.getD []).map
      (fun x => [Temporal.Atom.object x])).eraseDups.length == 1) = true at hf
    rw [eraseDups_map_injective (fun x : Nat => [Temporal.Atom.object x])
      (by intro x y he; simpa using he), List.length_map,
      eraseDups_of_nodup (table_signature_nodup _ _ wf _)] at hf
    exact beq_iff_eq.mp hf
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hn
  refine ⟨r, hr, ?_⟩
  exact Structural.declaration_included (schema v).declarations (τ.state 0) hd
    _ 0 _ (schema_signature v v.core.structural.root) rfl r (by simp [hr])

theorem target_parent_rows (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace) (t : Nat)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (row : List Nat) (hr : row ∈ (τ.state t).fields[0]?.getD []) :
    ∃ x y, row = [x,y] ∧ x ∈ (τ.state t).signatures[0]?.getD [] ∧
      y ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨x,y,rfl⟩ := Structural.field_binary _ _ wf 0 row hr
  exact ⟨x,y,rfl, Structural.field_typed _ _ hd 0 {owner:=0,target:=0} rfl x y hr⟩

theorem target_reference_rows (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace) (t : Nat)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (d : Fin k) (row : List Nat) (hr : row ∈ (τ.state t).fields[2+d.val]?.getD []) :
    ∃ x y, row = [x,y] ∧ x ∈ (τ.state t).signatures[0]?.getD [] ∧
      y ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨x,y,rfl⟩ := Structural.field_binary _ _ wf _ row hr
  refine ⟨x,y,rfl, Structural.field_typed _ _ hd (2+d.val) {owner:=0,target:=0} ?_ x y hr⟩
  simp [schema, Nat.add_comm 2, d.isLt]

theorem target_root_static (v : IR.BehavioralStructural.Validated k) (τ : Temporal.Trace)
    (hd : τ.Declarations (schema v)) (r : Nat)
    (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (t x : Nat) : x ∈ (τ.state t).signatures[signatureId v.core.structural.root]?.getD [] ↔ x=r := by
  rw [hd.2.2.1 (signatureId v.core.structural.root) (by
    simp [schema, show signatureId v.core.structural.root < k + 1 by simp [signatureId]; omega]) t x, hr]
  simp

theorem target_live_rows (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (hd : τ.Declarations (schema v)) (r : Nat)
    (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (t : Nat) (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w τ [] t)
    (row : List Nat) (hrow : row ∈ (τ.state t).fields[1]?.getD []) :
    ∃ x, row = [r,x] ∧ x ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨a,x,rfl⟩ := Structural.field_binary _ _ (hd.2.1 t).1 _ row hrow
  have typed := facts (.subset (.field 1) (.product (root v) (.sig 0))) (by simp [stateFacts])
  have image := Relations.binary_product (.sig _) (.sig _)
    (raw_signature_unary (schema v) w τ [] t (signatureId v.core.structural.root))
    (raw_signature_unary (schema v) w τ [] t 0)
  have input : [Temporal.Atom.object a, .object x] ∈
      (Temporal.Rel.field 1).eval (schema v) w τ [] t := by
    change _ ∈ ((τ.state t).fields[1]?.getD []).map (List.map Temporal.Atom.object)
    exact List.mem_map.mpr ⟨[a, x], hrow, rfl⟩
  obtain ⟨b, c, ⟨hb, hc⟩, eq⟩ := (image _).mp (typed _ input)
  have ab : a = b := by simpa using (List.cons.inj eq).1
  have xc : x = c := by simpa using (List.cons.inj (List.cons.inj eq).2).1
  have he := (target_root_static v τ hd r hr t a).mp (ab ▸ hb)
  exact ⟨x, by simp [he], xc ▸ hc⟩

theorem target_parent_image (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true) (x : Nat) :
    Relations.Unary id {y | [x,y] ∈ (τ.state 0).fields[0]?.getD []}
      ((Temporal.Rel.join (.var 0) parent).eval (schema v) w τ [.object x] 0) := by
  have image := Relations.unary_image Function.injective_id (.var 0) (.field 0)
    (Relations.unary_singleton (f := id) x)
    (raw_field_binary (schema v) w τ wf [.object x] 0)
  intro row
  simp only [parent]
  rw [image row]
  simp

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem target_parent_root_empty (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (y : Nat) : [r,y] ∉ (τ.state 0).fields[0]?.getD [] := by
  intro row
  have fact := facts (.equal (.join (root v) parent) (.empty .unary)) (by simp [identityFacts])
  have image := Relations.unary_image Function.injective_id (.sig _) (.field 0)
    (raw_signature_unary (schema v) w τ [] 0 (signatureId v.core.structural.root))
    (raw_field_binary (schema v) w τ wf [] 0)
  have mem : [.object y] ∈ (Temporal.Rel.join (root v) parent).eval (schema v) w τ [] 0 :=
    (image _).mpr ⟨y, ⟨r, by simp [hr], row⟩, rfl⟩
  exact List.not_mem_nil ((fact _).mp mem)

theorem target_parent_one (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (x : Nat) (hx : x ∈ (τ.state 0).signatures[0]?.getD []) (hne : x ≠ r) :
    ((Temporal.Rel.join (.var 0) parent).eval (schema v) w τ [.object x] 0).eraseDups.length = 1 := by
  have fact := facts (.all (.diff (.sig 0) (root v)) (.mult .one (.join (.var 0) parent)))
    (by simp [identityFacts])
  have domain : [.object x] ∈ (Temporal.Rel.diff (.sig 0) (root v)).eval (schema v) w τ [] 0 := by
    simp only [root, directPool]
    rw [Temporal.Rel.eval_diff (.sig _) (.sig _)]
    change [.object x] ∈ (((τ.state 0).signatures[0]?.getD []).map (fun a => [Temporal.Atom.object a])).filter
      (fun row => !((((τ.state 0).signatures[signatureId v.core.structural.root]?.getD []).map
        (fun a => [Temporal.Atom.object a])).contains row))
    simp [hr,hx,hne]
  have h := fact (.object x) domain
  change (_ == 1) = true at h
  exact beq_iff_eq.mp h

theorem target_parent_unique (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (hd : (τ.state 0).declarations (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (x y z : Nat) (hy : [x,y] ∈ (τ.state 0).fields[0]?.getD [])
    (hz : [x,z] ∈ (τ.state 0).fields[0]?.getD []) : y=z := by
  have hx := (Structural.field_typed _ _ hd 0 {owner:=0,target:=0} rfl x y hy).1
  have hne : x ≠ r := by
    intro he
    subst x
    exact target_parent_root_empty v w τ wf facts r hr y hy
  obtain ⟨row, he⟩ := List.length_eq_one_iff.mp (target_parent_one v w τ facts r hr x hx hne)
  have image := target_parent_image v w τ wf x
  have hmy := List.mem_eraseDups.mpr ((image _).mpr ⟨y, hy, rfl⟩)
  have hmz := List.mem_eraseDups.mpr ((image _).mpr ⟨z, hz, rfl⟩)
  rw [he] at hmy hmz
  have hye : [Temporal.Atom.object y] = row := by simpa using hmy
  have hze : [Temporal.Atom.object z] = row := by simpa using hmz
  simpa using hye.trans hze.symm

theorem target_parent_total (v : IR.BehavioralStructural.Validated k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[signatureId v.core.structural.root]?.getD [] = [r])
    (x : Nat) (hx : x ∈ (τ.state 0).signatures[0]?.getD []) (hne : x ≠ r) :
    ∃ y, [x,y] ∈ (τ.state 0).fields[0]?.getD [] := by
  have one := target_parent_one v w τ facts r hr x hx hne
  obtain ⟨row, hm⟩ := List.length_pos_iff_exists_mem.mp (show 0 <
    ((Temporal.Rel.join (.var 0) parent).eval (schema v) w τ [.object x] 0).eraseDups.length by omega)
  obtain ⟨y, hy, _⟩ := (target_parent_image v w τ wf x row).mp (List.mem_eraseDups.mp hm)
  exact ⟨y,hy⟩

end ClaferCompiler.Correctness.Behavioral.Full
