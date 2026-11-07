module

public import ClaferCompiler.Correctness.Behavioral.TargetIdentities
public import ClaferCompiler.Correctness.Behavioral.SnapshotProperties

public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

-- [proof->req~compiler-trace-representation~1]
theorem target_root_singleton (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (hd : (τ.state 0).declarations (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0) :
    ∃ r, (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r] ∧
      r ∈ (τ.state 0).signatures[0]?.getD [] := by
  have hf := facts (.mult .one (root v)) (by simp [identityFacts])
  have hn : ((τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD []).length = 1 := by
    change ((((τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD []).map
      (fun x => [Temporal.Atom.object x])).eraseDups.length == 1) = true at hf
    rw [eraseDups_map_injective (fun x : Nat => [Temporal.Atom.object x])
      (by intro x y he; simpa using he), List.length_map,
      eraseDups_of_nodup (table_signature_nodup _ _ wf _)] at hf
    exact beq_iff_eq.mp hf
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hn
  refine ⟨r, hr, ?_⟩
  have hp := v.coreChecked.2.2.1.2.2.1
  exact Structural.declaration_included (schema v).declarations (τ.state 0) hd
    _ 0 _ (Structural.schema_signature v v.core.root) (by simp [hp]) r (by simp [hr])

theorem target_parent_rows (v : IR.Structural.Layout k) (τ : Temporal.Trace) (t : Nat)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (row : List Nat) (hr : row ∈ (τ.state t).fields[0]?.getD []) :
    ∃ x y, row = [x,y] ∧ x ∈ (τ.state t).signatures[0]?.getD [] ∧
      y ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨x,y,rfl⟩ := Structural.field_binary _ _ wf 0 row hr
  exact ⟨x,y,rfl, Structural.field_typed _ _ hd 0 {owner:=0,target:=0} rfl x y hr⟩

theorem target_reference_rows (v : IR.Structural.Layout k) (τ : Temporal.Trace) (t : Nat)
    (wf : (τ.state t).wellFormed (schema v).declarations = true)
    (hd : (τ.state t).declarations (schema v).declarations = true)
    (d : Fin k) (row : List Nat) (hr : row ∈ (τ.state t).fields[2+d.val]?.getD []) :
    ∃ x y, row = [x,y] ∧ x ∈ (τ.state t).signatures[0]?.getD [] ∧
      y ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨x,y,rfl⟩ := Structural.field_binary _ _ wf _ row hr
  refine ⟨x,y,rfl, Structural.field_typed _ _ hd (2+d.val) {owner:=0,target:=0} ?_ x y hr⟩
  simp [schema, Nat.add_comm 2, d.isLt]

theorem target_root_static (v : IR.Structural.Layout k) (τ : Temporal.Trace)
    (hd : τ.Declarations (schema v)) (r : Nat)
    (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
    (t x : Nat) : x ∈ (τ.state t).signatures[Structural.signatureId v v.core.root]?.getD [] ↔ x=r := by
  rw [hd.2.2.1 (Structural.signatureId v v.core.root) (by
    simp [schema, (Structural.signatureId_bounds v v.core.root).2]) t x, hr]
  simp

theorem target_live_rows (v : IR.Structural.Layout k) (τ : Temporal.Trace)
    (hd : τ.Declarations (schema v)) (r : Nat)
    (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
    (t : Nat) (row : List Nat) (hrow : row ∈ (τ.state t).fields[1]?.getD []) :
    ∃ x, row = [r,x] ∧ x ∈ (τ.state t).signatures[0]?.getD [] := by
  obtain ⟨a,x,rfl⟩ := Structural.field_binary _ _ (hd.2.1 t).1 _ row hrow
  have typed := Structural.field_typed _ _ (hd.2.1 t).2.1 1
    {owner:=Structural.signatureId v v.core.root,target:=0} rfl a x hrow
  have he := (target_root_static v τ hd r hr t a).mp typed.1
  exact ⟨x, by simp [he], typed.2⟩

theorem target_parent_image (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
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

-- [proof->req~compiler-trace-representation~1]
theorem target_parent_root_empty (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
    (y : Nat) : [r,y] ∉ (τ.state 0).fields[0]?.getD [] := by
  intro row
  have fact := facts (.equal (.join (root v) parent) (.empty .unary)) (by simp [identityFacts])
  have image := Relations.unary_image Function.injective_id (.sig _) (.field 0)
    (raw_signature_unary (schema v) w τ [] 0 (Structural.signatureId v v.core.root))
    (raw_field_binary (schema v) w τ wf [] 0)
  have mem : [.object y] ∈ (Temporal.Rel.join (root v) parent).eval (schema v) w τ [] 0 :=
    (image _).mpr ⟨y, ⟨r, by simp [hr], row⟩, rfl⟩
  exact List.not_mem_nil ((fact _).mp mem)

theorem target_parent_one (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
    (x : Nat) (hx : x ∈ (τ.state 0).signatures[0]?.getD []) (hne : x ≠ r) :
    ((Temporal.Rel.join (.var 0) parent).eval (schema v) w τ [.object x] 0).eraseDups.length = 1 := by
  have fact := facts (.all (.diff (.sig 0) (root v)) (.mult .one (.join (.var 0) parent)))
    (by simp [identityFacts])
  have domain : [.object x] ∈ (Temporal.Rel.diff (.sig 0) (root v)).eval (schema v) w τ [] 0 := by
    simp only [root, pool]
    rw [Temporal.Rel.eval_diff (.sig _) (.sig _)]
    change [.object x] ∈ (((τ.state 0).signatures[0]?.getD []).map (fun a => [Temporal.Atom.object a])).filter
      (fun row => !((((τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD []).map
        (fun a => [Temporal.Atom.object a])).contains row))
    simp [hr,hx,hne]
  have h := fact (.object x) domain
  change (_ == 1) = true at h
  exact beq_iff_eq.mp h

theorem target_parent_unique (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (hd : (τ.state 0).declarations (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
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

theorem target_parent_total (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state 0).wellFormed (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (r : Nat) (hr : (τ.state 0).signatures[Structural.signatureId v v.core.root]?.getD [] = [r])
    (x : Nat) (hx : x ∈ (τ.state 0).signatures[0]?.getD []) (hne : x ≠ r) :
    ∃ y, [x,y] ∈ (τ.state 0).fields[0]?.getD [] := by
  have one := target_parent_one v w τ facts r hr x hx hne
  obtain ⟨row, hm⟩ := List.length_pos_iff_exists_mem.mp (show 0 <
    ((Temporal.Rel.join (.var 0) parent).eval (schema v) w τ [.object x] 0).eraseDups.length by omega)
  obtain ⟨y, hy, _⟩ := (target_parent_image v w τ wf x row).mp (List.mem_eraseDups.mp hm)
  exact ⟨y,hy⟩

end ClaferCompiler.Correctness.Behavioral
