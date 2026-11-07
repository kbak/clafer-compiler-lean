module

public import ClaferCompiler.Correctness.Behavioral.SnapshotFormulas
public import ClaferCompiler.Correctness.Behavioral.RepresentationRelations
public import ClaferCompiler.Correctness.StructuralRelations

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral

def objectValue : Temporal.Atom → Nat
  | .object n => n
  | .integer _ => 0

def unaryValues (rows : Temporal.Relation) : List Nat :=
  rows.map fun row => objectValue (row.headD (.object 0))

def rowValues (rows : Temporal.Relation) : Alloy.Relation :=
  rows.map (List.map objectValue)

/-- Concrete projection of one temporal state into the already verified M1
target. It keeps live heads and reference occurrences, not unused identities. -/
def snapshotState (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace) (t : Nat) : Instance where
  signatures := (List.range (k + 1)).map fun n =>
    unaryValues ((snapshotRel v (.sig n)).eval (schema v) w τ [] t)
  fields := (List.range (Structural.fieldKeys v.core).length).map fun n =>
    rowValues ((snapshotRel v (.field n)).eval (schema v) w τ [] t)

theorem unaryValues_exact {rows : Temporal.Relation}
    (h : ∀ row ∈ rows, ∃ x, row = [.object x]) :
    objectRows ((unaryValues rows).map fun x => [x]) = rows := by
  simp only [objectRows, unaryValues, List.map_map]
  rw [List.map_congr_left (g := id) (by
    intro row hr
    obtain ⟨x, rfl⟩ := h row hr
    rfl)]
  exact List.map_id _

theorem rowValues_exact {rows : Temporal.Relation}
    (h : ∀ row ∈ rows, ∃ x y, row = [.object x, .object y]) :
    objectRows (rowValues rows) = rows := by
  simp only [objectRows, rowValues, List.map_map]
  rw [List.map_congr_left (g := id) (by
    intro row hr
    obtain ⟨x, y, rfl⟩ := h row hr
    rfl)]
  exact List.map_id _

theorem raw_signature_unary (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace)
    (e : Temporal.Environment) (t n : Nat) :
    Relations.Unary id {x | x ∈ (τ.state t).signatures[n]?.getD []}
      ((Temporal.Rel.sig n).eval s w τ e t) := by
  intro row
  change row ∈ ((τ.state t).signatures[n]?.getD []).map (fun x => [.object x]) ↔ _
  simp [eq_comm]

theorem raw_field_binary (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed s.declarations = true)
    (e : Temporal.Environment) (n : Nat) :
    Relations.Binary id (fun x y => [x, y] ∈ (τ.state t).fields[n]?.getD [])
      ((Temporal.Rel.field n).eval s w τ e t) := by
  intro row
  change row ∈ ((τ.state t).fields[n]?.getD []).map (List.map Temporal.Atom.object) ↔ _
  constructor
  · rintro h
    obtain ⟨r, hr, he⟩ := List.mem_map.mp h
    obtain ⟨x, y, rfl⟩ := Structural.field_binary s.declarations (τ.state t) wf n r hr
    exact ⟨x, y, hr, he.symm⟩
  · rintro ⟨x, y, hr, rfl⟩
    exact List.mem_map.mpr ⟨[x, y], hr, rfl⟩

theorem snapshotSig_env (v : IR.Structural.Layout k) (s : Temporal.Schema) (w : Nat)
    (τ : Temporal.Trace) (t n : Nat) (e : Temporal.Environment) :
    (snapshotRel v (.sig n)).eval s w τ e t =
      (snapshotRel v (.sig n)).eval s w τ [] t := by
  simp only [snapshotRel_sig]
  split <;> rfl

theorem snapshotField_env (v : IR.Structural.Layout k) (s : Temporal.Schema) (w : Nat)
    (τ : Temporal.Trace) (t n : Nat) (e : Temporal.Environment) :
    (snapshotRel v (.field n)).eval s w τ e t =
      (snapshotRel v (.field n)).eval s w τ [] t := by
  simp only [snapshotRel_field]
  split
  · rename_i _ d hd
    unfold contains
    split <;> rfl
  · rfl
  · rfl

theorem snapshotSig_unary (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) :
    ∀ row ∈ (snapshotRel v (.sig n)).eval (schema v) w τ [] t,
      ∃ x, row = [.object x] := by
  have hr := raw_signature_unary (schema v) w τ [] t (Structural.signatureId v v.core.root)
  have hl := Relations.unary_image Function.injective_id (.sig _) (.field _)
    hr (raw_field_binary (schema v) w τ wf [] 1)
  change ∀ row ∈ (if n == 0 then live v else Temporal.Rel.inter (.sig n) (live v)).eval
    (schema v) w τ [] t, _
  split
  · intro row hrow
    obtain ⟨x, _, he⟩ := (hl row).mp hrow
    exact ⟨x, he⟩
  · intro row hrow
    have h := Relations.unary_inter Function.injective_id (.sig _) (.join (.sig _) (.field _))
      (raw_signature_unary (schema v) w τ [] t n) hl
    obtain ⟨x, _, he⟩ := (h row).mp hrow
    exact ⟨x, he⟩

theorem snapshotField_binary (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) :
    ∀ row ∈ (snapshotRel v (.field n)).eval (schema v) w τ [] t,
      ∃ x y, row = [.object x, .object y] := by
  change ∀ row ∈ (match (Structural.fieldKeys v.core)[n]? with
    | some (d, .containment) => contains v d
    | some (d, .dereference) => deref d
    | none => Temporal.Rel.empty .binary).eval (schema v) w τ [] t, _
  split
  · rename_i _ d hd
    unfold contains
    split
    · simp [Temporal.Rel.eval, Temporal.Rel.fold, Temporal.Rel.empty, Temporal.RelAlgebra.step,
        Temporal.relationAlgebra]
    · intro row hrow
      simp only [parent, live, head, root, pool] at hrow
      rw [Temporal.Rel.eval_inter (.transpose (.field _))
        (.product (.join (.sig _) (.field _)) (.inter (.sig _) (.join (.sig _) (.field _))))] at hrow
      have hp := Relations.binary_transpose (.field _)
        (raw_field_binary (schema v) w τ wf [] 0)
      obtain ⟨x, y, _, he⟩ := (hp row).mp (List.mem_filter.mp hrow).1
      exact ⟨x, y, he⟩
  · rename_i _ d hd
    intro row hrow
    obtain ⟨x, y, _, he⟩ := (raw_field_binary (schema v) w τ wf [] (2 + d.val) row).mp hrow
    exact ⟨x, y, he⟩
  · simp [Temporal.Rel.eval, Temporal.Rel.fold, Temporal.Rel.empty, Temporal.RelAlgebra.step,
      Temporal.relationAlgebra]

-- [proof->req~compiler-behavioral-correctness~1]
theorem snapshotState_signatures (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) (env : List Nat) :
    (snapshotRel v (.sig n)).eval (schema v) w τ (env.map .object) t =
      objectRows ((Rel.sig n).eval (snapshotState v w τ t) env) := by
  rw [snapshotSig_env]
  by_cases hn : n < k + 1
  · simp only [Rel.eval_sig, snapshotState, List.getElem?_map, List.getElem?_range hn,
      Option.map_some, Option.getD_some]
    exact (unaryValues_exact (snapshotSig_unary v w τ wf n)).symm
  · have length : (τ.state t).signatures.length = k + 1 := by
      have hl := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).1).1
      simpa [schema, Structural.signature_inventory] using hl
    have out : (τ.state t).signatures[n]? = none := List.getElem?_eq_none (by omega)
    have nonzero : n ≠ 0 := by omega
    have rangeOut : (List.range (k + 1))[n]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hn)
    simp only [Rel.eval_sig, snapshotState, List.getElem?_map, rangeOut, Option.map_none,
      Option.getD_none, List.map_nil, objectRows]
    rw [snapshotRel_sig]
    simp only [beq_eq_false_iff_ne.mpr nonzero, Bool.false_eq_true, ↓reduceIte]
    unfold live root pool
    rw [Temporal.Rel.eval_inter (.sig _) (.join (.sig _) (.field _))]
    change (((τ.state t).signatures[n]?.getD []).map _).filter _ = []
    simp [out]

theorem snapshotState_fields (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) (env : List Nat) :
    (snapshotRel v (.field n)).eval (schema v) w τ (env.map .object) t =
      objectRows ((Rel.field n).eval (snapshotState v w τ t) env) := by
  rw [snapshotField_env]
  by_cases hn : n < (Structural.fieldKeys v.core).length
  · simp only [Rel.eval_field, snapshotState, List.getElem?_map, List.getElem?_range hn,
      Option.map_some, Option.getD_some]
    exact (rowValues_exact (snapshotField_binary v w τ wf n)).symm
  · have out : (Structural.fieldKeys v.core)[n]? = none := List.getElem?_eq_none (by omega)
    have rangeOut : (List.range (Structural.fieldKeys v.core).length)[n]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hn)
    simp only [Rel.eval_field, snapshotState, List.getElem?_map, rangeOut, Option.map_none,
      Option.getD_none]
    change (match (Structural.fieldKeys v.core)[n]? with
      | some (d, .containment) => contains v d
      | some (d, .dereference) => deref d
      | none => Temporal.Rel.empty .binary).eval (schema v) w τ [] t = []
    rw [out]
    rfl

end ClaferCompiler.Correctness.Behavioral
