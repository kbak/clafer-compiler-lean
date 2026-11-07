module

public import ClaferCompiler.Correctness.Behavioral.SnapshotTables
public import ClaferCompiler.Correctness.Behavioral.Compilation

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy

theorem SnapshotRel.unionList (rs : List Rel) (h : ∀ r ∈ rs, SnapshotRel r) :
    SnapshotRel (Alloy.Structural.union rs) := by
  unfold Alloy.Structural.union
  generalize ha : Rel.empty .unary = a
  have init : SnapshotRel a := ha ▸ SnapshotRel.empty .unary
  clear ha
  induction rs generalizing a with
  | nil => exact init
  | cons r rs ih =>
    exact ih (fun q hq => h q (by simp [hq])) _ (.union init (h r (by simp)))

theorem static_sig_unary (i : Instance) (n : Nat) :
    ∀ env row, row ∈ (Rel.sig n).eval i env → ∃ x, row = [x] := by
  intro env row h
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
  exact ⟨x, rfl⟩

theorem static_var_field_unary (s : Alloy.Schema) (i : Instance)
    (wf : i.wellFormed s = true) (j f : Nat) :
    ∀ env row, row ∈ (Rel.join (.var j) (.field f)).eval i env → ∃ x, row = [x] := by
  intro env row h
  cases he : env[j]? with
  | none =>
    rw [Rel.eval_join (.var _) (.field _)] at h
    simp [he] at h
  | some a =>
    obtain ⟨b, _, he⟩ := (Structural.mem_join_singleton (.field f) (.field f)
      i env j a he (Structural.field_binary s i wf f) row).mp h
    exact ⟨b, he⟩

theorem snapshot_interval (i : Instance) (bounds : IR.Structural.Bounds) (r : Rel)
    (hr : SnapshotRel r) : SnapshotFormula i (Alloy.Structural.interval bounds r) := by
  apply SnapshotFormula.conj
  · split
    · exact .truth
    · exact .compare _ (.literal _) (.count hr)
  · cases bounds.upper with
    | unbounded => exact .truth
    | finite _ => exact .compare _ (.count hr) (.literal _)

theorem snapshot_childHeads (m : IR.Structural.Core k) (d : Fin k) :
    SnapshotRel (Alloy.Structural.childHeads m d) := by
  apply SnapshotRel.unionList
  intro r hr
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
  exact .join (.var _) (.field _)

theorem snapshot_declarationFacts (v : IR.Structural.Layout k) (i : Instance)
    (wf : i.wellFormed (Alloy.Structural.schema v) = true) (d : Fin k)
    (f : Alloy.Structural.Obligation × Alloy.Formula)
    (hf : f ∈ Alloy.Structural.declarationFacts v d) : SnapshotFormula i f.2 := by
  have group : SnapshotFormula i (.all (Alloy.Structural.head v d)
      (Alloy.Structural.interval (v.core.get d).groupBounds (Alloy.Structural.childHeads v.core d))) :=
    .all (.sig _) (static_sig_unary i _) (snapshot_interval i _ _ (snapshot_childHeads v.core d))
  have abstract : SnapshotFormula i (.equal (Alloy.Structural.head v d)
      (Alloy.Structural.union ((Alloy.Structural.subtypes v.core d).map (Alloy.Structural.head v)))) := by
    apply SnapshotFormula.equal (.sig _)
    apply SnapshotRel.unionList
    intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    exact .sig _
  have own : SnapshotFormula i (Alloy.Structural.ownership v d) :=
    .all (.sig _) (static_sig_unary i _) (.mult .one (.join (.var _) (.transpose (.field _))))
  have localBounds (p : Fin k) : SnapshotFormula i (.all (Alloy.Structural.head v p)
      (Alloy.Structural.interval (v.core.get d).localBounds
        (.join (.var 0) (Alloy.Structural.contains v.core d)))) :=
    .all (.sig _) (static_sig_unary i _) (snapshot_interval i _ _ (.join (.var _) (.field _)))
  have key (p : Fin k) : SnapshotFormula i (Alloy.Structural.setKey v d p) :=
    .all (.sig _) (static_sig_unary i _)
      (.all (.join (.var _) (.field _)) (static_var_field_unary _ i wf _ _)
        (.all (.join (.var _) (.field _)) (static_var_field_unary _ i wf _ _)
          (.key (.join (.var _) (.field _)) (.join (.var _) (.field _)) (.var _) (.var _))))
  simp only [Alloy.Structural.declarationFacts] at hf
  rcases List.mem_append.mp hf with ha | hp
  · split at ha <;> simpa using List.mem_singleton.mp ha ▸ (by assumption : SnapshotFormula i _)
  · cases hparent : (v.core.get d).parent with
    | none => simp [hparent] at hp
    | some p =>
      simp only [hparent] at hp
      rcases List.mem_append.mp hp with hb | hk
      · rcases List.mem_cons.mp hb with he | hb
        · cases he; exact own
        · have he := List.mem_singleton.mp hb
          cases he; exact localBounds p
      · cases href : (v.core.get d).reference <;> simp only [href] at hk
        · simp at hk
        · have he := List.mem_singleton.mp hk
          cases he; exact key p
        · simp at hk

-- [proof->req~compiler-behavioral-correctness~1]
/-- The transport grammar covers every fact actually emitted by M1. -/
theorem snapshot_facts (v : IR.Structural.Layout k) (i : Instance)
    (wf : i.wellFormed (Alloy.Structural.schema v) = true)
    (f : Alloy.Structural.Obligation × Alloy.Formula) (hf : f ∈ Alloy.Structural.facts v) :
    SnapshotFormula i f.2 := by
  simp only [Alloy.Structural.facts, List.mem_append] at hf
  rcases hf with hf | hf
  · rcases List.mem_cons.mp hf with he | hf
    · cases he; exact .mult .one (.sig _)
    · have he := List.mem_singleton.mp hf
      cases he
      apply SnapshotFormula.equal (.sig _)
      apply SnapshotRel.unionList
      intro r hr
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
      exact .sig _
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hf
    exact snapshot_declarationFacts v i wf d f hd

-- [proof->req~compiler-behavioral-correctness~1]
theorem snapshot_fact_value (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (frame : (τ.state t).wellFormed (Backend.Alloy.Behavioral.schema v).declarations = true)
    (wf : (snapshotState v w τ t).wellFormed (Alloy.Structural.schema v) = true)
    (f : Alloy.Structural.Obligation × Alloy.Formula) (hf : f ∈ Alloy.Structural.facts v)
    (holds : (Backend.Alloy.Behavioral.snapshotFormula v f.2).Defined
        (Backend.Alloy.Behavioral.schema v) w τ [] t ∧
      (Backend.Alloy.Behavioral.snapshotFormula v f.2).Holds
        (Backend.Alloy.Behavioral.schema v) w τ [] t) :
    f.2.eval w (snapshotState v w τ t) [] = some true :=
  (snapshotFormula_eval v (snapshot_facts v _ wf f hf) _ w τ t
    (snapshotState_signatures v w τ frame) (snapshotState_fields v w τ frame) []).mp holds

end ClaferCompiler.Correctness.Behavioral
