module

public import ClaferCompiler.Correctness.Behavioral.SnapshotProperties
public import ClaferCompiler.Correctness.Behavioral.LiveSnapshot
public import ClaferCompiler.Correctness.Behavioral.RepresentationInvariants
public import ClaferCompiler.Correctness.StructuralReferences

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

theorem snapshot_contains_rel (v : IR.Structural.Layout k) (d : Fin k)
    (hp : (v.core.get d).parent.isSome = true) :
    snapshotRel v (.field (Alloy.Structural.fieldId v.core d .containment)) = contains v d := by
  rw [snapshotRel_field]
  simp [Alloy.Structural.fieldId, List.getElem?_idxOf
    ((Alloy.Structural.containment_inventory v.core d).mpr hp)]

theorem snapshot_deref_rel (v : IR.Structural.Layout k) (d : Fin k)
    (hp : (v.core.get d).reference.target.isSome = true) :
    snapshotRel v (.field (Alloy.Structural.fieldId v.core d .dereference)) = deref d := by
  rw [snapshotRel_field]
  simp [Alloy.Structural.fieldId, List.getElem?_idxOf
    ((Alloy.Structural.dereference_inventory v.core d).mpr hp)]

theorem snapshot_head_rel (v : IR.Structural.Layout k) (d : Fin k) :
    snapshotRel v (.sig (Alloy.Structural.signatureId v d)) = head v d := by
  rw [snapshotRel_sig]
  simp only [head, pool, beq_iff_eq,
    Nat.ne_of_gt (Alloy.Structural.signatureId_bounds v d).1, ↓reduceIte]

theorem snapshot_field_mem (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (wf : (τ.state t).wellFormed (schema v).declarations = true) (n : Nat) (row : Alloy.Tuple) :
    row ∈ (snapshotState v w τ t).fields[n]?.getD [] ↔
      row.map Temporal.Atom.object ∈ (snapshotRel v (.field n)).eval (schema v) w τ [] t := by
  have tables := snapshotState_fields v w τ wf n []
  simp only [List.map_nil] at tables
  rw [tables]
  change row ∈ _ ↔ row.map Temporal.Atom.object ∈ objectRows _
  simp [objectRows, objectRow_injective.eq_iff]

namespace TraceRep
variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Temporal.Lasso}

theorem snapshot_objects (rep : TraceRep v source target) (w : Nat) (t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true) (label : Nat) :
    label ∈ (snapshotState v w target.unfold t).signatures[0]?.getD [] ↔
      ∃ x ∈ (trace source).live t, label = rep.label x := by
  rw [snapshot_extent_mem v w target.unfold wf 0 label]
  change [.object label] ∈ (live v).eval (schema v) w target.unfold [] t ↔ _
  rw [rep.live_meaning w [] t]
  simp

theorem snapshot_heads (rep : TraceRep v source target) (w : Nat) (t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (d : Fin k) (label : Nat) :
    label ∈ (snapshotState v w target.unfold t).signatures[Alloy.Structural.signatureId v d]?.getD [] ↔
      ∃ x ∈ ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).head d,
        label = rep.label x := by
  rw [snapshot_extent_mem v w target.unfold wf, snapshot_head_rel, rep.head_meaning w [] t d]
  simp

def snapshotObjects (rep : TraceRep v source target) (w : Nat) (t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true) :
    (trace source).Live t ≃
      {x : Nat // x ∈ (snapshotState v w target.unfold t).signatures[0]?.getD []} :=
  Equiv.ofBijective (fun x => ⟨rep.label x.val,
    (rep.snapshot_objects w t wf _).mpr ⟨x.val, x.property, rfl⟩⟩) (by
      constructor
      · intro x y h
        exact Subtype.ext (rep.label_injective (congrArg (fun z => z.val) h))
      · rintro ⟨label, hl⟩
        obtain ⟨x, hx, he⟩ := (rep.snapshot_objects w t wf label).mp hl
        exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩)

@[simp] theorem snapshotObjects_label (rep : TraceRep v source target) (w t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (x : (trace source).Live t) : (rep.snapshotObjects w t wf x).val = rep.label x.val := rfl

theorem snapshot_root (rep : TraceRep v source target) (w t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (rootLive : (trace source).identities.root ∈ (trace source).live t) :
    (snapshotState v w target.unfold t).signatures[Alloy.Structural.signatureId v v.core.root]?.getD [] =
      [rep.label source.identities.root] := by
  classical
  let xs := (snapshotState v w target.unfold t).signatures[Alloy.Structural.signatureId v v.core.root]?.getD []
  have mem : ∀ label, label ∈ xs ↔ label = rep.label source.identities.root := by
    intro label
    rw [rep.snapshot_heads w t wf v.core.root label]
    constructor
    · rintro ⟨x, hx, he⟩
      have ht : source.identities.directType[x] = v.core.root :=
        (Structural.ancestor_root_iff v _).mp hx.2
      exact he.trans (congrArg rep.label (rep.root_only x ht))
    · intro he
      refine ⟨source.identities.root, ⟨rootLive, ?_⟩, he⟩
      change (SemanticsBridge.Structural.interpret v.core).Ancestor
        source.identities.directType[source.identities.root] v.core.root
      rw [rep.root_type]
      exact .refl
  have hn : xs.Nodup := table_signature_nodup _ _ (snapshotState_wellFormed v w target.unfold wf) _
  have length : xs.length = 1 := by
    rw [← List.toFinset_card_of_nodup hn]
    have eq : xs.toFinset = {rep.label source.identities.root} := by ext; simp [mem]
    rw [eq]
    simp
  obtain ⟨x, he⟩ := List.length_eq_one_iff.mp length
  have hx : x = rep.label source.identities.root := (mem x).mp (by simp [he])
  simpa [xs, hx] using he

theorem reference_typed (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (x y : Fin o) (h : (trace source).deref t d x y) :
    ∃ targetType, (v.core.get d).reference.target = some targetType ∧
      x ∈ ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).head d ∧
      y ∈ ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).head targetType := by
  have row := (rep.deref_meaning w [] t d _).mpr ⟨x, y, h, rfl⟩
  have generated (f : Temporal.Formula) (hf : f ∈ snapshotDeclarations v) :
      f.Holds (schema v) w target.unfold [] t := facts f (by
        apply List.mem_append_left
        exact List.mem_append_right _ hf)
  cases hr : (v.core.get d).reference.target with
  | none =>
    have empty := generated (.equal (deref d) (.empty .binary)) (by
      apply List.mem_flatMap.mpr
      exact ⟨d, List.mem_finRange _, by simp [hr]⟩)
    exact (List.not_mem_nil ((empty _).mp row)).elim
  | some targetType =>
    have typed := generated (.binary .conj
      (.subset (deref d) (.product (head v d) (head v targetType)))
      (.all (head v d) (.mult .one (.join (.var 0) (deref d))))) (by
        apply List.mem_flatMap.mpr
        exact ⟨d, List.mem_finRange _, by simp [hr]⟩)
    change (_ ∧ _) at typed
    have product := typed.1 _ row
    have image := Relations.binary_product (head_term v d) (head_term v targetType)
      (rep.head_meaning w [] t d) (rep.head_meaning w [] t targetType)
    obtain ⟨a, b, hab, he⟩ := (image _).mp product
    have hx : x = a := rep.label_injective (by simpa using (List.cons.inj he).1)
    have hy : y = b := rep.label_injective (by simpa using (List.cons.inj (List.cons.inj he).2).1)
    exact ⟨targetType, rfl, hx ▸ hab.1, hy ▸ hab.2⟩

theorem references_live (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (x y : Fin o) (h : (trace source).deref t d x y) :
    x ∈ (trace source).live t ∧ y ∈ (trace source).live t := by
  obtain ⟨_, _, hx, hy⟩ := rep.reference_typed w t facts d x y h
  exact ⟨hx.1, hy.1⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- The projected temporal tables represent the source live snapshot under the
restriction of the same global identity bijection. No source validity is assumed. -/
def snapshotRepData (rep : TraceRep v source target) (w t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (liveTables : Structural.Live (snapshotState v w target.unfold t))
    (activeRefs : ∀ d x y, (trace source).deref t d x y →
      (v.core.get d).reference.target.isSome = true)
    (rootLive : (trace source).identities.root ∈ (trace source).live t) :
    Structural.Represents v (liveSnapshot (SemanticsBridge.Structural.interpret v.core)
      (trace source) t rootLive) (snapshotState v w target.unfold t) where
  wellFormed := snapshotState_wellFormed v w target.unfold wf
  live := liveTables
  objects := rep.snapshotObjects w t wf
  root := rep.snapshot_root w t wf rootLive
  heads := by
    intro d x
    rw [rep.snapshot_heads w t wf d]
    constructor
    · intro hx; exact ⟨x.val, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      change x.val ∈ ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).head d
      rw [rep.label_injective he]
      exact hy
  containment := by
    intro d p x
    constructor
    · intro h
      have active : (v.core.get d).parent.isSome = true := by
        cases hp : (v.core.get d).parent with
        | none => exact (h.2.2 hp).elim
        | some _ => rfl
      refine ⟨active, ?_⟩
      rw [snapshot_field_mem v w target.unfold wf, snapshot_contains_rel v d active]
      exact (rep.step_meaning w [] t (.child d) _).mpr ⟨p.val, x.val, h, rfl⟩
    · rintro ⟨active, h⟩
      rw [snapshot_field_mem v w target.unfold wf, snapshot_contains_rel v d active] at h
      obtain ⟨a, b, hab, he⟩ := (rep.step_meaning w [] t (.child d) _).mp h
      have hp : p.val = a := rep.label_injective (by simpa using (List.cons.inj he).1)
      have hx : x.val = b := rep.label_injective (by simpa using (List.cons.inj (List.cons.inj he).2).1)
      change ((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).contains d p.val x.val
      rw [hp, hx]
      exact hab
  dereference := by
    intro d x y
    constructor
    · intro h
      have active := activeRefs d x.val y.val h
      refine ⟨active, ?_⟩
      rw [snapshot_field_mem v w target.unfold wf, snapshot_deref_rel v d active]
      exact (rep.deref_meaning w [] t d _).mpr ⟨x.val, y.val, h, rfl⟩
    · rintro ⟨active, h⟩
      rw [snapshot_field_mem v w target.unfold wf, snapshot_deref_rel v d active] at h
      obtain ⟨a, b, hab, he⟩ := (rep.deref_meaning w [] t d _).mp h
      have hx : x.val = a := rep.label_injective (by simpa using (List.cons.inj he).1)
      have hy : y.val = b := rep.label_injective (by simpa using (List.cons.inj (List.cons.inj he).2).1)
      change (trace source).deref t d x.val y.val
      rw [hx, hy]
      exact hab

/-- Target declarations and emitted reference clauses supply the data-only
premises of the common snapshot representation. -/
def snapshotRep (rep : TraceRep v source target) (w t : Nat)
    (wf : (target.unfold.state t).wellFormed (schema v).declarations = true)
    (sw : (Alloy.Structural.schema v).wellFormed = true)
    (sd : (snapshotState v w target.unfold t).declarations (Alloy.Structural.schema v) = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (rootLive : (trace source).identities.root ∈ (trace source).live t) :
    Structural.Represents v (liveSnapshot (SemanticsBridge.Structural.interpret v.core)
      (trace source) t rootLive) (snapshotState v w target.unfold t) :=
  rep.snapshotRepData w t wf
    (Structural.declarations_live _ _ sw (snapshotState_wellFormed v w target.unfold wf)
      sd (Structural.schema_parentless v))
    (fun d x y h => by
      obtain ⟨c, hc, _, _⟩ := rep.reference_typed w t facts d x y h
      simp [hc]) rootLive

end TraceRep
end ClaferCompiler.Correctness.Behavioral
