module

public import ClaferCompiler.Backend.Alloy.StructuralRepresentation
public import ClaferCompiler.Correctness.StructuralGeneration
public import ClaferCompiler.Correctness.AlloyEvaluation
public import ClaferCompiler.SemanticsBridge.Structural
public import Clafer.Semantics.Renaming

@[expose] public section
/-! [proof->req~compiler-structural-representation~1] -/

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural

/-- The carrier is precisely the object-union extent. Unused allocation slots
are absent; no auxiliary atom can manufacture a source object. -/
abbrev Objects (o : Observation n) := {x : Nat // x ∈ o.objects}

instance objectsFintype (o : Observation n) : Fintype (Objects o) :=
  Fintype.ofFinset o.objects.toFinset (by
    intro x
    change x ∈ o.objects.toFinset ↔ x ∈ o.objects
    simp)

theorem objects_card (o : Observation n) :
    Fintype.card (Objects o) = o.objects.toFinset.card :=
  Fintype.card_ofFinset _ _

/-- Interpret only data equations into the independent upstream configuration. -/
def realize (o : Observation n) (hr : o.root ∈ o.objects) :
    Clafer.Semantics.Configuration (Fin n) (Objects o) where
  root := ⟨o.root, hr⟩
  head d := {x | x.val ∈ o.heads d}
  contains d p x := (p.val, x.val) ∈ o.containment d
  deref d x t := (x.val, t.val) ∈ o.dereference d

/-- All allocated extent and tuple atoms belong to the declared live carrier.
This is a finite data condition, independent of either satisfaction relation. -/
def Live (i : Instance) : Prop :=
  (∀ xs ∈ i.signatures, ∀ x ∈ xs, x ∈ i.signatures[0]?.getD []) ∧
  (∀ ts ∈ i.fields, ∀ tuple ∈ ts, ∀ x ∈ tuple, x ∈ i.signatures[0]?.getD [])

/-- Concrete representation, up to a bijection of the common live carrier.
All equations concern data; neither source nor target satisfaction occurs. -/
structure Represents (v : IR.Structural.Validated n)
    {U : Type} (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance) where
  wellFormed : i.wellFormed (schema v) = true
  live : Live i
  objects : U ≃ {x : Nat // x ∈ i.signatures[0]?.getD []}
  root : i.signatures[signatureId v v.core.root]?.getD [] = [objects s.root]
  heads : ∀ d x, x ∈ s.head d ↔ (objects x).val ∈ i.signatures[signatureId v d]?.getD []
  containment : ∀ d p x, s.contains d p x ↔
    (v.core.get d).parent.isSome = true ∧
      [(objects p).val, (objects x).val] ∈ i.fields[fieldId v.core d .containment]?.getD []
  dereference : ∀ d x t, s.deref d x t ↔
    (v.core.get d).reference.target.isSome = true ∧
      [(objects x).val, (objects t).val] ∈ i.fields[fieldId v.core d .dereference]?.getD []

@[simp] theorem encode_objects (v : IR.Structural.Validated n) (o : Observation n) :
    (encode v o).signatures[0]? = some o.objects := rfl

@[simp] theorem encode_heads (v : IR.Structural.Validated n) (o : Observation n) (d : Fin n) :
    (encode v o).signatures[signatureId v d]? = some (o.heads d) := by
  simp only [encode, signatureId, Nat.add_comm 1, List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_idxOf (mem_order v d), Option.map_some]

@[simp] theorem encode_field (v : IR.Structural.Validated n) (o : Observation n)
    (d : Fin n) (role : FieldRole) (h : (d, role) ∈ fieldKeys v.core) :
    (encode v o).fields[fieldId v.core d role]? =
      some ((match role with | .containment => o.containment d | .dereference => o.dereference d).map
        fun (x, y) => [x, y]) := by
  cases role <;> simp [encode, fieldId, List.getElem?_idxOf, h]

@[simp] theorem mem_readPairs (ts : Relation) (x y : Nat) :
    (x, y) ∈ readPairs ts ↔ [x, y] ∈ ts := by
  simp only [readPairs, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, he⟩
    split at he <;> simp_all
  · intro h
    exact ⟨[x, y], h, rfl⟩

@[simp] theorem readPairs_map (ts : List (Nat × Nat)) :
    readPairs (ts.map fun (x, y) => [x, y]) = ts := by
  simp only [readPairs, List.filterMap_map]
  simp

/-- The map preserves individual reference heads, not only owner/target pairs. -/
theorem encode_dereference (v : IR.Structural.Validated n) (o : Observation n)
    (d t : Fin n) (h : (v.core.get d).reference.target = some t) (x y : Nat) :
    [x, y] ∈ (encode v o).fields[fieldId v.core d .dereference]?.getD [] ↔
      (x, y) ∈ o.dereference d := by
  rw [encode_field v o d .dereference ((dereference_inventory v.core d).mpr (by simp [h]))]
  simp

/-- Structural table hygiene only. It permits semantic violations (including
bad ownership, local/group counts, overlapping extents and set keys). -/
def TableWellFormed (v : IR.Structural.Validated n) (o : Observation n) : Prop :=
  o.objects.Nodup ∧ (∀ d, (o.heads d).Nodup) ∧
  (∀ d, (o.containment d).Nodup ∧ (o.dereference d).Nodup) ∧
  (∀ d, (v.core.get d).parent = none → o.containment d = []) ∧
  (∀ d, (v.core.get d).reference.target = none → o.dereference d = [])

theorem observation_encode (v : IR.Structural.Validated n) (o : Observation n)
    (hc : ∀ d, (v.core.get d).parent = none → o.containment d = [])
    (hd : ∀ d, (v.core.get d).reference.target = none → o.dereference d = []) :
    observation v (encode v o) o.root = o := by
  have cp : ∀ d, (observation v (encode v o) o.root).containment d = o.containment d := by
    intro d
    simp only [observation]
    cases hp : (v.core.get d).parent with
    | none => simp [hc d hp, readPairs]
    | some p =>
      simp only [Option.bind_some]
      rw [encode_field v o d .containment ((containment_inventory v.core d).mpr (by simp [hp]))]
      exact readPairs_map _
  have dr : ∀ d, (observation v (encode v o) o.root).dereference d = o.dereference d := by
    intro d
    simp only [observation]
    cases hp : (v.core.get d).reference.target with
    | none => simp [hd d hp, readPairs]
    | some p =>
      simp only [Option.bind_some]
      rw [encode_field v o d .dereference ((dereference_inventory v.core d).mpr (by simp [hp]))]
      exact readPairs_map _
  have hh : (observation v (encode v o) o.root).heads = o.heads := by
    funext d
    simp [observation]
  cases o
  change Observation.mk _ _ _ _ _ = Observation.mk _ _ _ _ _
  congr 1
  · exact funext cp
  · exact funext dr

theorem encode_wellFormed (v : IR.Structural.Validated n) (o : Observation n)
    (h : TableWellFormed v o) : (encode v o).wellFormed (schema v) = true := by
  have hn (ts : List (Nat × Nat)) (hn : ts.Nodup) :
      (ts.map fun (x, y) => [x, y]).Nodup :=
    hn.map (by intro a b hab; simpa [Prod.ext_iff] using hab)
  have hd (ts : List (Nat × Nat)) (ht : ts.Nodup) :
      ((ts.map fun (x, y) => [x, y]).eraseDups.length ==
        (ts.map fun (x, y) => [x, y]).length) = true := by
    rw [eraseDups_of_nodup (hn ts ht)]
    simp
  simp only [Instance.wellFormed, encode, schema, List.length_cons, List.length_map,
    beq_self_eq_true, List.all_cons, List.all_map, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [eraseDups_of_nodup h.1]; simp
  · exact List.all_eq_true.mpr (fun d _ => by simp [eraseDups_of_nodup (h.2.1 d)])
  · apply List.all_eq_true.mpr
    rintro ⟨d, role⟩ _
    cases role <;> simp only [Function.comp_apply, List.all_map, Bool.and_eq_true]
    · constructor
      · exact hd _ (h.2.2.1 d).1
      · simp
    · constructor
      · exact hd _ (h.2.2.1 d).2
      · simp

/-- Executable round trip retains even violating candidates. Its assumptions are
table hygiene, the chosen root singleton and root presence, not source truth. -/
theorem decode_encode (v : IR.Structural.Validated n) (o : Observation n)
    (h : TableWellFormed v o) (hr : o.heads v.core.root = [o.root])
    (hm : o.root ∈ o.objects) : decode v (encode v o) = .ok o := by
  simp only [decode, encode_wellFormed v o h, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, encode_heads, Option.getD_some, hr, encode_objects,
    List.contains_iff_mem.mpr hm, ↓reduceIte]
  rw [observation_encode v o h.2.2.2.1 h.2.2.2.2]

/-- Decode reports its actual data equations; it does not certify satisfaction. -/
theorem decode_success (v : IR.Structural.Validated n) (i : Instance) (o : Observation n)
    (h : decode v i = .ok o) :
    i.wellFormed (schema v) = true ∧ o.root ∈ o.objects ∧
    i.signatures[signatureId v v.core.root]?.getD [] = [o.root] ∧
    o = observation v i o.root := by
  unfold decode at h
  split at h
  · cases h
  · rename_i hw
    have hw' : i.wellFormed (schema v) = true := by simpa using hw
    split at h
    · rename_i root hr
      split at h
      · rename_i hm
        cases h
        exact ⟨hw', by simpa [observation] using hm, hr, rfl⟩
      · cases h
    · cases h

def observation_represents (v : IR.Structural.Validated n) (i : Instance) (root : Nat)
    (hr : i.signatures[signatureId v v.core.root]?.getD [] = [root])
    (hm : root ∈ i.signatures[0]?.getD []) (hw : i.wellFormed (schema v) = true)
    (hl : Live i) :
    Represents v (realize (observation v i root) hm) i := by
  refine ⟨hw, hl, Equiv.refl _, hr, ?_, ?_, ?_⟩
  · intro d x; rfl
  · intro d p x
    change (p.val, x.val) ∈ readPairs _ ↔ _
    rw [mem_readPairs]
    cases (v.core.get d).parent <;> simp
    rfl
  · intro d x t
    change (x.val, t.val) ∈ readPairs _ ↔ _
    rw [mem_readPairs]
    cases (v.core.get d).reference.target <;> simp
    rfl

/-- Changing source object labels preserves the concrete representation equations. -/
def Represents.rename {U V : Type} {v : IR.Structural.Validated n}
    {s : Clafer.Semantics.Configuration (Fin n) U} {i : Instance}
    (r : Represents v s i) (e : U ≃ V) :
    Represents v (s.rename e) i where
  wellFormed := r.wellFormed
  live := r.live
  objects := e.symm.trans r.objects
  root := by simpa [Clafer.Semantics.Configuration.rename] using r.root
  heads := by intro d x; exact r.heads d (e.symm x)
  containment := by intro d p x; exact r.containment d (e.symm p) (e.symm x)
  dereference := by intro d x t; exact r.dereference d (e.symm x) (e.symm t)

/-- A successful decoder constructs the concrete model relation, without a
caller-supplied bridge or a source-satisfaction assumption. -/
theorem decoded_represents (v : IR.Structural.Validated n) (i : Instance) (o : Observation n)
    (h : decode v i = .ok o) (hl : Live i) :
    ∃ hr : o.root ∈ o.objects, Nonempty (Represents v (realize o hr) i) := by
  obtain ⟨hw, hm, hr, ho⟩ := decode_success v i o h
  have hm' : o.root ∈ i.signatures[0]?.getD [] := by
    have ht := congrArg Observation.objects ho
    simpa only [ht, observation] using hm
  have he := observation_represents v i o.root hr hm' hw hl
  exact Eq.mpr (congrArg (fun q => ∃ hq : q.root ∈ q.objects,
    Nonempty (Represents v (realize q hq) i)) ho) ⟨hm', ⟨he⟩⟩

end ClaferCompiler.Correctness.Structural
