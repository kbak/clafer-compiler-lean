module

public import ClaferCompiler.Backend.Alloy.Structural
public import Mathlib.Data.List.Basic

public section

namespace ClaferCompiler.Backend.Alloy.Structural

/-! Local generation and inventory proofs. Global source preservation is #11.
[proof->req~compiler-structural-encoding~1] -/

theorem order_perm (v : IR.Structural.Validated n) : List.Perm (order v) (List.finRange n) :=
  List.mergeSort_perm _ _

theorem mem_order (v : IR.Structural.Validated n) (d : Fin n) : d ∈ order v :=
  (order_perm v).mem_iff.mpr (List.mem_finRange d)

theorem order_nodup (v : IR.Structural.Validated n) : (order v).Nodup :=
  (order_perm v).nodup_iff.mpr (List.nodup_finRange n)

theorem order_length (v : IR.Structural.Validated n) : (order v).length = n := by
  simpa using (order_perm v).length_eq

theorem signatureId_bounds (v : IR.Structural.Validated n) (d : Fin n) :
    0 < signatureId v d ∧ signatureId v d < n + 1 := by
  have h := List.idxOf_lt_length_of_mem (mem_order v d)
  rw [order_length] at h
  simp only [signatureId]
  omega

theorem signatureId_injective (v : IR.Structural.Validated n) :
    Function.Injective (signatureId v) := by
  intro d e h
  exact (List.idxOf_inj (mem_order v d)).mp (Nat.add_left_cancel h)

theorem signature_inventory (v : IR.Structural.Validated n) :
    (schema v).signatures.length = n + 1 := by
  simp [schema, order_length]

theorem nameMap_inventory (v : IR.Structural.Validated n) :
    nameMap v = (List.finRange n).map (declarationMap v) ∧ (nameMap v).length = n := by
  simp [nameMap]

theorem declarationMap_preserves (v : IR.Structural.Validated n) (d : Fin n) :
    (declarationMap v d).id = (v.core.get d).id ∧
    (declarationMap v d).name = (v.core.get d).name ∧
    (declarationMap v d).source = (v.core.get d).source ∧
    (declarationMap v d).signature = signatureId v d := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem containment_inventory (m : IR.Structural.Core n) (d : Fin n) :
    (d, FieldRole.containment) ∈ fieldKeys m ↔ (m.get d).parent.isSome = true := by
  simp [fieldKeys, List.mem_flatMap, Prod.ext_iff]
  cases (m.get d).parent <;> simp

theorem dereference_inventory (m : IR.Structural.Core n) (d : Fin n) :
    (d, FieldRole.dereference) ∈ fieldKeys m ↔ (m.get d).reference.target.isSome = true := by
  simp [fieldKeys, List.mem_flatMap, Prod.ext_iff]
  cases (m.get d).reference.target <;> simp

theorem fieldId_bounds (m : IR.Structural.Core n) (d : Fin n) (role : FieldRole)
    (h : (d, role) ∈ fieldKeys m) : fieldId m d role < (fieldKeys m).length :=
  List.idxOf_lt_length_of_mem h

theorem fieldId_injective (m : IR.Structural.Core n) (a b : Fin n × FieldRole)
    (ha : a ∈ fieldKeys m) (h : fieldId m a.1 a.2 = fieldId m b.1 b.2) : a = b :=
  (List.idxOf_inj ha).mp h

theorem field_lookup (v : IR.Structural.Validated n) (d : Fin n) (role : FieldRole)
    (h : (d, role) ∈ fieldKeys v.core) :
    (schema v).fields[fieldId v.core d role]? = some (fieldDeclaration v (d, role)) := by
  simp [schema, fieldId, List.getElem?_idxOf, h]

theorem containment_direction (v : IR.Structural.Validated n) (d p : Fin n)
    (h : (v.core.get d).parent = some p) :
    (schema v).fields[fieldId v.core d .containment]? =
      some ⟨signatureId v p, signatureId v d, .set⟩ := by
  rw [field_lookup v d .containment ((containment_inventory v.core d).mpr (by simp [h]))]
  simp [fieldDeclaration, h]

theorem dereference_direction (v : IR.Structural.Validated n) (d t : Fin n)
    (h : (v.core.get d).reference.target = some t) :
    (schema v).fields[fieldId v.core d .dereference]? =
      some ⟨signatureId v d, signatureId v t, .one⟩ := by
  rw [field_lookup v d .dereference ((dereference_inventory v.core d).mpr (by simp [h]))]
  simp [fieldDeclaration, h]

theorem child_inventory (m : IR.Structural.Core n) (d c : Fin n) :
    c ∈ children m d ↔ (m.get c).parent = some d := by
  simp [children]

theorem subtype_inventory (m : IR.Structural.Core n) (d c : Fin n) :
    c ∈ subtypes m d ↔ (m.get c).super = some d := by
  simp [subtypes]

theorem root_generated (v : IR.Structural.Validated n) :
    (Obligation.root, Formula.mult .one (head v v.core.root)) ∈ facts v := by
  simp [facts]

theorem object_cover_generated (v : IR.Structural.Validated n) :
    (Obligation.objectCover,
      Formula.equal (.sig 0) (union ((List.finRange n).map (head v)))) ∈ facts v := by
  simp [facts]

theorem declaration_fact_generated (v : IR.Structural.Validated n) (d : Fin n)
    (fact : Obligation × Formula) (h : fact ∈ declarationFacts v d) : fact ∈ facts v := by
  simp only [facts, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, List.mem_finRange d, h⟩

theorem abstract_cover_generated (v : IR.Structural.Validated n) (d : Fin n)
    (h : (v.core.get d).isAbstract = true) :
    (.abstractCover (v.core.get d).id,
      Formula.equal (head v d) (union ((subtypes v.core d).map (head v)))) ∈ facts v := by
  apply declaration_fact_generated v d
  simp [declarationFacts, h]

theorem ownership_generated (v : IR.Structural.Validated n) (d p : Fin n)
    (h : (v.core.get d).parent = some p) :
    (.ownership (v.core.get d).id, ownership v d) ∈ facts v := by
  apply declaration_fact_generated v d
  simp [declarationFacts, h]

theorem local_bounds_generated (v : IR.Structural.Validated n) (d p : Fin n)
    (h : (v.core.get d).parent = some p) :
    (.localBounds (v.core.get d).id,
      Formula.all (head v p)
        (interval (v.core.get d).localBounds (.join (.var 0) (contains v.core d)))) ∈ facts v := by
  apply declaration_fact_generated v d
  simp [declarationFacts, h]

theorem group_generated (v : IR.Structural.Validated n) (d : Fin n)
    (h : (v.core.get d).isAbstract = false) :
    (.groupBounds (v.core.get d).id,
      Formula.all (head v d) (interval (v.core.get d).groupBounds (childHeads v.core d))) ∈ facts v := by
  apply declaration_fact_generated v d
  simp [declarationFacts, h]

theorem set_key_generated (v : IR.Structural.Validated n) (d p t : Fin n)
    (hp : (v.core.get d).parent = some p) (hr : (v.core.get d).reference = .set t) :
    (.setKey (v.core.get d).id, setKey v d p) ∈ facts v := by
  apply declaration_fact_generated v d
  simp [declarationFacts, hp, hr]

theorem compiled_checked (c : Compiled) :
    c.module.raw.wellTyped = true ∧ c.module.raw.safeBounds = true :=
  ⟨c.module.typed, c.module.bounded⟩

/-- Successful compilation returns the generated module and the entire inventory,
not merely a checked but unrelated target. No preservation premise is assumed. -/
theorem compile_output (v : IR.Structural.Validated n) (b : Bounds) (c : Compiled)
    (h : compile v b = .ok c) :
    ∃ scopes, resolveScopes v b = .ok scopes ∧ c.module.raw = target v scopes b.bitwidth ∧
      c.declarations = nameMap v ∧ c.obligations = (facts v).map Prod.fst := by
  unfold compile at h
  cases hs : resolveScopes v b with
  | error e => simp [hs, bind, Except.bind] at h
  | ok scopes =>
    simp only [hs, bind, Except.bind] at h
    cases hc : check (target v scopes b.bitwidth) with
    | error e => cases e <;> simp [hc] at h
    | ok checked =>
      simp only [hc, Except.ok.injEq] at h
      subst c
      refine ⟨scopes, rfl, ?_, rfl, rfl⟩
      unfold check at hc
      split at hc
      · split at hc
        · cases hc; rfl
        · cases hc
      · cases hc

end ClaferCompiler.Backend.Alloy.Structural
