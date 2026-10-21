module

public import ClaferCompiler.Correctness.StructuralRepresentation

public section
/-! [proof->req~compiler-structural-representation~1] -/

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural

/-- Read one declared signature, retaining its actual source super and flags. -/
theorem schema_signature (v : IR.Structural.Layout n) (d : Fin n) :
    (schema v).signatures[signatureId v d]? = some
      { parent := some ((v.core.get d).super.map (signatureId v) |>.getD 0)
        isAbstract := (v.core.get d).isAbstract } := by
  simp only [schema, signatureId, Nat.add_comm 1, List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_idxOf (mem_order v d), Option.map_some]

/-- The target's own declaration semantics enforces each extends inclusion. -/
theorem declaration_included (s : Schema) (i : Instance)
    (h : i.declarations s = true) (k p : Nat) (decl : Signature)
    (hk : s.signatures[k]? = some decl) (hp : decl.parent = some p)
    (x : Nat) (hx : x ∈ i.signatures[k]?.getD []) : x ∈ i.signatures[p]?.getD [] := by
  have hm : (decl, k) ∈ s.signatures.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hk
  simp only [Instance.declarations, Bool.and_eq_true] at h
  have hd := List.all_eq_true.mp h.1 (decl, k) hm
  simp only [Id.run, pure, hp, Option.all_some, Bool.and_eq_true] at hd
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hd.1.1.1 x hx)

/-- Every well-formed extent has the same cardinality as its tuple-set view. -/
theorem extent_card (s : Schema) (i : Instance) (hw : i.wellFormed s = true)
    (k : Nat) :
    (((i.signatures[k]?.getD []).map fun x => [x]).eraseDups).length =
      (i.signatures[k]?.getD []).length := by
  rw [eraseDups_map_injective (fun x : Nat => [x]) (by intro x y h; simpa using h)]
  simp only [List.length_map]
  cases hk : i.signatures[k]? with
  | none => rfl
  | some xs =>
    simp only [Instance.wellFormed, Bool.and_eq_true] at hw
    have hx := List.all_eq_true.mp hw.1.2 xs (List.mem_of_getElem? hk)
    simpa using hx

/-- The emitted singleton fact forces one actual root atom; a duplicate list
cannot disguise a larger raw extent because target well-formedness is included. -/
theorem satisfying_root (v : IR.Structural.Layout n) (scopes : List Scope)
    (w : Nat) (i : Instance) (h : Satisfies (target v scopes w) i) :
    ∃ root, i.signatures[signatureId v v.core.root]?.getD [] = [root] ∧
      root ∈ i.signatures[0]?.getD [] := by
  have hf := Module.fact_true (target v scopes w) i h.2.2.2.2.2
    (.mult .one (head v v.core.root)) (by
      exact List.mem_map.mpr ⟨_, root_generated v, rfl⟩)
  have hn : (i.signatures[signatureId v v.core.root]?.getD []).length = 1 := by
    change some (((i.signatures[signatureId v v.core.root]?.getD []).map fun x => [x]).eraseDups.length == 1)
      = some true at hf
    have hf := Option.some.inj hf
    rw [extent_card (schema v) i h.2.2.1] at hf
    exact beq_iff_eq.mp hf
  obtain ⟨root, hr⟩ := List.length_eq_one_iff.mp hn
  refine ⟨root, hr, ?_⟩
  have hp := v.coreChecked.2.2.1.2.2.1
  have hi := declaration_included (schema v) i h.2.2.2.1
    (signatureId v v.core.root) 0 _ (schema_signature v v.core.root)
    (by simp [hp]) root (by simp [hr])
  exact hi

/-- Target satisfaction alone is enough for the executable decoder to return.
No source predicate or supplied representation bridge is a premise. -/
theorem satisfying_decode (v : IR.Structural.Layout n) (scopes : List Scope)
    (w : Nat) (i : Instance) (h : Satisfies (target v scopes w) i) :
    ∃ o, decode v i = .ok o := by
  obtain ⟨root, hr, hm⟩ := satisfying_root v scopes w i h
  refine ⟨observation v i root, ?_⟩
  have hw : i.wellFormed (schema v) = true := h.2.2.1
  simp [decode, hw, hr, hm]

/-- This theorem applies to the actual successful compiler output. -/
theorem compiled_decode (v : IR.Structural.Validated n) (b : Structural.Bounds)
    (c : Compiled) (hc : compile v b = .ok c) (i : Instance)
    (h : Satisfies c.module.raw i) : ∃ o, decode v.toLayout i = .ok o := by
  obtain ⟨scopes, _, he, _, _⟩ := compile_output v b c hc
  rw [he] at h
  exact satisfying_decode v.toLayout scopes b.bitwidth i h

/-- The generated object-union signature is the only signature without a parent. -/
theorem schema_parentless (v : IR.Structural.Layout n) (k : Nat) (d : Signature)
    (hd : (schema v).signatures[k]? = some d) (hp : d.parent = none) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    cases hk : (order v)[k]? with
    | none => simp [schema, hk] at hd
    | some c =>
      simp only [schema, List.getElem?_cons_succ, List.getElem?_map, hk, Option.map_some,
        Option.some.injEq] at hd
      subst d
      cases hp

/-- A finite ordered extends forest with one root keeps every declared atom in
that root. This uses target inclusion and the target's own checked parent order. -/
theorem declarations_live (s : Schema) (i : Instance)
    (sw : s.wellFormed = true) (iw : i.wellFormed s = true)
    (id : i.declarations s = true)
    (root : ∀ (k : Nat) (d : Signature), s.signatures[k]? = some d → d.parent = none → k = 0) : Live i := by
  have il : i.signatures.length = s.signatures.length ∧ i.fields.length = s.fields.length := by
    simp only [Instance.wellFormed, Bool.and_eq_true, beq_iff_eq] at iw
    exact iw.1.1
  have included : ∀ (k : Nat) (d : Signature), s.signatures[k]? = some d →
      ∀ x ∈ i.signatures[k]?.getD [], x ∈ i.signatures[0]?.getD [] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd x hx
      by_cases hz : k = 0
      · simpa [hz] using hx
      cases hp : d.parent with
      | none => exact (hz (root k d hd hp)).elim
      | some p =>
        have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp sw).1
          (d, k) (List.mk_mem_zipIdx_iff_getElem?.mpr hd)
        have hpk : p < k := by simpa [hp] using hs
        have hk := (List.getElem?_eq_some_iff.mp hd).1
        have hps : p < s.signatures.length := Nat.lt_trans hpk hk
        exact ih p hpk s.signatures[p] (List.getElem?_eq_some_iff.mpr ⟨hps, rfl⟩) x
          (declaration_included s i id k p d hd hp x hx)
  have allsig : ∀ xs ∈ i.signatures, ∀ x ∈ xs, x ∈ i.signatures[0]?.getD [] := by
    intro xs hxs x hx
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hxs
    have hs : k < s.signatures.length := by simpa only [il.1] using hk
    exact included k s.signatures[k] (List.getElem?_eq_some_iff.mpr ⟨hs, rfl⟩) x
      (by simpa only [List.getElem?_eq_some_iff.mpr ⟨hk, he⟩, Option.getD_some] using hx)
  refine ⟨allsig, ?_⟩
  intro ts hts tuple ht x hx
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hts
  have hsf : k < s.fields.length := by simpa only [il.2] using hk
  let f := s.fields[k]
  have hf : (f, k) ∈ s.fields.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr
    (List.getElem?_eq_some_iff.mpr ⟨hsf, rfl⟩)
  have hfd := List.all_eq_true.mp (Bool.and_eq_true_iff.mp id).2 (f, k) hf
  have htp := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hfd).1 tuple (by simpa only [List.getElem?_eq_some_iff.mpr ⟨hk, he⟩, Option.getD_some] using ht)
  split at htp
  · rename_i _ a b
    have ha := List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp htp).1
    have hb := List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp htp).2
    have ma : a ∈ i.signatures[0]?.getD [] := by
      cases ho : i.signatures[f.owner]? with
      | none => simp [ho] at ha
      | some xs => exact allsig xs (List.mem_of_getElem? ho) a (by simpa [ho] using ha)
    have mb : b ∈ i.signatures[0]?.getD [] := by
      cases ho : i.signatures[f.target]? with
      | none => simp [ho] at hb
      | some xs => exact allsig xs (List.mem_of_getElem? ho) b (by simpa [ho] using hb)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · contradiction

/-- No target atom outside the live carrier is hidden by source interpretation. -/
theorem satisfying_live (v : IR.Structural.Layout n) (scopes : List Scope)
    (w : Nat) (i : Instance) (h : Satisfies (target v scopes w) i) : Live i := by
  have sw : (schema v).wellFormed = true := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp h.1).1).1
  exact declarations_live (schema v) i sw h.2.2.1 h.2.2.2.1 (schema_parentless v)

/-- Satisfaction constructs the actual decoder output and the complete concrete
representation, with atom coverage derived from target declarations. -/
theorem compiled_representation (v : IR.Structural.Validated n) (b : Structural.Bounds)
    (c : Compiled) (hc : compile v b = .ok c) (i : Instance)
    (h : Satisfies c.module.raw i) :
    ∃ o, decode v.toLayout i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Represents v.toLayout (realize o hr) i) := by
  obtain ⟨scopes, _, he, _, _⟩ := compile_output v b c hc
  rw [he] at h
  obtain ⟨o, ho⟩ := satisfying_decode v.toLayout scopes b.bitwidth i h
  exact ⟨o, ho, decoded_represents v.toLayout i o ho (satisfying_live v.toLayout scopes b.bitwidth i h)⟩

end ClaferCompiler.Correctness.Structural
