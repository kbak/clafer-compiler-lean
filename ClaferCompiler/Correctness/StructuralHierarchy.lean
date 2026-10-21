module

public import ClaferCompiler.Correctness.StructuralDecoding

public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

theorem declaration_siblings (s : Schema) (i : Instance)
    (h : i.declarations s = true) (k l : Nat) (a b : Signature)
    (hk : s.signatures[k]? = some a) (hl : s.signatures[l]? = some b)
    (hp : a.parent = b.parent) (x : Nat)
    (hx : x ∈ i.signatures[k]?.getD []) (hy : x ∈ i.signatures[l]?.getD []) : k = l := by
  have ha := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1
    (a, k) (List.mk_mem_zipIdx_iff_getElem?.mpr hk)
  simp only [Id.run, pure, Bool.and_eq_true] at ha
  have hb := List.all_eq_true.mp ha.1.2 (b, l) (List.mk_mem_zipIdx_iff_getElem?.mpr hl)
  by_contra hn
  simp only [hp, bne_self_eq_false, Bool.or_false,
    beq_eq_false_iff_ne.mpr hn, Bool.false_or] at hb
  have hx' := List.all_eq_true.mp hb x hx
  have hn' : x ∉ i.signatures[l]?.getD [] := by simpa using hx'
  exact hn' hy

/-- Follow occupied target signatures down the checked extends forest. -/
def OccupiedEdge (s : Schema) (i : Instance) (x : Nat) (p c : Nat) : Prop :=
  ∃ d, s.signatures[c]? = some d ∧ d.parent = some p ∧
    x ∈ i.signatures[c]?.getD []

theorem occupied_right_unique (s : Schema) (i : Instance) (x : Nat)
    (h : i.declarations s = true) : Relator.RightUnique (OccupiedEdge s i x) := by
  rintro p a b ⟨da, ha, hpa, hxa⟩ ⟨db, hb, hpb, hxb⟩
  exact declaration_siblings s i h a b da db ha hb (hpa.trans hpb.symm) x hxa hxb

theorem occupied_reachable (s : Schema) (i : Instance) (x : Nat)
    (sw : s.wellFormed = true) (hi : i.declarations s = true)
    (root : ∀ k d, s.signatures[k]? = some d → d.parent = none → k = 0)
    (k : Nat) (d : Signature) (hd : s.signatures[k]? = some d)
    (hx : x ∈ i.signatures[k]?.getD []) :
    Relation.ReflTransGen (OccupiedEdge s i x) 0 k := by
  induction k using Nat.strong_induction_on generalizing d with
  | h k ih =>
    cases hp : d.parent with
    | none => simpa [root k d hd hp] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (OccupiedEdge s i x) 0 0)
    | some p =>
      have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp sw).1
        (d, k) (List.mk_mem_zipIdx_iff_getElem?.mpr hd)
      have hpk : p < k := by simpa [hp] using hs
      have hps : p < s.signatures.length :=
        Nat.lt_trans hpk (List.getElem?_eq_some_iff.mp hd).1
      exact (ih p hpk s.signatures[p] (List.getElem?_eq_some_iff.mpr ⟨hps, rfl⟩)
        (declaration_included s i hi k p d hd hp x hx)).tail ⟨d, hd, hp, hx⟩

theorem signature_preimage (v : IR.Structural.Validated n) (k : Nat) (d : Signature)
    (hd : (schema v).signatures[k]? = some d) (hk : k ≠ 0) :
    ∃ c : Fin n, k = signatureId v c := by
  cases k with
  | zero => contradiction
  | succ k =>
    cases hc : (order v)[k]? with
    | none => simp [schema, hc] at hd
    | some c =>
      refine ⟨c, ?_⟩
      obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hc
      have hi := (order_nodup v).idxOf_getElem k hk
      rw [he] at hi
      simp [signatureId, hi, Nat.add_comm]

theorem signature_parent (v : IR.Structural.Validated n) (c p : Fin n) :
    some ((v.core.get c).super.map (signatureId v) |>.getD 0) = some (signatureId v p) ↔
      (v.core.get c).super = some p := by
  cases hc : (v.core.get c).super with
  | none => simp only [Option.map_none, Option.getD_none, Option.some.injEq,
      reduceCtorEq, iff_false]; exact Nat.ne_of_lt (signatureId_bounds v p).1
  | some d => simp [signatureId_injective v |>.eq_iff]

theorem occupied_source_path (v : IR.Structural.Validated n) (i : Instance) (x : Nat)
    (d : Fin n) {k : Nat}
    (h : Relation.ReflTransGen (OccupiedEdge (schema v) i x) (signatureId v d) k) :
    ∃ e, k = signatureId v e ∧ (interpret v.core).Ancestor e d := by
  induction h with
  | refl => exact ⟨d, rfl, .refl⟩
  | @tail b c path edge ih =>
    obtain ⟨e, rfl, he⟩ := ih
    obtain ⟨decl, hd, hp, _⟩ := edge
    have hc : c ≠ 0 := by
      intro hz
      subst c
      simp [schema] at hd
      subst decl
      cases hp
    obtain ⟨f, rfl⟩ := signature_preimage v c decl hd hc
    have hh := (schema_signature v f).symm.trans hd
    cases Option.some.inj hh
    have hf : (interpret v.core).Ancestor f e :=
      Relation.ReflTransGen.single ((signature_parent v f e).mp hp)
    exact ⟨f, rfl, hf.trans he⟩

/-- Sibling disjointness plus the actual finite extends forest derives global
source declaration comparability, including cousins at different depths. -/
theorem represented_disjoint {U : Type} (v : IR.Structural.Validated n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (sw : (schema v).wellFormed = true)
    (h : i.declarations (schema v) = true) :
    s.DeclarationDisjoint (interpret v.core) := by
  intro d e x hd he
  have pd := occupied_reachable _ i (r.objects x).val sw h (schema_parentless v)
    _ _ (schema_signature v d) ((r.heads d x).mp hd)
  have pe := occupied_reachable _ i (r.objects x).val sw h (schema_parentless v)
    _ _ (schema_signature v e) ((r.heads e x).mp he)
  rcases Relation.ReflTransGen.total_of_right_unique
    (occupied_right_unique _ i (r.objects x).val h) pd pe with hp | hp
  · obtain ⟨f, hf, ha⟩ := occupied_source_path v i _ d hp
    have hf := signatureId_injective v hf
    exact Or.inr (hf ▸ ha)
  · obtain ⟨f, hf, ha⟩ := occupied_source_path v i _ e hp
    have hf := signatureId_injective v hf
    exact Or.inl (hf ▸ ha)

end ClaferCompiler.Correctness.Structural
