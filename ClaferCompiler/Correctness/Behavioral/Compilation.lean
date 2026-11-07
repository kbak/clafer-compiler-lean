module

public import ClaferCompiler.Backend.Alloy.Behavioral.Compile
public import ClaferCompiler.Backend.Alloy.Temporal.Semantics
public import ClaferCompiler.Correctness.StructuralGeneration

public section
namespace ClaferCompiler.Correctness.Behavioral.Encoding
open Backend.Alloy
open Backend.Alloy.Behavioral

-- [proof->req~compiler-behavioral-encoding~1]
/-- Compilation returns this generated target and its exact source inventory.
The statement contains no target or source satisfaction premise. -/
theorem compile_output (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (h : compile v b fuel enough = .ok c) :
    ∃ scopes, Structural.resolveScopes v.structural.toLayout b.toBounds = .ok scopes ∧
      c.module.raw = target v b scopes fuel enough ∧
      c.declarations = (List.finRange k).map (declarationMap v.structural.toLayout) ∧
      c.attachments = v.document.attachments.map (·.id) := by
  unfold compile at h
  cases hs : Structural.resolveScopes v.structural.toLayout b.toBounds with
  | error e => simp [hs, bind, Except.bind] at h
  | ok scopes =>
    simp only [hs, bind, Except.bind] at h
    cases hc : Temporal.check (target v b scopes fuel enough) with
    | error e => cases e <;> simp [hc] at h
    | ok checked =>
      simp only [hc, Except.ok.injEq] at h
      subst c
      refine ⟨scopes, rfl, ?_, rfl, rfl⟩
      unfold Temporal.check at hc
      split at hc
      · split at hc
        · cases hc; rfl
        · cases hc
      · cases hc

theorem compiled_checked (c : Compiled) :
    c.module.raw.wellTyped = true ∧ c.module.raw.safeBounds = true :=
  ⟨c.module.typed, c.module.bounded⟩

theorem declarationMap_preserves (v : IR.Structural.Layout k) (d : Fin k) :
    (declarationMap v d).id = (v.core.get d).id ∧
    (declarationMap v d).name = (v.core.get d).name ∧
    (declarationMap v d).source = (v.core.get d).source ∧
    (declarationMap v d).signature = Structural.signatureId v d ∧
    (declarationMap v d).containment = (v.core.get d).parent.map (fun _ => contains v d) ∧
    (declarationMap v d).dereference = (v.core.get d).reference.target.map (fun _ => 2 + d.val) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem owner_matches (v : IR.Structural.Layout k) (a : IR.Behavioral.Attachment k)
    (d : Fin k) (hd : (v.core.get d).id = a.owner) : owner v a = d := by
  unfold owner
  cases hf : (List.finRange k).find? (fun e => (v.core.get e).id == a.owner) with
  | none =>
      have hn := List.find?_eq_none.mp hf d (List.mem_finRange d)
      simp [hd] at hn
  | some e =>
      have he := List.find?_some hf
      have eq : e = d := v.coreChecked.1 e d (by simpa [hd] using he)
      simp [eq]

theorem owner_id (v : IR.Behavioral.Admitted k) (a : IR.Behavioral.Attachment k)
    (ha : a ∈ v.document.attachments) :
    (v.document.core.get (owner v.structural.toLayout a)).id = a.owner := by
  obtain ⟨d, hd⟩ := (v.metadataChecked.2.1 a ha).1
  rw [owner_matches v.structural.toLayout a d hd]
  exact hd

theorem attachment_eq (v : IR.Behavioral.Admitted k) (capacity fuel : Nat)
    (a : {a // a ∈ v.document.attachments})
    (enough : ∀ f, a.val.body = .formula f → sizeOf f < fuel)
    (f : IR.Behavioral.Formula k 0) (hf : a.val.body = .formula f) :
    attachment v capacity fuel a enough =
      attached v.structural.toLayout capacity (owner v.structural.toLayout a.val)
        f fuel (enough f hf) := by
  unfold attachment
  split
  · rename_i g hg
    have hfg := IR.Behavioral.RequestedBody.formula.inj (hf.symm.trans hg)
    subst g
    rfl
  · rename_i name hg
    cases hf.symm.trans hg

-- [proof->req~compiler-behavioral-encoding~1]
theorem identity_generated (v : IR.Behavioral.Admitted k) (b : Bounds)
    (scopes : List Scope) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (f : Temporal.Formula) (hf : f ∈ identityFacts v.structural.toLayout) :
    f ∈ (target v b scopes fuel enough).facts := by
  simp only [target, List.mem_append]
  exact Or.inl (Or.inl hf)

theorem state_generated (v : IR.Behavioral.Admitted k) (b : Bounds)
    (scopes : List Scope) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (f : Temporal.Formula) (hf : f ∈ stateFacts v.structural.toLayout) :
    Temporal.Formula.unary .always f ∈ (target v b scopes fuel enough).facts := by
  simp only [target, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨f, hf, rfl⟩))

theorem attachment_generated (v : IR.Behavioral.Admitted k) (b : Bounds)
    (scopes : List Scope) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (a : IR.Behavioral.Attachment k) (ha : a ∈ v.document.attachments) :
    attachment v b.objects fuel ⟨a, ha⟩ (enough a ha) ∈
      (target v b scopes fuel enough).facts := by
  simp only [target, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨⟨a, ha⟩, by simp, rfl⟩)

-- [proof->req~compiler-behavioral-correctness~1]
theorem compiled_identity_holds (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (τ : Temporal.Trace) (hs : Temporal.Satisfies c.module.raw τ)
    (f : Temporal.Formula) (hf : f ∈ identityFacts v.structural.toLayout) :
    f.Holds (schema v.structural.toLayout) b.bitwidth τ [] 0 := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at hs
  exact (hs.2.2.2.2.1 _ (identity_generated v b scopes fuel enough f hf)).2

theorem compiled_attachment_holds (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (τ : Temporal.Trace) (hs : Temporal.Satisfies c.module.raw τ)
    (a : IR.Behavioral.Attachment k) (ha : a ∈ v.document.attachments)
    (f : IR.Behavioral.Formula k 0) (hf : a.body = .formula f) :
    (attached v.structural.toLayout b.objects (owner v.structural.toLayout a)
      f fuel (enough a ha f hf)).Holds (schema v.structural.toLayout) b.bitwidth τ [] 0 := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at hs
  have h := (hs.2.2.2.2.1 _ (attachment_generated v b scopes fuel enough a ha)).2
  rw [attachment_eq v b.objects fuel ⟨a, ha⟩ (enough a ha) f hf] at h
  exact h

/-- Satisfying the actual output entails every generated source-state clause
at every natural time, once its ordinary target syntax is well-built. -/
theorem compiled_state_holds (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (τ : Temporal.Trace) (hs : Temporal.Satisfies c.module.raw τ)
    (f : Temporal.Formula) (hf : f ∈ stateFacts v.structural.toLayout)
    (hb : f.Built) (t : Nat) :
    f.Holds (schema v.structural.toLayout) b.bitwidth τ [] t := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at hs
  have h := (hs.2.2.2.2.1 _ (state_generated v b scopes fuel enough f hf)).2
  change (Temporal.Formula.unary .always f).Holds (schema v.structural.toLayout)
    b.bitwidth τ [] 0 at h
  simp only [Temporal.Formula.Holds, Temporal.Formula.fold_unary _ _ _ _ hb] at h
  exact h t (Nat.zero_le t)

theorem compiled_state_defined (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (τ : Temporal.Trace) (hs : Temporal.Satisfies c.module.raw τ)
    (f : Temporal.Formula) (hf : f ∈ stateFacts v.structural.toLayout)
    (hb : f.Built) (t : Nat) :
    f.Defined (schema v.structural.toLayout) b.bitwidth τ [] t := by
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at hs
  have h := (hs.2.2.2.2.1 _ (state_generated v b scopes fuel enough f hf)).1
  change (Temporal.Formula.unary .always f).Defined (schema v.structural.toLayout)
    b.bitwidth τ [] 0 at h
  simp only [Temporal.Formula.Defined, Temporal.Formula.fold_unary _ _ _ _ hb] at h
  exact h t (Nat.zero_le t)

end ClaferCompiler.Correctness.Behavioral.Encoding
