module

public import ClaferCompiler.Correctness.Behavioral.CompletionBounds
public import ClaferCompiler.Correctness.Behavioral.SnapshotCompletion

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral
open Encoding

-- [proof->req~compiler-behavioral-correctness~1]
/-- Bounded completeness for the actual compiler and concrete lasso encoder.
The finite-data assumptions constrain labels, duplicate rows, identity capacity,
source counts and lasso length. Source semantic obligations are stated directly. -/
theorem compiled_complete (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (source : IR.Behavioral.Lasso k o steps)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (refs : ∀ t, (source.at t).references.Nodup)
    (capacity : o ≤ b.objects)
    (scopeFits : SourceScopeFits v.structural.toLayout source.identities c.module.raw.command.scopes)
    (timeFits : b.minSteps ≤ steps ∧ steps ≤ b.maxSteps)
    (countFits : ∀ t, Structural.SourceCountFits v.structural.toLayout
      ((trace source).raw (SemanticsBridge.Structural.interpret v.document.core) t) b.bitwidth)
    (valid : (trace source).Valid (SemanticsBridge.Structural.interpret v.document.core))
    (attached : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f →
      Attached v.document.core (trace source) a.owner f) :
    (encode v.structural.toLayout source).Satisfies c.module.raw := by
  let rep := encode_rep v.structural.toLayout source unique valid.identities.root_type
    valid.identities.root_only
  have decl := encode_declarations v.structural.toLayout source unique refs valid.identities
  have typed := c.module.typed
  have bounded := c.module.bounded
  obtain ⟨scopes, _, hout, _, _⟩ := compile_output v b fuel enough c hc
  rw [hout] at scopeFits typed bounded ⊢
  have sw : (Backend.Alloy.Structural.schema v.structural.toLayout).wellFormed = true := by
    apply static_schema_wellFormed
    simp only [Temporal.Module.wellTyped, Temporal.Schema.wellFormed, Bool.and_eq_true] at typed
    exact typed.1.1.1.1.1
  refine ⟨?_, typed, bounded, decl, encode_inScope _ _ scopes unique scopeFits, ?_, trivial, trivial, ?_⟩
  · simpa [Temporal.Lasso.Fits, target, encode] using timeFits
  · intro fact hf
    simp only [target, List.mem_append] at hf
    rcases hf with (hi | hs) | ha
    · exact ⟨identityFacts_defined _ _ _ [] 0 fact hi,
        rep.identityFacts_complete b.bitwidth valid.identities fact hi⟩
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
      have hb := stateFacts_built v.structural.toLayout b.bitwidth
        (encode v.structural.toLayout source).unfold (decl.2.1 0).1 f hf
      have allTimes t := rep.stateFacts_complete b.bitwidth t sw
        (decl.2.1 t).1 (decl.2.1 t).2.1 valid (countFits t) f hf
      simp only [Temporal.Formula.Defined, Temporal.Formula.Holds,
        Temporal.Formula.fold_unary _ _ _ _ hb]
      exact ⟨fun t _ => (allTimes t).1, fun t _ => (allTimes t).2⟩
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, _, f, hf⟩ := admitted_attachment v a.val a.property
      rw [attachment_eq v b.objects fuel a (enough a.val a.property) f hf]
      refine ⟨attached_defined _ _ _ _ _ _ _ _ _ [] 0, ?_⟩
      apply (rep.attached_meaning b.bitwidth b.objects capacity
        (owner v.structural.toLayout a.val) f fuel (enough a.val a.property f hf)).mpr
      intro t x hx
      apply attached a.val a.property f hf t x
      · rw [← owner_id v a.val a.property, contexts_resolved v]
        exact hx
      · exact hx.1
  · intro t
    simp only [target, schema, Backend.Alloy.Structural.schema, Instance.scalarFields,
      List.zipIdx_cons, List.all_cons, Bool.and_eq_true]
    constructor
    · rfl
    · apply List.all_eq_true.mpr
      intro row hr
      obtain ⟨d, _, hd⟩ := List.mem_map.mp (List.fst_mem_of_mem_zipIdx hr)
      simp only [← hd]
      rfl

end ClaferCompiler.Correctness.Behavioral
