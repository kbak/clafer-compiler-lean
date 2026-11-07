module

public import ClaferCompiler.Correctness.Behavioral.Completion
public import ClaferCompiler.Correctness.Behavioral.RepresentationCompletion
public import ClaferCompiler.Correctness.Behavioral.StaticReduction

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

-- [proof->req~compiler-trace-representation~1]
/-- Encoding and actual decoding preserve the whole trace observation under a
global correspondence. Only identity and finite-table hygiene is needed here;
source snapshot validity and attachment truth are not assumed. -/
theorem encoded_decodes (v : IR.Structural.Layout k)
    (source : IR.Behavioral.Lasso k o steps)
    (hw : (schema v).declarations.wellFormed = true)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (refs : ∀ t, (source.at t).references.Nodup)
    (identities : (trace source).identities.Valid (SemanticsBridge.Structural.interpret v.core)) :
    ∃ decoded : Σ o steps, IR.Behavioral.Lasso k o steps,
      decode v (encode v source) = .ok decoded ∧
      Nonempty (TraceRep v decoded.2.2 (encode v source)) := by
  let rep := encode_rep v source unique identities.root_type identities.root_only
  obtain ⟨decoded, hd⟩ := target_decode_exists v 0 (encode v source) hw
    (encode_declarations v source unique refs identities)
    (rep.identityFacts_complete 0 identities)
  exact ⟨decoded, hd, ⟨decode_rep v (encode v source) decoded hd⟩⟩

-- [proof->req~compiler-behavioral-correctness~1]
/-- Soundness of the actual successful compiler output constructs executable
decoder success and one concrete global representation, then derives upstream
validity and every attachment. No source trace or preservation adapter is assumed. -/
theorem compiled_sound (v : IR.Behavioral.Admitted k) (b : Bounds) (fuel : Nat)
    (enough : ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f → sizeOf f < fuel)
    (c : Compiled) (hc : compile v b fuel enough = .ok c)
    (target : Temporal.Lasso) (sat : target.Satisfies c.module.raw) :
    ∃ decoded : Σ o steps, IR.Behavioral.Lasso k o steps,
      decode v.structural.toLayout target = .ok decoded ∧
      Nonempty (TraceRep v.structural.toLayout decoded.2.2 target) ∧
      (trace decoded.2.2).Valid (SemanticsBridge.Structural.interpret v.document.core) ∧
      ∀ a ∈ v.document.attachments, ∀ f, a.body = .formula f →
        Attached v.document.core (trace decoded.2.2) a.owner f := by
  have hw : (schema v.structural.toLayout).declarations.wellFormed = true := by
    have typed := c.module.typed
    obtain ⟨scopes, _, hout, _, _⟩ := Encoding.compile_output v b fuel enough c hc
    rw [hout] at typed
    simp only [Temporal.Module.wellTyped, Temporal.Schema.wellFormed, Bool.and_eq_true] at typed
    exact typed.1.1.1.1.1
  obtain ⟨decoded, hd⟩ := target_decode_exists v.structural.toLayout b.bitwidth target hw
    (Encoding.compiled_declarations v b fuel enough c hc target.unfold sat.2)
    (Encoding.compiled_identity_holds v b fuel enough c hc target.unfold sat.2)
  let rep := decode_rep v.structural.toLayout target decoded hd
  have unique := (roundTrip_data v.structural.toLayout decoded.2.2 target
    (decode_checked v.structural.toLayout target decoded hd)).2.2.1
  refine ⟨decoded, hd, ⟨rep⟩, rep.compiled_valid b fuel enough c hc sat.2 unique, ?_⟩
  intro a ha f hf
  exact rep.compiled_attached b (rep.compiled_capacity b fuel enough c hc sat.2)
    fuel enough c hc sat.2 a ha f hf

end ClaferCompiler.Correctness.Behavioral
