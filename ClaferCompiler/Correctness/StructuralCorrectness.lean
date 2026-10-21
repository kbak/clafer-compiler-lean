module

public import ClaferCompiler.Correctness.StructuralCompletionDeclarations
public import ClaferCompiler.Correctness.StructuralSourceObservation
public import Clafer.Semantics.Bridge
public import Clafer.Semantics.Normalization
public import Mathlib.SetTheory.Cardinal.Finite

/-! M1 preservation with explicit finite scope and integer observation hypotheses.
[proof->req~compiler-structural-correctness~1] -/

@[expose] public section

namespace ClaferCompiler.Correctness.Structural
open Backend.Alloy Backend.Alloy.Structural SemanticsBridge.Structural

/-- The complete explicit target scope vector applied only to source observation
counts in declaration order. No declarations, generated facts, source truth or
target truth is tested here. Compilation checks the scope inventory separately. -/
def ObservationScopesFit (v : IR.Structural.Layout n) (scopes : List Scope)
    (o : Observation n) : Prop :=
  ∀ entry ∈ scopes.zip (o.objects :: (order v).map o.heads),
    if entry.1.exact then entry.2.length = entry.1.size else entry.2.length ≤ entry.1.size

theorem observation_inScope (v : IR.Structural.Layout n) (scopes : List Scope)
    (o : Observation n) :
    (encode v o).inScope scopes = true ↔ ObservationScopesFit v scopes o := by
  unfold Instance.inScope encode ObservationScopesFit
  rw [List.all_eq_true]
  apply forall_congr'
  intro entry
  apply imp_congr_right
  intro _
  split; simp

theorem source_object_count {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) :
    (sourceObservation s).objects.length = Fintype.card U := by
  classical
  simp [sourceObservation, Finset.card_image_of_injective _ sourceLabel_injective]

theorem source_head_count {U : Type} [Fintype U]
    (s : Clafer.Semantics.Configuration (Fin n) U) (d : Fin n) :
    ((sourceObservation s).heads d).length = Nat.card (s.head d) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [sourceObservation, Finset.card_image_of_injective _ sourceLabel_injective,
    Fintype.card_subtype]

/-- Completeness under concrete representation equations, finite source counts,
manual scopes and explicitly representable observations. -/
theorem represented_complete {U : Type} [Fintype U] (v : IR.Structural.Layout n)
    (s : Clafer.Semantics.Configuration (Fin n) U) (i : Instance)
    (r : Represents v s i) (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s)
    (scopes : List Scope) (w : Nat) (typed : (target v scopes w).wellTyped = true)
    (bounded : (target v scopes w).safeBounds = true)
    (scopeFits : i.inScope scopes = true) (countFits : SourceCountFits v s w) :
    Satisfies (target v scopes w) i :=
  ⟨typed, bounded, r.wellFormed, source_declarations v s i r h, scopeFits,
    source_module_eval v s i r h scopes w countFits⟩

/-- Every finite admitted source model fitting the explicit manual scopes and
integer observation ranges has an actual satisfying encoded target instance.
The construction retains every object and every reference occurrence. -/
theorem compiled_complete {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (b : Structural.Bounds) (c : Compiled) (hc : compile v b = .ok c)
    (s : Clafer.Semantics.Configuration (Fin n) U)
    (h : Clafer.Semantics.StructuralSatisfies (interpret v.core) s)
    (scopes : ObservationScopesFit v.toLayout c.module.raw.command.scopes (sourceObservation s))
    (counts : SourceCountFits v.toLayout s b.bitwidth) :
    ∃ i, encode v.toLayout (sourceObservation s) = i ∧ Nonempty (Represents v.toLayout s i) ∧
      Satisfies c.module.raw i := by
  let i := encode v.toLayout (sourceObservation s)
  let r := source_represents v.toLayout s h.1 h.2.1
  refine ⟨i, rfl, ⟨r⟩, ?_⟩
  obtain ⟨qs, _, he, _, _⟩ := compile_output v b c hc
  have typed := c.module.typed
  have bounded := c.module.bounded
  rw [he] at scopes typed bounded ⊢
  exact represented_complete v.toLayout s i r h qs b.bitwidth typed bounded
    ((observation_inScope v.toLayout qs _).mpr scopes) counts

/-- Composition with the existing independent local bank retains every global
root, abstract, group and declaration-disjointness obligation explicitly. -/
theorem compiled_sound_bank (v : IR.Structural.Validated n) (b : Structural.Bounds)
    (c : Compiled) (hc : compile v b = .ok c) (i : Instance)
    (h : Satisfies c.module.raw i) :
    ∃ o, decode v.toLayout i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Represents v.toLayout (realize o hr) i) ∧
      (realize o hr).Typed (interpret v.core) ∧
      (realize o hr).GlobalConditions (interpret v.core) ∧
      (DPGraph.Predicates.interpretation (Objects o)).IsModel
        (Clafer.Compile.localFormulas (interpret v.core).family).diagram
        ((realize o hr).interpret (interpret v.core)) := by
  obtain ⟨o, ho, hr, r, hs⟩ := compiled_sound v b c hc i h
  exact ⟨o, ho, hr, r, ((realize o hr).structural_model_iff _
    (validated_domain v).1 (validated_domain v).2).mp hs⟩

/-- An actual constraint-free compiled source bank can be used as the source
premise. The erasure equation is data equality, not a supplied truth bridge. -/
theorem compiled_complete_bank {a : Clafer.AST} (input : Clafer.Compile.Input a)
    (free : Clafer.Semantics.ConstraintFree a) {U : Type} [Fintype U]
    (v : IR.Structural.Validated a.entries.length)
    (erased : interpret v.core = Clafer.Semantics.EffectiveCore.erase input)
    (b : Structural.Bounds) (c : Compiled) (hc : compile v b = .ok c)
    (s : Clafer.Semantics.Configuration a.Occurrence U)
    (h : Clafer.Semantics.SatisfiesAST input free s)
    (scopes : ObservationScopesFit v.toLayout c.module.raw.command.scopes (sourceObservation s))
    (counts : SourceCountFits v.toLayout s b.bitwidth) :
    ∃ i, encode v.toLayout (sourceObservation s) = i ∧ Nonempty (Represents v.toLayout s i) ∧
      Satisfies c.module.raw i := by
  apply compiled_complete v b c hc s _ scopes counts
  rw [erased]
  exact (Clafer.Semantics.erasure_correspondence input free
    (erased ▸ (validated_domain v).2) s).mp h

/-- Arbitrary source span/link carriers are normalized by the pinned upstream
theorem. Only this concrete model carrier is finite; DPGraph stays unrestricted. -/
theorem normalized_complete {U : Type} [Fintype U] (v : IR.Structural.Validated n)
    (b : Structural.Bounds) (c : Compiled) (hc : compile v b = .ok c)
    (g : (interpret v.core).family.canonicalRoles.graph ⥤q DPGraph.Predicates.semanticGraph.{0,0} U)
    (root : U)
    (model : (DPGraph.Predicates.interpretation U).IsModel
      (Clafer.Compile.localFormulas (interpret v.core).family).diagram g)
    (global : (Clafer.Semantics.SpanModel.normalize (interpret v.core) g root).GlobalConditions
      (interpret v.core))
    (scopes : ObservationScopesFit v.toLayout c.module.raw.command.scopes
      (sourceObservation (Clafer.Semantics.SpanModel.normalize (interpret v.core) g root)))
    (counts : SourceCountFits v.toLayout (Clafer.Semantics.SpanModel.normalize (interpret v.core) g root) b.bitwidth) :
    ∃ i, encode v.toLayout (sourceObservation (Clafer.Semantics.SpanModel.normalize (interpret v.core) g root)) = i ∧
      Nonempty (Represents v.toLayout (Clafer.Semantics.SpanModel.normalize (interpret v.core) g root) i) ∧
      Satisfies c.module.raw i :=
  compiled_complete v b c hc _
    (Clafer.Semantics.SpanModel.normalize_satisfies (interpret v.core) g root model
      (validated_domain v).1 (validated_domain v).2 global) scopes counts

end ClaferCompiler.Correctness.Structural
