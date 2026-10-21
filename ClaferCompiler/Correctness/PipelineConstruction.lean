module

public import ClaferCompiler.Driver.Source
public import ClaferCompiler.SemanticsBridge.Resolution
public import ClaferCompiler.SemanticsBridge.Constraints
public import ClaferCompiler.Correctness.ExpressionScalarFacts
public import ClaferCompiler.Correctness.InheritedCorrectness

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions Frontend

theorem primitive_explicit_false (v : IR.Inherited.Validated n) (d : Fin n)
    (hd : (v.core.structural.get d).origin = .integer) : v.core.explicitAbstract[d] = false := by
  cases he : v.core.explicitAbstract[d] with
  | false => rfl
  | true =>
    have hp := (v.selectedChecked.1 d he).2
    have ht := (v.selectedChecked.2.2.2.2.2.2.2.1 d hd).1
    rw [hp] at ht
    cases ht

theorem source_wellFormed (p : Pipeline.Prepared) :
    (SemanticsBridge.Inherited.interpret (Pipeline.inherited p.document p.resolved).core).toEffectiveCore.WellFormed :=
  SemanticsBridge.Inherited.wellFormed _

theorem source_selected (p : Pipeline.Prepared) :
    (SemanticsBridge.Inherited.interpret (Pipeline.inherited p.document p.resolved).core).Selected :=
  SemanticsBridge.Inherited.selected _

theorem source_occurrences (p : Pipeline.Prepared) :
    p.attachments.map Sigma.fst = Constraints.occurrences p.document p.resolved.candidate :=
  SemanticsBridge.Constraints.attachments_preserved _ _ _ p.attachments_checked

/-- Every encoded occurrence is the original checked source term, owner and
span. Ordering and duplicates are retained by the actual successful pipeline. -/
theorem encoded_occurrences (p : Driver.Source.Product) :
    p.encoded.bodies.map EncodedBody.original = p.prepared.bodies :=
  ExpressionMeaning.occurrences_preserved _ _ _ _ _ p.encoded_checked

theorem encoded_tags (p : Driver.Source.Product) :
    (p.encoded.bodies.map fun b => (b.original.id, b.original.owner.val, b.original.source)) =
    (p.prepared.attachments.zipIdx.map fun (a, k) =>
      (k, a.1.owner.val, some a.1.expression.span)) := by
  have h := congrArg (List.map fun b : Body p.prepared.resolved.count => (b.id, b.owner.val, b.source))
    (encoded_occurrences p)
  simpa [List.map_map, Pipeline.Prepared.bodies, Pipeline.body, Function.comp_def] using h

theorem source_body_meaning {doc : Document} {c : Resolution.Candidate n}
    (a : (o : Constraints.Occurrence doc c) × Constraints.Attached doc c o) {U : Type}
    (model : Clafer.Constraints.IntegerBinding (SemanticsBridge.Expr.support a.2.layout.support) U)
    (env : Clafer.Constraints.Environment (SemanticsBridge.Expr.support a.2.layout.support) U []) :
    SemanticsBridge.Constraints.Meaning c.core a.2.layout.support a.1.expression model env
      (SemanticsBridge.Expr.denote a.2.body.checked model env) :=
  SemanticsBridge.Constraints.denote_sound a.2.body model env

theorem module_eq (p : Driver.Source.Product) : p.module.raw =
    { p.encoded.module.raw with facts := p.encoded.module.raw.facts ++
      [Driver.Source.objectBudget p.validated p.bounds.structural.objects] } :=
  ExpressionMeaning.check_raw _ _ p.module_checked

def eraseScalars (s : Schema) : Schema :=
  { s with signatures := s.signatures.map fun d => {d with scalar := false} }

theorem declarations_eraseScalars (s : Schema) (i : Instance) :
    i.declarations (eraseScalars s) = i.declarations s := by
  simp [Instance.declarations, eraseScalars, List.zipIdx_map, List.all_map,
    List.filter_map, List.map_map, Function.comp_def]

theorem scalarSchema_erase (v : IR.Inherited.Validated n) (s : Schema) :
    eraseScalars (scalarSchema v s) = eraseScalars s := by
  unfold eraseScalars scalarSchema
  congr 1
  simp only [List.map_map]
  change (s.signatures.zipIdx.map fun p => {p.1 with scalar := false}) = _
  have h := congrArg (List.map (fun d : Signature => {d with scalar := false}))
    (List.zipIdx_map_fst 0 s.signatures)
  simpa only [List.map_map, Function.comp_def] using h

theorem scalarSchema_declarations (v : IR.Inherited.Validated n) (s : Schema) (i : Instance) :
    i.declarations (scalarSchema v s) = i.declarations s := by
  rw [← declarations_eraseScalars, scalarSchema_erase, declarations_eraseScalars]

theorem scalarSchema_wellFormed (v : IR.Inherited.Validated n) (s : Schema) (i : Instance) :
    i.wellFormed (scalarSchema v s) = i.wellFormed s := by
  simp [Instance.wellFormed, scalarSchema]

/-- Successful source expression compilation records its precise schema as well
as facts and command; scalar flags add no structural ownership relation. -/
theorem compiled_schema (v : IR.Inherited.Validated n) (b : Structural.Bounds)
    (ranges : Vector IR.Expr.Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v b ranges bodies = .ok out) :
    out.module.raw.schema = scalarSchema v (Structural.schema v.layout) := by
  unfold compile at h
  cases hb : Inherited.compile v b with
  | error e => simp [hb, bind, Except.bind] at h
  | ok base =>
    cases hn : numericFacts v b ranges with
    | error e => simp [hb, hn, bind, Except.bind] at h
    | ok nums =>
      cases he : bodies.mapM (encodeBody v (sourceBounds v b ranges)) with
      | error e => simp [hb, hn, he, bind, Except.bind] at h
      | ok encoded =>
        simp only [hb, hn, he, bind, Except.bind] at h
        split at h
        · cases h
        · cases h
        · rename_i checked hc
          cases h
          have hr := ExpressionMeaning.check_raw _ checked hc
          obtain ⟨qs, _, hbase, _⟩ := Inherited.compile_output v b base hb
          rw [hr, hbase]
          rfl

theorem module_scalarFields (m : Module) (i : Instance) (h : m.eval i = some true) :
    i.scalarFields m.command.bitwidth m.schema = true := by
  unfold Module.eval at h
  cases hf : m.facts.mapM (fun f => f.eval m.command.bitwidth i []) with
  | none => simp [hf] at h
  | some values =>
    cases hb : m.command.body.eval m.command.bitwidth i [] with
    | none => simp [hf, hb] at h
    | some b =>
      simp [hf, hb] at h
      exact h.2

/-- The new budget fact only restricts the existing generated expression module. -/
theorem encoded_satisfies (p : Driver.Source.Product) (i : Instance)
    (h : Satisfies p.module.raw i) : Satisfies p.encoded.module.raw i := by
  have he := module_eq p
  have hs := module_scalarFields p.module.raw i h.2.2.2.2.2
  rw [he] at h hs
  refine ⟨p.encoded.module.typed, p.encoded.module.bounded, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  obtain ⟨base, hb, _, _, _, hc⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  obtain ⟨qs, _, hbase, _⟩ := Inherited.compile_output _ _ _ hb
  have hcmd : p.encoded.module.raw.command =
      { scopes := qs, bitwidth := (Driver.Source.targetBounds p.validated p.bounds).bitwidth } := by
    rw [hc, hbase]; rfl
  have ht : p.encoded.module.raw = {
      schema := p.encoded.module.raw.schema
      facts := p.encoded.module.raw.facts
      command := {scopes := qs, bitwidth := (Driver.Source.targetBounds p.validated p.bounds).bitwidth} } := by
    cases hm : p.encoded.module.raw
    simp only [hm] at hcmd ⊢
    rw [hcmd]
  rw [ht]
  apply (Inherited.run_eval _ _ _ _ _ (by simpa only [hcmd] using hs)).mpr
  intro fact hf
  have hh := Module.fact_true _ _ h.2.2.2.2.2 fact (List.mem_append_left _ hf)
  simpa only [hcmd] using hh

/-- Scalar payloads and source constraints preserve the actual structural target
reduct. This theorem has no supplied decoded instance or source-truth premise. -/
theorem inherited_reduct (p : Driver.Source.Product) (i : Instance)
    (h : Satisfies p.module.raw i) :
    ∃ base, Backend.Alloy.Inherited.compile p.validated
      (Driver.Source.targetBounds p.validated p.bounds) = .ok base ∧
      Satisfies base.module.raw i := by
  have hs := encoded_satisfies p i h
  obtain ⟨base, hb, _, _, hfacts, hcommand⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  have hschema := compiled_schema _ _ _ _ _ p.encoded_checked
  obtain ⟨qs, _, hbase, _⟩ := Inherited.compile_output _ _ _ hb
  refine ⟨base, hb, base.module.typed, base.module.bounded, ?_, ?_, ?_, ?_⟩
  · simpa only [hschema, scalarSchema_wellFormed, hbase, Backend.Alloy.Inherited.target,
      Backend.Alloy.Structural.target] using hs.2.2.1
  · simpa only [hschema, scalarSchema_declarations, hbase, Backend.Alloy.Inherited.target,
      Backend.Alloy.Structural.target] using hs.2.2.2.1
  · simpa only [hcommand] using hs.2.2.2.2.1
  · rw [hbase]
    apply (Inherited.run_eval _ _ _ _ _ (Structural.no_scalar_fields _ _ _)).mpr
    intro fact hf
    have hm : fact ∈ p.encoded.module.raw.facts := by
      rw [hfacts, hbase]
      exact List.mem_append_left _ (List.mem_append_left _ hf)
    have hh := Module.fact_true _ _ hs.2.2.2.2.2 fact hm
    simpa only [hcommand, hbase, Backend.Alloy.Inherited.target, Backend.Alloy.Structural.target] using hh

/-- The source CLI's satisfying target actually decodes and satisfies every
selected inherited structural obligation on its finite observed carrier. Full
primitive extension and authored-body interpretation are separate obligations. -/
theorem decoded_structure (p : Driver.Source.Product) (i : Instance)
    (h : Satisfies p.module.raw i) :
    ∃ o, Backend.Alloy.Inherited.decode p.validated i = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Structural.Represents p.validated.layout (Structural.realize o hr) i) ∧
      Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
        (Structural.realize o hr) := by
  obtain ⟨base, hb, hs⟩ := inherited_reduct p i h
  exact Inherited.compiled_sound p.validated _ base hb i hs

end ClaferCompiler.Correctness.Pipeline
