module

public import ClaferCompiler.Correctness.PipelineCompletion
public import ClaferCompiler.Correctness.PipelineConstruction

@[expose] public section
/-! The completion shape is derived from successful source elaboration.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Frontend Frontend.Resolution IR.Structural

theorem source_primitive_shape (product : Driver.Source.Product)
    (p : Fin product.prepared.resolved.count)
    (primitive : (product.validated.core.structural.get p).origin = .integer) :
    PrimitiveShape (SemanticsBridge.Inherited.interpret product.validated.core) p := by
  let c := product.prepared.resolved.candidate
  let doc := product.prepared.document
  have checked := product.prepared.resolved.correspondence
  change Elaboration doc c at checked
  have rows := checked.2.2.2.2.1
  have hp : (c.core.get p).origin = .integer := primitive
  have notRoot : p ≠ c.core.root := by
    intro he
    have hr := (checked.1.2.1 p).mpr he
    rw [hp] at hr
    cases hr
  have prows := rows p
  simp only [ite_eq_right notRoot,ite_eq_left hp] at prows
  have rrows := rows c.core.root
  simp only [↓reduceIte] at rrows
  have noChild : ∀ d, (c.core.get d).parent ≠ some p := by
    intro d hd
    by_cases hdr : d = c.core.root
    · subst d
      rw [checked.1.2.2.1.1] at hd
      cases hd
    by_cases hdi : (c.core.get d).origin = .integer
    · have he : d = p := product.validated.selectedChecked.2.2.2.2.2.2.2.2.1 d p hdi hp
      subst d
      exact notRoot (Option.some.inj (hd.symm.trans prows.2.2.1))
    have hrow := rows d
    simp only [ite_eq_right hdr,ite_eq_right hdi] at hrow
    unfold SourceRow at hrow
    split at hrow
    · rename_i path h pathEq headerEq
      have parent := hrow.2.2.2.2.2.2.1
      split at parent
      · split at parent
        · rw [parent] at hd; cases hd
        · exact notRoot (Option.some.inj (hd.symm.trans parent))
      · obtain ⟨q,hq,hpath,_⟩ := parent
        have he : q = p := Option.some.inj (hq.symm.trans hd)
        subst q
        rw [prows.1] at hpath
        cases hpath
    · contradiction
  refine ⟨notRoot,prows.2.2.1,?_,prows.2.2.2.1,?_,noChild,?_,?_,?_,?_,?_⟩
  · change SemanticsBridge.Structural.reference (c.core.get p).reference = .basic
    rw [prows.2.2.2.2.1]
    rfl
  · intro d hd
    have ha := (product.validated.selectedChecked.2.2.1 d p hd).1
    rw [primitive_explicit_false product.validated p primitive] at ha
    cases ha
  · exact primitive_explicit_false product.validated p primitive
  · change SemanticsBridge.Structural.bounds (c.core.get p).localBounds = _
    rw [prows.2.2.2.2.2.2.2.2.1]
    rfl
  · change SemanticsBridge.Structural.bounds (c.core.get p).groupBounds = _
    rw [prows.2.2.2.2.2.2.2.1]
    rfl
  · change SemanticsBridge.Structural.bounds (c.core.get c.core.root).groupBounds = _
    rw [rrows.2.2.2.1]
    rfl
  · intro d h
    rcases h.cases_tail with he | ⟨e,_,he⟩
    · exact he.symm
    · have habs := (product.validated.selectedChecked.2.2.1 e c.core.root he).1
      have hr := (product.validated.selectedChecked.1 _ habs).1
      change (c.core.get c.core.root).isAbstract = true at hr
      rw [checked.1.2.2.1.2.2.2] at hr
      cases hr

end ClaferCompiler.Correctness.Pipeline
