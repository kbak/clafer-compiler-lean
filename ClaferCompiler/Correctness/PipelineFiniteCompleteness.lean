module

public import ClaferCompiler.Correctness.PipelineScalarCompleteness
public import ClaferCompiler.Correctness.PipelineDecoded

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

/-- Executable encoding of the original tables and their scalar payload rows. -/
def encodeObservation (p : Driver.Source.Product)
    (o : Structural.Observation p.prepared.resolved.count) (values : List (List (Nat × Int))) : Instance :=
  { Backend.Alloy.Inherited.encode p.validated o with values }

theorem encode_observation_live (v : IR.Inherited.Validated n) (o : Structural.Observation n)
    (live : ObservationLive o) (values : List (List (Nat × Int))) :
    Structural.Live { Backend.Alloy.Inherited.encode v o with values } := by
  constructor
  · intro xs hxs x hx
    change xs ∈ o.objects :: (Structural.order v.layout).map o.heads at hxs
    rcases List.mem_cons.mp hxs with rfl | hxs
    · exact hx
    · obtain ⟨d,_,rfl⟩ := List.mem_map.mp hxs
      exact live.heads d x hx
  · intro ts hts tuple ht x hx
    obtain ⟨⟨d,role⟩,_,rfl⟩ := List.mem_map.mp hts
    cases role <;> obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp ht
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    · exact hx.elim (fun h => h ▸ (live.containment d a b hab).1)
        (fun h => h ▸ (live.containment d a b hab).2)
    · exact hx.elim (fun h => h ▸ (live.dereference d a b hab).1)
        (fun h => h ▸ (live.dereference d a b hab).2)

theorem encode_observation_decode (p : Driver.Source.Product)
    (o : Structural.Observation p.prepared.resolved.count) (values : List (List (Nat × Int)))
    (table : Structural.TableWellFormed p.validated.layout o)
    (root : o.heads p.validated.layout.core.root = [o.root]) (present : o.root ∈ o.objects) :
    Backend.Alloy.Inherited.decode p.validated (encodeObservation p o values) = .ok o := by
  have h := Structural.decode_encode p.validated.layout o table root present
  exact h

/-- Data-only finite bounds: no formula evaluation or source/target satisfaction
is hidden here. CountFits is the existing independent cardinality capacity test. -/
structure FiniteFits (p : Driver.Source.Product)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) : Prop where
  table : Structural.TableWellFormed p.validated.layout o
  live : ObservationLive o
  rootHead : o.heads p.validated.layout.core.root = [o.root]
  scopes : ∀ base, Backend.Alloy.Inherited.compile p.validated
    (Driver.Source.targetBounds p.validated p.bounds) = .ok base →
    Structural.ObservationScopesFit p.validated.layout base.module.raw.command.scopes o
  counts : Inherited.CountFits p.validated (Structural.realize o root) p.bounds.structural.bitwidth
  scalarFields : (encodeObservation p o values).scalarFields p.bounds.structural.bitwidth
    (scalarSchema p.validated (Structural.schema p.validated.layout)) = true
  ranges : ∀ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer →
    ∀ row ∈ values[Structural.signatureId p.validated.layout d]?.getD [], p.intervals[d].Contains row.2
  unique : ∀ d : Fin p.prepared.resolved.count, (p.validated.core.structural.get d).origin = .integer →
    ∀ row ∈ values[Structural.signatureId p.validated.layout d]?.getD [],
    ∀ other ∈ values[Structural.signatureId p.validated.layout d]?.getD [], row.2 = other.2 → row.1 = other.1
  ordinaryCount :
    ((.diff (.sig 0) (Structural.union ((scalarIds p.validated).map Rel.sig)) : Rel).eval
      (encodeObservation p o values) []).eraseDups.length ≤ p.bounds.structural.objects
  budgetFits : fitsInt p.bounds.structural.bitwidth p.bounds.structural.objects = true

/-- Independent finite structural satisfaction supplies the structural target
facts. Scalar payloads are separately checked data and add no structural atoms. -/
theorem finite_observation_facts (p : Driver.Source.Product)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (fits : FiniteFits p o root values)
    (source : Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret p.validated.core)
      (Structural.realize o root)) : ObservationFacts p (encodeObservation p o values) := by
  let i := encodeObservation p o values
  have decoded := encode_observation_decode p o values fits.table fits.rootHead root
  obtain ⟨hr,⟨r⟩⟩ := Structural.decoded_represents p.validated.layout i o decoded
    (encode_observation_live p.validated o fits.live values)
  obtain ⟨base,hbase,_,hn,_⟩ := ExpressionMeaning.compile_output _ _ _ _ _ p.encoded_checked
  have structural : Satisfies base.module.raw i := by
    have hs := (SemanticsBridge.Inherited.satisfies_iff p.validated.core _).mp source
    obtain ⟨qs,_,he,_,_⟩ := Inherited.compile_output _ _ _ hbase
    refine ⟨base.module.typed,base.module.bounded,?_,?_,?_,?_⟩
    · simpa only [he,Backend.Alloy.Inherited.target,Structural.target,Driver.Source.Product.validated] using r.wellFormed
    · simpa only [he,Backend.Alloy.Inherited.target,Structural.target,Driver.Source.Product.validated] using
        Structural.source_declarations p.validated.layout _ i r hs.1
    · exact (Structural.observation_inScope _ _ o).mpr (fits.scopes base hbase)
    · rw [he]
      apply (Inherited.run_eval _ _ _ _ _ (Structural.no_scalar_fields _ _ i)).mpr
      rw [List.forall_mem_append]
      constructor
      · intro f hf
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf
        exact Structural.source_facts p.validated.layout _ i r hs.1 _ fits.counts.1 q hq
      · apply (Inherited.groups_iff p.validated _ i r _).mpr
        intro d hd x hx
        exact ⟨fits.counts.2 d hd x hx,source.2.2.2.2.1 d hd ⟨x,hx⟩⟩
  refine ⟨⟨base,hbase,structural⟩,fits.scalarFields,?_⟩
  intro fact hf
  obtain ⟨d,hd,hrange,hm⟩ := numericFacts_origin _ _ _ _ hn fact hf
  obtain ⟨decl,hdecl,hscalar⟩ := scalar_signature p.validated d hd
  obtain ⟨_,keys,total⟩ := ExpressionMeaning.scalar_field_rows i _ _ _ decl hdecl hscalar fits.scalarFields
  exact scalarFacts_complete i _ _ _ hrange (fits.ranges d hd) keys total (fits.unique d hd) fact hm

theorem finite_budget (p : Driver.Source.Product)
    (o : Structural.Observation p.prepared.resolved.count) (root : o.root ∈ o.objects)
    (values : List (List (Nat × Int))) (fits : FiniteFits p o root values) :
    (Driver.Source.objectBudget p.validated p.bounds.structural.objects).eval
      p.bounds.structural.bitwidth (encodeObservation p o values) [] = some true := by
  let count := ((.diff (.sig 0) (Structural.union ((scalarIds p.validated).map Rel.sig)) : Rel).eval
    (encodeObservation p o values) []).eraseDups.length
  have hc : fitsInt p.bounds.structural.bitwidth count = true := by
    have hb := fits.budgetFits
    simp only [fitsInt,Bool.and_eq_true,decide_eq_true_eq] at hb ⊢
    refine ⟨⟨hb.1.1,?_⟩,?_⟩
    · have hmin : minInt p.bounds.structural.bitwidth ≤ 0 := by unfold minInt; exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact hmin.trans (by omega)
    · exact (Int.ofNat_le.mpr fits.ordinaryCount).trans hb.2
  change (do let a ← boundedInt p.bounds.structural.bitwidth count
             let b ← boundedInt p.bounds.structural.bitwidth p.bounds.structural.objects
             pure (Comparison.le.holds a b)) = some true
  rw [(boundedInt_some_iff _ _).mpr hc,(boundedInt_some_iff _ _).mpr fits.budgetFits]
  simpa [Comparison.holds] using fits.ordinaryCount

end ClaferCompiler.Correctness.Pipeline
