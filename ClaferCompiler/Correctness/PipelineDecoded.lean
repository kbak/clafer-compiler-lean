module

public import ClaferCompiler.Correctness.PipelineModelAgreement
public import ClaferCompiler.Correctness.PipelineFullStructure
public import ClaferCompiler.Correctness.PipelineConstraints

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

theorem decoded_live (v : IR.Inherited.Validated n) (i : Instance)
    (o : Structural.Observation n) (decoded : Backend.Alloy.Inherited.decode v i = .ok o)
    (live : Structural.Live i) : ObservationLive o := by
  have he := (Structural.decode_success v.layout i o decoded).2.2.2
  rw [he]
  constructor
  · intro d x hx
    exact signature_live i live _ _ hx
  · intro d x y hm
    simp only [Structural.observation] at hm
    cases hp : (v.layout.core.get d).parent with
    | none => simp [hp,Structural.readPairs] at hm
    | some p =>
      simp only [hp,Option.bind_some] at hm
      exact Structural.field_atom_live i live _ x y ((Structural.mem_readPairs _ _ _).mp hm)
  · intro d x y hm
    simp only [Structural.observation] at hm
    cases hp : (v.layout.core.get d).reference.target with
    | none => simp [hp,Structural.readPairs] at hm
    | some p =>
      simp only [hp,Option.bind_some] at hm
      exact Structural.field_atom_live i live _ x y ((Structural.mem_readPairs _ _ _).mp hm)

theorem decoded_observation (p : Driver.Source.Product) (i : Instance)
    (o : Structural.Observation p.prepared.resolved.count)
    (decoded : Backend.Alloy.Inherited.decode p.validated i = .ok o)
    (s : Support p.prepared.resolved.count m) :
    observe p.validated s o (scalarRows p.validated i) = candidateObservation p i s := by
  rw [(Structural.decode_success p.validated.layout i o decoded).2.2.2]
  rfl

theorem decoded_values (p : Driver.Source.Product) (i : Instance) (hs : ObservationFacts p i)
    (d : Fin p.prepared.resolved.count) (hd : (p.validated.core.structural.get d).origin = .integer)
    (o : Structural.Observation p.prepared.resolved.count) (hr : o.root ∈ o.objects)
    (decoded : Backend.Alloy.Inherited.decode p.validated i = .ok o)
    (g : Structural.Objects o ↪ Atom)
    (labels : ∀ x, g x = decodeAtom (scalarRows p.validated i) x.val) :
    (∀ x, x ∉ (Structural.realize o hr).head d → ∃ a, g x = .object a) ∧
    (∀ x, x ∈ (Structural.realize o hr).head d →
      ∃ z ∈ (scalarRows p.validated i).map Prod.snd, g x = .integer z) := by
  have rows : scalarRows p.validated i = i.values[Structural.signatureId p.validated.layout d]?.getD [] := by
    simp [scalarRows,scalarIds_singleton p.validated d hd]
  have heads := congrArg (fun q : Structural.Observation p.prepared.resolved.count => q.heads d)
    (Structural.decode_success p.validated.layout i o decoded).2.2.2
  have sr := scalar_rows p i hs d hd
  constructor
  · intro x hx
    refine ⟨x.val,(labels x).trans (atom_object _ _ ?_)⟩
    intro z hz
    rw [rows] at hz
    apply hx
    change x.val ∈ o.heads d
    rw [heads]
    exact (sr.1 _ hz).1
  · intro x hx
    change x.val ∈ o.heads d at hx
    rw [heads] at hx
    obtain ⟨z,hz⟩ := sr.2.2.1 x.val hx
    refine ⟨z,?_,?_⟩
    · rw [rows]
      exact List.mem_map.mpr ⟨(x.val,z),hz,rfl⟩
    · rw [labels x,rows]
      exact (atom_integer _ sr.2.1 _ _).mpr hz

end ClaferCompiler.Correctness.Pipeline
