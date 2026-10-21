module

public import ClaferCompiler.Correctness.PipelineScalars

public section
/-! [utest->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Tests.PipelineLimits

/-- The upstream whole-model relation cannot use a root-only carrier together
with its unconditional mathematical-integer realization. This exposes the
carrier boundary even for a constant true source constraint. -/
theorem root_only_no_integer_realization {U : Type}
    (m : Clafer.Semantics.EffectiveCore 1)
    (s : Clafer.Semantics.Configuration (Fin 1) U)
    (h : s.Rooted m) (r : FormalCD.IntegerRealization U) : False := by
  have collapse : ∀ x : U, x = s.root := by
    intro x
    rcases h.2.2 x with hx | ⟨d, hd, _⟩
    · exact hx
    · exact (hd (Subsingleton.elim d m.family.root)).elim
  have he : r.encode 0 = r.encode 1 := (collapse _).trans (collapse _).symm
  have hz : (0 : Int) = 1 := r.encode.injective he
  cases hz

/-- No finite observation is the complete mathematical primitive extent. -/
theorem finite_is_not_integer_domain {U : Type} (r : FormalCD.IntegerRealization U)
    (values : Set U) (finite : values.Finite) : values ≠ r.domain := by
  intro h
  have hi : r.domain.Infinite := Set.infinite_range_of_injective r.encode.injective
  exact (h ▸ finite).not_infinite hi

end ClaferCompiler.Tests.PipelineLimits
