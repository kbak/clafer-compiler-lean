module

public import ClaferCompiler.IR.StructuralNormalization
public import ClaferCompiler.SemanticsBridge.Structural
public import Clafer.Semantics.Structural

public section
namespace ClaferCompiler.SemanticsBridge.Structural.Normalization
open IR.Structural IR.Structural.Normalization Clafer.Semantics

-- [proof->req~compiler-resolved-normalization~1]
/-- Local multiplicities constrain only actual parent fibers. No admission,
finiteness, source satisfaction or target satisfaction premise is needed. -/
theorem multiplicities_iff (m : Core n) (s : Configuration (Fin n) U) :
    s.Multiplicities (interpret (normalize m)) ↔ s.Multiplicities (interpret m) := by
  simp only [Configuration.Multiplicities, interpret, get_normalize, declaration]
  constructor <;> intro h d c hp p hm
  · simpa [hp] using h d c hp p hm
  · simpa [hp] using h d c hp p hm

/-- Same declaration indices and same configuration, in both directions. This
establishes first-pass meaning independently of the fixed-point theorem. -/
theorem satisfies_iff (m : Core n) (s : Configuration (Fin n) U) :
    StructuralSatisfies (interpret (normalize m)) s ↔ StructuralSatisfies (interpret m) s := by
  simp only [StructuralSatisfies, multiplicities_iff]
  simp only [Configuration.Typed, Configuration.Rooted, Configuration.Inherits,
    Configuration.Abstracts, Configuration.Parents, Configuration.References,
    Configuration.Keys, Configuration.Groups, Configuration.Child,
    Configuration.DeclarationDisjoint, EffectiveCore.Ancestor,
    interpret, get_normalize, root_preserved, declaration]

theorem admitted_domain (v : Validated n) :
    (interpret (admitted v).core).WellFormed ∧ (interpret (admitted v).core).Supported :=
  validated_domain (admitted v)

end ClaferCompiler.SemanticsBridge.Structural.Normalization
