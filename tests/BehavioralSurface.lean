module

public import ClaferCompiler.SemanticsBridge.Behavioral.Surface

public section
namespace ClaferCompiler.Tests.BehavioralSurface

/-- Alloy grouped uniqueness must not be replaced by nested uniqueness:
this three-pair relation distinguishes them. -/
theorem nested_unique_is_not_tuple_unique :
    (∃! x : Fin 2, ∃! y : Fin 2, x = 0 ∨ y = 0) ∧
    ¬ (∃! xy : Fin 2 × Fin 2, xy.1 = 0 ∨ xy.2 = 0) := by
  simp only [ExistsUnique]
  decide

end ClaferCompiler.Tests.BehavioralSurface
