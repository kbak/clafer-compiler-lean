module

public import ClaferCompiler.IR.Behavioral.Surface
public import ClaferCompiler.IR.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Modifiers
open Surface.Modifiers

def spelling : Modifier → String
  | .initial => "initial"
  | .final => "final"
  | .finalref => "finalref"
  | .finaltarget => "finaltarget"

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Preserve all authored modifiers and their order, including repetitions.
Inherited occurrences accumulate along the validated superclass chain. -/
def effective (v : BehavioralStructural.Validated k) (declared : Vector (List Modifier) k)
    (d : Fin k) : List Modifier :=
  v.analysis.ancestors[d].flatMap (fun a => declared[a])

def expansions (v : BehavioralStructural.Validated k) (declared : Vector (List Modifier) k) :
    List (Placement k × Formula k 0) :=
  (List.finRange k).flatMap (fun d => (effective v declared d).flatMap (Surface.Modifiers.expand d))

end ClaferCompiler.IR.Behavioral.Modifiers
