module

public import DPGraph
public import FormalCD
public import Clafer

public section

/-! Independent upstream imports: this file intentionally imports no compiler
module. These are API checks, not new downstream semantic proofs. -/
#check DPGraph.Span.red_comp
#check FormalCD.Hom
#check Clafer.Verification.check_correct
