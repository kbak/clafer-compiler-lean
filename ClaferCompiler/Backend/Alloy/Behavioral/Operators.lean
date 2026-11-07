module

public import ClaferCompiler.Backend.Alloy.Temporal.Syntax

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral
open Temporal

-- [impl->req~compiler-behavioral-encoding~1]
/-- Ordinary target formulas implementing the accepted parent-lifetime guards.
The argument is presence of the fixed parent, not presence of the context. -/
def next (parent body : Temporal.Formula) : Temporal.Formula :=
  .unary .after (.binary .disj (.unary .neg parent) body)

def eventually (parent body : Temporal.Formula) : Temporal.Formula :=
  .unary .eventually (.binary .disj (.unary .neg parent) body)

def always (parent body : Temporal.Formula) : Temporal.Formula :=
  .weakUntil (.binary .conj parent body) (.unary .neg parent)

def strongUntil (parent left right : Temporal.Formula) : Temporal.Formula :=
  .binary .until (.binary .conj parent left) (.binary .disj (.unary .neg parent) right)

def weakUntil (parent left right : Temporal.Formula) : Temporal.Formula :=
  .binary .disj (always parent left) (strongUntil parent left right)

def initially (present body : Temporal.Formula) : Temporal.Formula :=
  .binary .implies present.birth body

def atEnd (present body : Temporal.Formula) : Temporal.Formula :=
  .binary .implies (.binary .conj present (.unary .neg (.unary .after present))) body

end ClaferCompiler.Backend.Alloy.Behavioral
