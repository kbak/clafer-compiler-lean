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

-- [impl->req~compiler-past-operators~1]
def previous (parent body : Temporal.Formula) : Temporal.Formula :=
  .unary .before (.binary .conj parent body)

def weakPrevious (parent body : Temporal.Formula) : Temporal.Formula :=
  .unary .neg (previous parent (.unary .neg body))

def once (parent body : Temporal.Formula) : Temporal.Formula :=
  .binary .since parent (.binary .conj parent body)

def historically (parent body : Temporal.Formula) : Temporal.Formula :=
  .unary .neg (once parent (.unary .neg body))

def since (parent left right : Temporal.Formula) : Temporal.Formula :=
  .binary .since (.binary .conj parent left) (.binary .conj parent right)

def triggered (parent left right : Temporal.Formula) : Temporal.Formula :=
  .unary .neg (since parent (.unary .neg left) (.unary .neg right))

def initially (present body : Temporal.Formula) : Temporal.Formula :=
  .binary .implies present.birth body

def atEnd (present body : Temporal.Formula) : Temporal.Formula :=
  .binary .implies (.binary .conj present (.unary .neg (.unary .after present))) body

end ClaferCompiler.Backend.Alloy.Behavioral
