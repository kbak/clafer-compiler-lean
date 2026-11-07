module

public import ClaferCompiler.Backend.Alloy.Behavioral.Partial

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralPartial
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Partial

def base (p : Formula) (facts : List Formula := []) : Module :=
  ⟨⟨⟨[{}], []⟩, [true], []⟩, facts, ⟨.run, p, [⟨1, false⟩], 4, 1, 3⟩⟩
def p : Formula := .mult .some (.sig 0)
def notP : Formula := .unary .neg p
def leaves : List Formula := [p, .unary .after notP, .unary .always (.unary .after notP)]
def good : Translation := atom .truth .truth
def bad : Translation := atom .falsity .truth

def badLater : Translation := atom p .truth

-- [utest->req~compiler-behavioral-partial-lowering~1]
def cases : List (String × Bool × Module) := [
  ("partial-undefined-assertion", true, base (counterexample (satisfaction bad true))),
  ("partial-undefined-source-negative", false, base (satisfaction bad false)),
  ("partial-strict-disjunction", false, base (satisfaction (disjunction good bad) true)),
  ("partial-false-guard", false, base (satisfaction (implication (atom .truth .falsity) bad) true)),
  ("partial-unused-conditional", false, base (satisfaction (conditional good good bad) true)),
  ("partial-eventual-later-domain", false, base (satisfaction (eventually .truth badLater) true) leaves),
  ("partial-eventual-cancellation", true, base (satisfaction (eventually p badLater) true) leaves),
  ("partial-until-later-domain", false, base (satisfaction (strongUntil .truth good badLater) true) leaves),
  ("partial-next-cancel-positive", true, base (satisfaction (next p bad) true) leaves),
  ("partial-next-cancel-negative", true, base (satisfaction (next p bad) false) leaves),
  ("partial-inactive-birth", true, base (satisfaction (initially .falsity bad) true)),
  ("partial-inactive-death", true, base (satisfaction («finally» .falsity bad) true)),
  ("partial-vacuous-domain", true, base (satisfaction (quantify .all (.empty .unary) .truth bad bad) true)),
  ("partial-undefined-empty-domain", false, base (satisfaction (quantify .all (.empty .unary) .falsity good good) true))
]

end ClaferCompiler.Tests.BehavioralPartial
