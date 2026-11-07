module

public import ClaferCompiler.IR.Behavioral.Grouped
public import ClaferCompiler.IR.Behavioral.Surface

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralPrimitive
open IR.Behavioral

def partialBody : Primitive.Formula 2 0 :=
  .or .truth (.atom (.integerEqual (.binary .divide (.literal 1) (.literal 0)) (.literal 0)))

def counted : Grouped.Formula 2 0 :=
  .atom (.count .one 2 true (.set (.extent 1))
    (.not (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 1))))))))

def fail (message : String) : IO α := throw (IO.userError message)

-- [utest->req~compiler-behavioral-elaboration~1]
def run : IO Unit := do
  let prepared := Primitive.normalize partialBody true 1000 (by decide)
  match prepared.original with
  | .or .truth (.atom (.integerEqual (.binary .divide (.literal 1) (.literal 0)) _)) => pure ()
  | _ => fail "partial operand lost from definedness tree"
  let negative := FormulaF.normalize counted false 1000 (by decide)
  match negative with
  | .not (.atom (.count .one 2 true (.set (.extent 1))
      (.not (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 1))))))))) => pure ()
  | _ => fail "joint count/raw body/disjointness/capture changed during normalization"
  let p : Primitive.Formula 2 0 := .atom (.less (.coerce (.set .empty)) (.literal 1))
  let chain : Surface.Transitions.ChainF (Primitive.Atom 2) (Primitive.Collection 2) 0 :=
    ⟨[⟨p, some partialBody, .eventual⟩], p⟩
  match Surface.Transitions.expand p chain with
  | .implies (.and _ (.or .truth _)) (.strongUntil (.and _ _) _) => pure ()
  | _ => fail "partial transition operands erased"
  match Surface.Patterns.expand (.follow p partialBody) (.between p p) with
  | .always (.implies _ (.strongUntil (.implies (.or .truth _) _) _)) => pure ()
  | _ => fail "partial pattern operands erased"
  let occurrences : Primitive.Integer 2 0 := .fold .sum
    (.cons (.set (.extent 1)) (.cons (.set (.extent 1)) .nil))
    (.extract (.set (.step (.deref 1) (.var 0))))
  match occurrences with
  | .fold .sum (.cons _ (.cons _ .nil)) (.extract (.set (.step (.deref 1) (.var 0)))) => pure ()
  | _ => fail "fold occurrence/head-to-target distinction lost"
  IO.println "partial formulas and grouped counting barriers passed"

end ClaferCompiler.Tests.BehavioralPrimitive
