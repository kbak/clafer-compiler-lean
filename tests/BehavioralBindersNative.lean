module

public import ClaferCompiler.Frontend.Behavioral.Binders

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralBinders
open Frontend Frontend.Behavioral.Binders IR.Behavioral

def token (text : String) : Token := ⟨text, ⟨"binders.cfr", 0, text.utf8ByteSize⟩, 1, 1, 1⟩
def fail (message : String) : IO α := throw (IO.userError message)

-- [utest->req~compiler-behavioral-elaboration~1]
def run : IO Unit := do
  let outer : Context Nat 1 := #v[some (token "x", 7)]
  let plan ← match prepare outer (token "one") [token "x", token "y"] 9 with
    | .ok p => pure p | .error e => fail e.message
  for (name, index) in [("y", 0), ("x", 1)] do
    match lookup plan.bodyContext name with
    | some entry =>
      unless entry.index.val == index && entry.type == 9 do fail "wrong grouped local"
    | none => fail "missing grouped local"
  unless plan.bodyContext[2].isNone do fail "generated domain capture is source-visible"
  unless plan.bodyContext[3].map (·.2) == some 7 do fail "outer capture changed"
  match lookup outer "x" with
  | some entry => unless entry.index.val == 0 && entry.type == 7 do fail "domain scope changed"
  | none => fail "original domain binding missing"
  match prepare plan.bodyContext (token "some") [token "y"] 11 with
  | .error e => fail e.message
  | .ok nested =>
    match lookup nested.bodyContext "y", lookup nested.bodyContext "x" with
    | some y, some x =>
      unless y.index.val == 0 && y.type == 11 && x.index.val == 3 && x.type == 9 do
        fail "nested shadowing captured the wrong slot"
    | _, _ => fail "nested capture missing"
  for names in [[], [token "x", token "x"], [token "this"], [token "int"]] do
    match prepare outer (token "all") names 0 with
    | .error _ => pure ()
    | .ok _ => fail "illegal binder group accepted"
  match quantifier (token "not") with
  | .ok ⟨.no, _⟩ => pure ()
  | _ => fail "quantified not alias changed"
  let domain : Primitive.Collection 2 1 := .set (.var 0)
  let body : Grouped.Formula 2 4 :=
    .not (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 3))))))
  match IR.Behavioral.Binders.elaborate .all 2 true domain body with
  | .letSet (.set (.var 0)) (.quant .all (.set (.var 0))
      (.quant .all (.set (.diff (.var 1) (.var 0))) _)) => pure ()
  | _ => fail "shared/disjoint quantifier domains changed"
  match IR.Behavioral.Binders.elaborate .no 2 false domain body with
  | .letSet _ (.not (.quant .some (.set (.var 0)) (.quant .some (.set (.var 1)) _))) => pure ()
  | _ => fail "grouped no became repeated no"
  for q in [Quantifier.one, .lone] do
    match IR.Behavioral.Binders.elaborate q 2 true domain body with
    | .letSet _ (.atom (.count _ 2 true (.set (.var 0))
        (.not (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 3))))))))) => pure ()
    | _ => fail "ordered count body or outer capture changed"
  IO.println "behavioral binder captures, disjoint domains and tuple counting passed"

end ClaferCompiler.Tests.BehavioralBinders
