module

public import ClaferCompiler.Frontend.Behavioral.Elaborate

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralElaboration
open Frontend.Behavioral IR.Behavioral

def fail (message : String) : IO α := throw (IO.userError message)

def load (source : String) : IO ParsedModel :=
  match parseAndElaborate IR.BehavioralStructural.profile "elaboration.cfr" source with
  | .ok m => pure m
  | .error d => fail (d.code ++ ": " ++ d.message ++ "\n" ++ source)

def body (m : ParsedModel) : IO (Grouped.Formula m.elaborated.declarations.resolved.count 0) :=
  match m.elaborated.model.constraints.head? with
  | some c => pure c.body
  | none => fail "missing body"

def idOf (m : ParsedModel) (name : String) : IO (Fin m.elaborated.declarations.resolved.count) :=
  match (List.finRange m.elaborated.declarations.resolved.count).find?
      (fun i => (m.elaborated.declarations.resolved.candidate.core.get i).name == name) with
  | some i => pure i | none => fail ("missing " ++ name)

-- [utest->req~compiler-behavioral-elaboration~1]
def captures : IO Unit := do
  let m ← load "A *\n[one disj x; y : A | X (x = y)]\n"
  match ← body m with
  | .letSet (.set (.extent _)) (.atom (.count .one 2 true (.set (.var 0))
      (.next (.atom (.primitive (.equal (.set (.var 1)) (.set (.var 0)))))))) => pure ()
  | _ => fail "joint count, raw temporal body or capture order"
  let m ← load "A *\n[no x; y : A | x = y]\n"
  match ← body m with
  | .letSet _ (.not (.quant .some _ (.quant .some _ _))) => pure ()
  | _ => fail "grouped no is not one negated existential"
  let m ← load "A *\n[let old = A in X (old = A)]\n"
  match ← body m with
  | .letSet (.set (.extent a)) (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.extent b)))))) =>
    unless a == b do fail "let captured a different declaration"
  | _ => fail "let lost captured heads"
  let m ← load "A *\n[all old : A | some old; x : old | X (x = old)]\n"
  match ← body m with
  | .letSet _ (.quant .all _ (.letSet (.set (.var 0))
      (.quant .some _ (.quant .some _ (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 1)))))))))) => pure ()
  | _ => fail "group domain was resolved after introducing shadowing names"
  let m ← load "abstract Node -> Node\n  [some Outside]\nn : Node\nOutside\n"
  let outside ← idOf m "Outside"
  match ← body m with
  | .atom (.primitive (.inhabited (.set (.extent d)))) =>
    unless d == outside do fail "reference cycle hid an unrelated global name"
  | _ => fail "reference cycle changed global lookup into relative navigation"
  let m ← load "abstract A -> B\n  [some item]\nabstract B -> A\n  item ?\nitem ?\n"
  let b ← idOf m "B"
  match ← body m with
  | .atom (.primitive (.inhabited (.set (.step (.child child) (.thisStep (.deref _)))))) =>
    unless (m.elaborated.declarations.resolved.candidate.core.get child).parent == some b do
      fail "target field lost priority over a global name in a reference cycle"
  | _ => fail "cyclic target field lookup lost its relative path"
  let m ← load "a\n  [X some this.parent]\n"
  match ← body m with
  | .next (.atom (.primitive (.inhabited (.set (.thisStep .parent))))) => pure ()
  | _ => fail "direct this navigation lost its fixed identity"
  let m ← load "a\n  [X some (this ++ noclafer).parent]\n"
  match ← body m with
  | .next (.atom (.primitive (.inhabited (.set (.step .parent (.union .this .empty)))))) => pure ()
  | _ => fail "ordinary observed this became fixed-identity navigation"

def foldCount : Nat → Primitive.Integer k n → Nat :=
  Nat.rec (fun _ => 0) (fun _ next e => match e with
    | .binary _ a b => next a + next b
    | .fold .. => 1
    | _ => 0)

-- [utest->req~compiler-behavioral-elaboration~1]
def arithmetic : IO Unit := do
  let m ← load "abstract R -> int\nr : R *\n[r + 1 = 3]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer (.binary .add (.coerce (.set (.step (.deref d) (.extent h)))) (.literal 1)))
      (.integer (.literal 3)))) => unless d == h do fail "inherited reference head changed"
  | _ => fail "D3 integer conversion must use one inherited dereference"
  let m ← load "r -> int *\n[sum (r ++ r) = 6]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer (.binary .add (.binary .add (.literal 0) a) b)) _)) =>
    for term in [a, b] do
      match term with
      | .fold .sum (.cons _ .nil) (.extract (.set (.step (.deref _) (.var 0)))) => pure ()
      | _ => fail "aggregate erased repeated operand occurrences or head extraction"
  | _ => fail "aggregate shape"
  let m ← load "r -> int *\n[sum r ++ r ++ r ++ r ++ r ++ r ++ r = 0]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer sum) _)) =>
    unless foldCount 100 sum == 7 do fail "seven authored operands did not retain seven occurrence families"
  | _ => fail "aggregate fixture shape"
  let some occurrence := (properties m.elaborated.declarations).head? | fail "aggregate occurrence"
  for budget in [4, 5, 6] do
    let .error d := Expressions.synthAt m.source m.elaborated.declarations.resolved.admitted
        occurrence.owner budget #v[] none occurrence.expression
      | fail "insufficient traversal budget silently collapsed aggregate occurrences"
    unless d.code == "behavioral.expression-budget" do fail "aggregate traversal diagnostic"
  for expr in ["product r = 1", "min r = noclafer", "max r = 3", "#r = 2",
      "r * 2 / 3 % 4 >= -1", "if some r then r > 0 else no r"] do
    let _ ← load ("r -> int *\n[" ++ expr ++ "]\n")
  let m ← load "A\n[some A || 1 / 0 = 0]\n"
  match ← body m with
  | .or _ (.atom (.primitive (.equal (.integer (.binary .divide (.literal 1) (.literal 0))) _))) => pure ()
  | _ => fail "undefined operand disappeared from original strict domain"

-- [utest->req~compiler-behavioral-elaboration~1]
def surfaces : IO Unit := do
  for pat in ["never A", "sometime A", "lonce A", "always A", "A must precede B", "A must follow B"] do
    for scope in ["", " before R", " after Q", " between Q and R", " after Q until R"] do
      let _ ← load ("A ?\nB ?\nQ ?\nR ?\n[" ++ pat ++ scope ++ "]\n")
  let m ← load "A ?\nB ?\nC ?\nQ ?\nR ?\n[A -[Q]->> B -[R]-> C]\n"
  match ← body m with
  | .implies (.and a _) (.strongUntil (.and context _) (.and (.and _ _) (.next _))) =>
    match a, context with
    | .atom (.primitive (.inhabited (.set (.extent _)))), .atom (.primitive (.inhabited (.set .this))) => pure ()
    | _, _ => fail "eventual persistence contains entry guard or wrong context"
  | _ => fail "chain became nested implication or dropped later guard"
  for expr in ["!(X some A)", "initially (A --> B)", "finally no A", "A U B", "A W B",
      "some A <=> next (some B xor no A)", "globally (some A => eventually B)", "(some A) = (some B)"] do
    let _ ← load ("A ?\nB ?\n[" ++ expr ++ "]\n")

-- [utest->req~compiler-behavioral-elaboration~1]
def initializerOrigins : IO Unit := do
  for source in ["n -> int = 3\no\n  n\n", "abstract n -> int = 3\no\n  n\n"] do
    let m ← load source
    let e := m.elaborated
    let [header] := e.headers | fail "initializer origin inventory"
    let [property] := e.generated | fail "initializer property inventory"
    unless property.owner == e.declarations.resolved.candidate.core.root do
      fail "top-level initializer owner"
    let d := header.declaration
    match property.body with
    | .implies (.atom (.primitive (.inhabited (.set (.thisStep (.child h))))))
        (.atom (.primitive (.equal (.set (.step (.deref ref) (.thisStep (.child l)))) (.integer (.literal 3))))) =>
      unless h == d && l == d && ref == d && (e.declarations.resolved.candidate.core.get d).parent.isSome do
        fail "initializer resolved a same-spelled declaration instead of its origin"
    | .implies (.atom (.primitive (.inhabited (.set (.extent h)))))
        (.atom (.primitive (.equal (.set (.step (.deref ref) (.extent l))) (.integer (.literal 3))))) =>
      unless h == d && l == d && ref == d && (e.declarations.resolved.candidate.core.get d).parent.isNone do
        fail "initializer resolved a same-spelled declaration instead of its origin"
    | _ => fail "initializer origin equation"

-- [utest->req~compiler-behavioral-elaboration~1]
def documents : IO Unit := do
  let m ← load "abstract R -> int\ninitial finalref finaltarget r : R *\n  assert [X (this = 2)]\nowner\n  n -> int = 3\n  start ? --> finish\n  finish ?\n  [initially some start]\nassert [sometime r]\n"
  let e := m.elaborated
  unless e.model.constraints.length == 3 && e.model.assertions.length == 2 do fail "property inventory changed"
  let n ← idOf m "n"
  let owner ← idOf m "owner"
  let start ← idOf m "start"
  match e.generated with
  | [initializer, transition] =>
    unless initializer.owner == owner && transition.owner == start do fail "header attachment changed"
    match initializer.body with
    | .implies (.atom (.primitive (.inhabited (.set (.thisStep (.child h))))))
        (.atom (.primitive (.equal (.set (.step (.deref r) (.thisStep (.child h')))) (.integer (.literal 3))))) =>
      unless h == n && h' == n && r == n do fail "initializer's head and value views differ"
    | _ => fail "initializer lost presence guard, gained birth anchor or skipped dereference"
    match transition.body with
    | .implies (.atom (.primitive (.inhabited (.set .this)))) (.next _) => pure ()
    | _ => fail "declaration transition lost this attachment"
  | _ => fail "header inventory"
  let .ok check := e.check 0 | fail "check request"
  match check.command with
  | .check i => unless i.val == 0 do fail "wrong assertion selected"
  | _ => fail "assertion turned into run/source negation"
  let .error _ := e.check 2 | fail "invalid assertion index accepted"
  let .ok scenario := parseBehavioral IR.BehavioralStructural.profile "scenario.cfr" "[initially (start --> finish)]\n"
    | fail "scenario parse"
  let .ok run := e.run [⟨owner, scenario⟩] | fail "scenario binding"
  unless run.model.constraints.length == 3 do fail "scenario replaced model constraints"
  match run.command with
  | .run [c] =>
    unless c.owner == owner && c.source.file == "scenario.cfr" do fail "scenario owner/span"
    match c.body with | .initially (.implies _ (.next _)) => pure () | _ => fail "scenario anchor changed"
  | _ => fail "scenario command shape"
  let .ok assertion := parseBehavioral IR.BehavioralStructural.profile "bad.cfr" "assert [some r]\n"
    | fail "assertion parse"
  let .error d := e.run [⟨owner, assertion⟩] | fail "assertion silently promoted to scenario constraint"
  unless d.code == "behavioral.scenario-assertion" do fail "scenario diagnostic"

-- [utest->req~compiler-diagnostics~1]
def diagnostics : IO Unit := do
  for (source, code) in [
      ("A\n[X missing]\n", "behavioral.unknown-name"),
      ("abstract Node -> Node\n  [some missing]\n", "behavioral.unknown-name"),
      ("A\n[1 + A = 2]\n", "behavioral.expected-integer"),
      ("A\n[one x; x : A | some x]\n", "behavioral.binder-group"),
      ("A\n[some int]\n", "behavioral.infinite-primitive-extent"),
      ("A\n[if some A then 1 else 2]\n", "behavioral.unsupported-value-conditional")] do
    let .error d := parseAndElaborate IR.BehavioralStructural.profile "bad.cfr" source
      | fail ("bad source accepted: " ++ source)
    unless d.code == code && d.primary.file == "bad.cfr" && d.line == 2 do
      fail ("incorrect diagnostic " ++ d.code ++ ": " ++ toString d.line)

def run : IO Unit := do
  captures
  arithmetic
  surfaces
  initializerOrigins
  documents
  diagnostics
  IO.println "behavioral source expressions, captures, arithmetic, surfaces and requests passed"

end ClaferCompiler.Tests.BehavioralElaboration
