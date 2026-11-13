module

public import ClaferCompiler.Frontend.Behavioral.Elaborate
public import ClaferCompiler.IR.Behavioral.Ranges

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralElaboration
open Frontend.Behavioral IR.Behavioral

def fail (message : String) : IO α := throw (IO.userError message)

def load (source : String) : IO ParsedModel :=
  match parseAndElaborate IR.BehavioralStructural.profile "elaboration.cfr" source with
  | .ok m => pure m
  | .error d => fail (d.code ++ ": " ++ d.message ++ "\n" ++ source)

def body (m : ParsedModel) : IO (Expression.Formula m.elaborated.declarations.resolved.count 0) :=
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
  -- A RHS uses the previous environment, and nested binders cannot capture it.
  let m ← load "A *\nB *\n[let x = A ++ B in let x = x -- B in X (no x)]\n"
  match ← body m with
  | .letSet (.set (.union (.extent a) (.extent b)))
      (.letSet (.set (.diff (.var 0) (.extent b')))
        (.next (.not (.atom (.primitive (.inhabited (.set (.var 0)))))))) =>
    unless a == (← idOf m "A") && b == b' do fail "let shadowing changed RHS declaration identity"
  | _ => fail "compound let RHS was substituted or recaptured"
  for source in ["A *\n[let x = A in all x : x | X (x = x)]\n",
      "A *\n[let captured = A in all item : captured | X (item = item)]\n"] do
    let m ← load source
    match ← body m with
    | .letSet (.set (.extent _)) (.letSet (.set (.var 0))
        (.quant .all (.set (.var 0))
          (.next (.atom (.primitive (.equal (.set (.var 0)) (.set (.var 0)))))))) => pure ()
    | _ => fail "alpha-renaming or shadowing changed resolved captures"
  let m ← load "A *\n[let unused = 1 / 0 in some A]\n"
  match ← body m with
  | .letSet (.integer (.binary .divide (.literal 1) (.literal 0))) _ => pure ()
  | _ => fail "unused undefined binding was discarded"
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

-- [utest->req~compiler-behavioral-elaboration~1]
def roots : IO Unit := do
  for source in ["A ?\n[X some root]\n", "A ?\n  [X some root]\n",
      "P\n  A ?\n    [X some root]\n"] do
    let m ← load source
    match ← body m with
    | .next (.atom (.primitive (.inhabited (.set .root)))) => pure ()
    | _ => fail "root must denote the global identity rather than the enclosing owner"
  let m ← load "A ?\n  [X some root.A]\n"
  let a ← idOf m "A"
  match ← body m with
  | .next (.atom (.primitive (.inhabited (.set (.step (.child d) .root))))) =>
    unless d == a do fail "root navigation changed its selected field"
  | _ => fail "root navigation must observe the field at evaluation time"
  let m ← load "A ?\n  [let r = root in X (r = root)]\n"
  match ← body m with
  | .letSet (.set .root) (.next (.atom (.primitive (.equal (.set (.var 0)) (.set .root))))) => pure ()
  | _ => fail "root capture lost the lexical slot"
  for source in ["root ?\n", "A ?\n[all root : A | some root]\n",
      "A ?\n[some A.root]\n"] do
    let .error _ := parseAndElaborate IR.BehavioralStructural.profile "root.cfr" source
      | fail "root became a user declaration, binder or relative field"

def foldCount : Nat → Expression.Integer k n → Nat :=
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
      "some A <=> next (some B xor no A)", "globally (some A => eventually B)", "(some A) = (some B)", "(some A) = B", "A != (some B)",
      "(A --> B) = (some A)", "if some A then some B else A",
      "if some A then B else (A --> B)"] do
    let _ ← load ("A ?\nB ?\n[" ++ expr ++ "]\n")

-- [utest->req~compiler-behavioral-elaboration~1]
def values : IO Unit := do
  let m ← load "A ?\n[1 / (if some A then 1 else 0) = 1]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer (.binary .divide (.literal 1)
      (.ite _ (.literal 1) (.literal 0)))) (.integer (.literal 1)))) => pure ()
  | _ => fail "value conditional was distributed over division"
  let m ← load "A ?\n[(if some A then 1 else 1 / 0) = 1]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer (.ite _ (.literal 1)
      (.binary .divide (.literal 1) (.literal 0)))) _)) => pure ()
  | _ => fail "conditional discarded an undefined unselected branch"
  let m ← load "A\n  x ?\nB\n  y ?\n[some (if some A then A else B).parent]\n"
  match ← body m with
  | .atom (.primitive (.inhabited (.union _ _))) => pure ()
  | _ => fail "heterogeneous conditional navigation"
  let m ← load "A *\n[all x : (if some A then A else noclafer) | X some x]\n"
  match ← body m with
  | .letSet (.ite _ _ _) (.quant .all _ (.next _)) => pure ()
  | _ => fail "conditional domain was moved outside its binder"
  for expr in ["some (A ++ B)", "some (A ++ B).parent", "no noclafer.parent",
      "no noclafer.A", "(A <: A) = A", "(A :> A) = A",
      "some (if some A then A else B)"] do
    let _ ← load ("A *\nB *\n[" ++ expr ++ "]\n")
  let _ ← load "abstract T\n  [some this.parent]\nP\n  a : T\nQ\n  b : T\n"
  let _ ← load "abstract T\n  [some this.parent.field]\nP\n  a : T\n  field\nQ\n  b : T\n  field\n"
  let _ ← load "P\n  field\nQ\n  field\n[no noclafer.field]\n"
  let m ← load "A ?\n[no (if 1 / 0 = 0 then A else A).noclafer]\n"
  match ← body m with
  | .not (.atom (.primitive (.inhabited (.inter (.ite _ _ _) (.set .empty))))) => pure ()
  | _ => fail "empty navigation erased partial input"
  let _ ← load "a -> int *\nb -> int *\n[sum (a ++ b) >= 0]\n"

-- [utest->req~compiler-behavioral-elaboration~1]
def ranges : IO Unit := do
  let cases : List (String × Nat × Option String) := [
    ("1 + 2 = 3", 4, none),
    ("(if some A then 1 else 2) = 1", 4, none),
    ("all x : A | #x = 1", 4, none),
    ("let x = A in #x = 3", 4, none),
    ("#(A ++ A) = 6", 4, none),
    ("sum r = 0", 4, none),
    ("product r = 0", 5, none),
    ("min r = 1", 4, none),
    ("some A || 1 / 0 = 0", 4, some "behavioral.possible-zero-divisor"),
    ("no A && 7 + 1 = 0", 4, some "behavioral.integer-range"),
    ("(if some A then 1 else 7 + 1) = 1", 4, some "behavioral.integer-range"),
    ("all x : noclafer | 7 + 1 = 0", 4, some "behavioral.integer-range"),
    ("one disj x; y : A | 7 + 1 = 0", 4, some "behavioral.integer-range"),
    ("#(A ++ A ++ A) = 0", 4, some "behavioral.integer-range"),
    ("sum (r ++ r) = 0", 4, some "behavioral.integer-range"),
    ("product r = 0", 4, some "behavioral.integer-range"),
    ("1 / (if some A then 1 else 0) = 1", 4, some "behavioral.possible-zero-divisor")]
  for (expression, width, expected) in cases do
    let m ← load ("A *\nr -> int *\n[" ++ expression ++ "]\n")
    let formula ← body m
    let bounds : Expression.Ranges.Inputs m.elaborated.declarations.resolved.count :=
      ⟨width, ⟨1, ⟨0, 0⟩⟩, ⟨1, ⟨0, 0⟩⟩,
        Vector.replicate _ ⟨3, ⟨2, 2⟩⟩, (fun _ => ⟨3, ⟨2, 2⟩⟩), Vector.replicate _ true, fun _ => true⟩
    match Expression.Ranges.analyze bounds 256 formula #v[], expected with
    | .ok _, none => pure ()
    | .error d, some code => unless d.code == code do fail (expression ++ ": " ++ d.code)
    | .error d, none => fail (expression ++ ": unexpected " ++ d.code)
    | .ok _, some _ => fail (expression ++ ": missing range rejection")
    let .error exhausted := Expression.Ranges.analyze bounds 0 formula #v[]
      | fail "range budget exhaustion silently accepted"
    unless exhausted.code == "behavioral.range-budget" do fail "range budget diagnostic"
  let bad : Expression.Ranges.Inputs 1 :=
    ⟨4, ⟨1, ⟨0, 0⟩⟩, ⟨1, ⟨0, 0⟩⟩, #v[⟨1, ⟨8, 8⟩⟩], (fun _ => ⟨1, ⟨8, 8⟩⟩), #v[true], fun _ => true⟩
  for path in [SetExpr.diff .empty (.extent 0), .inter .empty (.extent 0),
      .diff .empty (.step .parent .this)] do
    let .error d := Expression.Ranges.analyze bad 32
      (.atom (.primitive (.inhabited (.set path))) : Expression.Formula 1 0) #v[]
      | fail "set simplification hid an out-of-range observation"
    unless d.code == "behavioral.integer-range" do fail "set observation range diagnostic"


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
    | .quant .all (.set (.thisStep (.child h)))
        (.atom (.equalClosed (.step (.deref ref) (.thisStep (.child l))) (.integer (.literal 3)))) =>
      unless h == d && l == d && ref == d && (e.declarations.resolved.candidate.core.get d).parent.isSome do
        fail "initializer resolved a same-spelled declaration instead of its origin"
    | .quant .all (.set (.extent h))
        (.atom (.equalClosed (.step (.deref ref) (.extent l)) (.integer (.literal 3)))) =>
      unless h == d && l == d && ref == d && (e.declarations.resolved.candidate.core.get d).parent.isNone do
        fail "initializer resolved a same-spelled declaration instead of its origin"
    | _ => fail "initializer origin equation"

-- [utest->req~compiler-behavioral-elaboration~1]
def initializerAdmission : IO Unit := do
  for (rhs, temporal) in [("A ++ A", false), ("if X (some A) then A else A", true)] do
    let m ← load ("A ?\nx -> int ? := 0\n[let unused = (" ++ rhs ++ ") in some root]\n")
    unless m.source.temporal == temporal do fail "let RHS lost authored temporal selection"
    let [p] := m.elaborated.generated | fail "let RHS initializer inventory"
    match p.body, temporal with
    | .quant .all _ (.atom (.equalClosed _ _)), false => pure ()
    | .atom (.inContext _ (.initially _)), true => pure ()
    | _, _ => fail "let RHS changed initializer clock selection"
  for source in ["x -> int ? := 0\n", "enum E = A | B\nx -> int ? := 0\n"] do
    let m ← load source
    if m.source.temporal then fail "generated enum finality selected temporal initializer semantics"
    let some p := m.elaborated.generated.getLast? | fail "static initializer inventory"
    match p.body with
    | .quant .all _ (.atom (.equalClosed _ _)) => pure ()
    | _ => fail "static initializer acquired a generated birth anchor"
  for (source, single) in [
      ("x -> int := 0\n", true), ("x -> int ? := 0\n", true),
      ("x -> int 0..1 := 0\n", true), ("x -> int 1..1 := 0\n", true),
      ("x -> int 0 := 0\n", true), ("x -> int * := 0\n", false),
      ("x -> int 2 := 0\n", false), ("x -> int + := 0\n", false),
      ("abstract x -> int := 0\n", true),
      ("abstract x -> int * := 0\n", false),
      ("abstract x -> int 0..* := 0\n", false),
      ("xor P\n  x -> int := 0\n", true),
      ("or P\n  x -> int := 0\n", true),
      ("P\n  abstract x -> int := 0\n", true),
      ("P\n  abstract x -> int * := 0\n", false)] do
    let m ← load (source ++ "[always one root]\n")
    let [p] := m.elaborated.generated | fail "initializer inventory"
    match p.body, single with
    | .atom (.inContext _ (.initially (.quant .all (.set .this)
        (.atom (.inContext _ (.atom (.equalClosed (.step (.deref _) (.var 0)) _))))))), true => pure ()
    | .initially (.quant .all _ (.atom (.equalClosed _ _))), false => pure ()
    | _, _ => fail ("initializer clock: " ++ source)
  for bounds in ["?", "1", "0", "+", "0..1", "1..*"] do
    let .error d := parseAndElaborate IR.BehavioralStructural.profile "initial.cfr"
        ("abstract x -> int " ++ bounds ++ " := 0\n")
      | fail "parentless abstract bound was silently reclassified"
    unless d.code == "behavioral.initializer-parentless-multiplicity" do fail d.code
  for rhs in ["xs", "0 ++ 1"] do
    let .error d := parseAndElaborate IR.BehavioralStructural.profile "initial.cfr"
        ("xs -> int *\nabstract x -> int := " ++ rhs ++ "\n")
      | fail ("abstract single accepted an unproved scalar bound: " ++ rhs)
    unless d.code == "behavioral.initializer-scalar" do fail d.code
  for rhs in ["x", "0 ++ 0", "if X (some x) then 0 else 1"] do
    let _ ← load ("x -> int ?\nabstract A -> int := " ++ rhs ++ "\n")
  let .ok report := parseAndElaborateReport IR.BehavioralStructural.profile "inherit.cfr"
      "abstract A -> int = 0\na : A ? := 1\n[always one root]\n"
    | fail "own initial equation under inherited constant rejected"
  if !report.warnings.isEmpty then fail "blanket inherited initializer warning"

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
    | .quant .all (.set (.thisStep (.child h)))
        (.atom (.equalClosed (.step (.deref r) (.thisStep (.child h'))) (.integer (.literal 3)))) =>
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

-- [utest->req~compiler-behavioral-elaboration~1]
def correctedPatternAttachments : IO Unit := do
  for pattern in ["x must follow B between Q and R", "x must precede B after Q"] do
    for anchor in [false, true] do
      let wrapped := if anchor then "initially (" ++ pattern ++ ")" else pattern
      let m ← load ("machine *\n  ctx *\n    A ?\n    B ?\n    Q ?\n    R ?\n    assert [all x : A | " ++ wrapped ++ "]\n" ++
        "assert [all c : machine.ctx | X some c]\n")
      let ctx ← idOf m "ctx"
      let [top, nested] := m.elaborated.model.assertions | fail "nested assertion inventory"
      unless nested.owner == ctx && top.owner == m.elaborated.declarations.resolved.candidate.core.root do
        fail "assertion attachment changed during binder lowering"
      match nested.body, anchor with
      | .letSet _ (.quant .all _ (.initially _)), true => pure ()
      | .letSet _ (.quant .all _ _), false => pure ()
      | _, _ => fail "corrected pattern lost its explicit anchor or binding"
      match top.body with
      | .letSet (.set (.step (.child child) _)) (.quant .all _ (.next (.atom (.primitive (.inhabited (.set (.var 0))))))) =>
        unless child == ctx do fail "nested assertion domain changed"
      | _ => fail "nested assertion domain or time-spanning capture changed"

-- [utest->req~compiler-diagnostics~1]
def diagnostics : IO Unit := do
  for (source, code) in [
      ("A\n[X missing]\n", "behavioral.unknown-name"),
      ("abstract Node -> Node\n  [some missing]\n", "behavioral.unknown-name"),
      ("A\n[1 + A = 2]\n", "behavioral.expected-integer"),
      ("A\n[one x; x : A | some x]\n", "behavioral.binder-group"),
      ("A\n[some int]\n", "behavioral.infinite-primitive-extent"),
      ("A\n[if some A then 1 else 2]\n", "behavioral.expected-formula")] do
    let .error d := parseAndElaborate IR.BehavioralStructural.profile "bad.cfr" source
      | fail ("bad source accepted: " ++ source)
    unless d.code == code && d.primary.file == "bad.cfr" && d.line == 2 do
      fail ("incorrect diagnostic " ++ d.code ++ ": " ++ toString d.line)

-- [utest->req~compiler-behavioral-elaboration~1]
def separateScenarios : IO Unit := do
  for source in ["", "A ?\n", "abstract A\na : A ?\n"] do
    let m ← load source
    let e := m.elaborated
    let integerRows := (List.finRange e.declarations.resolved.count).filter fun d =>
      (e.declarations.resolved.candidate.core.get d).origin == .integer
    unless integerRows.length == 1 && e.model.constraints.isEmpty && e.model.assertions.isEmpty do
      fail "scenario preparation must reserve one integer domain without adding a property"
    for expression in ["0 = 0", "0 < 1", "some 0", "all x : 0 | some x", "#noclafer = 0"] do
      let .ok scenario := parseBehavioral IR.BehavioralStructural.profile "scenario.cfr" ("[" ++ expression ++ "]")
        | fail "numeric scenario parse"
      let .ok request := e.run [⟨e.model.structural.core.structural.root, scenario⟩]
        | fail ("separate numeric scenario: " ++ expression)
      unless request.model.constraints.isEmpty do fail "scenario became a model constraint"
      match request.command with
      | .run [c] => unless c.owner == e.model.structural.core.structural.root && c.source.file == "scenario.cfr" do
          fail "scenario attachment or span changed"
      | _ => fail "scenario count changed"

-- [utest->req~compiler-behavioral-elaboration~1]
-- [utest->req~compiler-diagnostics~1]
def emptyNavigationWarnings : IO Unit := do
  for expression in ["noclafer.missing", "(noclafer).missing.parent.dref",
      "noclafer.(missing.parent)", "(noclafer.missing).other", "noclafer.field",
      "noclafer.this", "noclafer.noclafer"] do
    let source := "P\n  field\nQ\n  field\n[no " ++ expression ++ "]\n"
    let .ok report := parseAndElaborateReport IR.BehavioralStructural.profile "empty.cfr" source
      | fail ("literal empty chain rejected: " ++ expression)
    match ← body report.model with
    | .not (.atom (.primitive (.inhabited (.set .empty)))) => pure ()
    | _ => fail "literal navigation did not elaborate to unary empty"
    unless report.warnings.length == 1 &&
        report.warnings.all (·.code == "behavioral.empty-navigation") do
      fail "maximal literal navigation must report once"
  let m ← load "A ?\n[no (if 1 / 0 = 0 then A else A).(noclafer.missing)]\n"
  match ← body m with
  | .not (.atom (.primitive (.inhabited (.inter (.ite _ _ _) (.set .empty))))) => pure ()
  | _ => fail "literal-tail rewrite erased partial cursor"
  let m ← load "A ?\n[(1 / 0) = (1 / 0)]\n"
  match ← body m with
  | .atom (.primitive (.equal (.integer (.binary .divide _ _)) (.integer (.binary .divide _ _)))) => pure ()
  | _ => fail "self equality was simplified before range admission"
  let .ok report := parseAndElaborateReport IR.BehavioralStructural.profile "warnings.cfr"
      "A ?\n[A = (A)]\n[A != A]\n[no (A -- A)]\n[some (A ** A)]\n"
    | fail "self expressions rejected"
  unless report.warnings.map (·.operator) == ["=", "!=", "--", "**"] do
    fail "four nonfatal warnings must follow source order"

def run : IO Unit := do
  captures
  roots
  arithmetic
  surfaces
  values
  ranges
  initializerOrigins
  initializerAdmission
  documents
  correctedPatternAttachments
  separateScenarios
  diagnostics
  emptyNavigationWarnings
  IO.println "behavioral source expressions, captures, arithmetic, surfaces and requests passed"

end ClaferCompiler.Tests.BehavioralElaboration
