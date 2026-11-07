module

public import ClaferCompiler.Frontend.Behavioral.Parser
public import ClaferCompiler.Frontend.Behavioral.Modifiers
public import ClaferCompiler.Frontend.Behavioral.Headers

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralDeclarations
open Frontend.Behavioral

def fail (message : String) : IO α := throw (IO.userError message)

structure Loaded where
  source : Document
  bound : BoundDeclarations source
  modifiers : BoundModifiers bound

def load (source : String) : IO Loaded := do
  let .ok doc := parseBehavioral IR.BehavioralStructural.profile "declarations.cfr" source
    | fail ("parse: " ++ source)
  let b ← match bindDeclarations IR.BehavioralStructural.profile doc with
    | .ok b => pure b
    | .error e => fail (e.code ++ ": " ++ e.message ++ "\n" ++ source)
  let .ok modifiers := bindModifiers b | fail "modifier binding"
  return ⟨doc, b, modifiers⟩

def idOf (v : Loaded) (name : String) : IO (Fin v.bound.resolved.count) :=
  match (List.finRange v.bound.resolved.count).find? (fun d =>
      (v.bound.resolved.candidate.core.get d).name == name) with
  | some d => pure d
  | none => fail ("missing declaration: " ++ name)

def declared (v : Loaded) (name : String) : IO (List String) := do
  return v.modifiers.declared[← idOf v name].map IR.Behavioral.Modifiers.spelling

def effective (v : Loaded) (name : String) : IO (List String) := do
  return (IR.Behavioral.Modifiers.effective v.bound.resolved.admitted v.modifiers.declared
    (← idOf v name)).map IR.Behavioral.Modifiers.spelling

-- [utest->req~compiler-behavioral-elaboration~1]
def run : IO Unit := do
  let v ← load "enum Colour = Red | Blue\nTarget\nabstract finalref finaltarget Ref ->> Target\n  assert [ X some this ]\nfinaltarget finalref finalref r : Ref\nowner\n  initial flag ?\n  value -> int = 2\n  phase ? --> flag\n  [ all x; y : r | X (x = y) ]\nassert [some Red]\n"
  unless (← declared v "Colour") == [] && (← declared v "Red") == ["final"] &&
      (← declared v "Blue") == ["final"] do fail "dynamic enum final markers"
  unless (← declared v "r") == ["finaltarget", "finalref", "finalref"] do
    fail "authored modifier order/repetition"
  unless (← effective v "r") == ["finaltarget", "finalref", "finalref", "finalref", "finaltarget"] do
    fail "effective inherited modifiers"
  unless (← effective v "flag") == ["initial"] do fail "initial modifier"
  let occurrences := properties v.bound
  let ownerNames := occurrences.map fun p =>
    ((v.bound.resolved.candidate.core.get p.owner).name, p.kind)
  unless ownerNames == [("Sing", .assertion), ("Ref", .assertion), ("owner", .constraint)] do
    fail "assertion polarity/attachment or inherited property duplicated"
  let some grouped := occurrences.find? (·.kind == .constraint) | fail "constraint occurrence"
  match grouped.expression with
  | .quantified _ _ [x, y] _ (.unary next _ _) _ =>
      unless x.text == "x" && y.text == "y" && next.text == "X" do fail "binder identities"
  | _ => fail "grouped binder or temporal body erased"
  for name in ["value", "phase"] do
    let d ← idOf v name
    let some path := v.bound.resolved.candidate.paths[d] | fail "authored path"
    let some h := headerAt v.bound.expanded path | fail "header/path correspondence"
    unless h.structural.name.text == name do fail "marker shifted a declaration path"
    if name == "value" then
      unless h.initializer.isSome do fail "initializer lost"
    else unless h.transition.isSome do fail "declaration transition lost"
  let .ok derived := headerProperties v.bound | fail "header properties"
  let origins := derived.map fun p =>
    ((v.bound.resolved.candidate.core.get p.declaration).name,
      (v.bound.resolved.candidate.core.get p.owner).name, p.kind)
  unless origins == [("value", "owner", .initializer), ("phase", "phase", .transition)] do
    fail "initializer/transition attached to the wrong context"
  match (derived.map (fun p => p.toHeaderProperty.expression) : List Expr) with
  | [.binary implies (.unary someHeads (.name heads) _) (.binary eq (.name left) (.integer _ 2) _) _,
      .transition arrow (.name source) none (.name target) _] =>
    unless implies.text == "=>" && someHeads.text == "some" && heads.text == "value" &&
        eq.text == "=" && left.text == "value" && arrow.text == "-->" &&
        source.text == "this" && target.text == "flag" do fail "header sugar changed"
  | _ => fail "header sugar gained an anchor or changed its expression"
  for source in ["a = 2\n", "a --> a\n", "assert [0 = 0]\n"] do
    let v ← load source
    unless v.bound.resolved.candidate.core.declarations.any (·.origin == .integer) do
      fail "expression-only model missing integer universe"
  for order in ["finalref finaltarget", "finaltarget finalref", "finalref finalref finaltarget",
      "finaltarget finaltarget finalref"] do
    for arrow in ["->", "->>"] do
      for inherited in [false, true] do
        let source := if inherited then
          "Target\nabstract Ref " ++ arrow ++ " Target\n" ++ order ++ " ref : Ref\n"
          else "Target\n" ++ order ++ " ref " ++ arrow ++ " Target\n"
        let v ← load source
        unless (← declared v "ref") == order.splitOn " " &&
            (← effective v "ref") == order.splitOn " " do
          fail "order/repetition × direct/inherited × single/set reference matrix"
  for source in ["A\n  enum B = C\n", "enum A = X | X\n", "A : B\nB : A\n"] do
    match parseBehavioral IR.BehavioralStructural.profile "bad.cfr" source with
    | .error _ => pure ()
    | .ok doc =>
      let .error _ := bindDeclarations IR.BehavioralStructural.profile doc | fail "invalid model admitted"
  let .error wrong := bindDeclarations "m1-effective" v.source | fail "profile separation"
  unless wrong.code == "behavioral.profile" do fail "profile diagnostic"
  let t : Frontend.Token := ⟨"A", ⟨"manual.cfr", 0, 1⟩, 1, 1, 1⟩
  let nested : Document := ⟨"manual.cfr", "A\n  enum B = C\n",
    [.declaration { structural := { name := t } }
      [.enumeration { t with text := "B" } [{ t with text := "C" }] t.span] t.span]⟩
  let .error enumError := bindDeclarations IR.BehavioralStructural.profile nested
    | fail "manually constructed nested enum admitted"
  unless enumError.code == "behavioral.nested-enum" do fail "nested enum diagnostic"
  let .error _ := Frontend.parse "static.cfr" "finalref finaltarget a\n" | fail "static baseline widened"
  IO.println "behavioral declaration, enum, modifier and property binding passed"

end ClaferCompiler.Tests.BehavioralDeclarations
