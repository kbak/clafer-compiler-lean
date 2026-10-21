module

public import ClaferCompiler.Frontend.Parser
public import ClaferCompiler.Frontend.Constraints

@[expose] public section
namespace ClaferCompiler.Tests.Constraints
open Frontend IR.Expr

def kind : MapKind → String
  | .head => "head" | .parent => "parent" | .dereference => "dref"
  | .inclusion => "super" | .target => "target"

/-- Compare resolved IDs/roles and tree structure, ignoring only source locations
and identity widenings. In particular head/dereference and operand order survive. -/
def pathAt (s : Support n m) : Nat → Path n m → List Nat :=
  Nat.rec (fun _ => []) (fun _ next p => match p with
    | .same => [] | .inclusion e => [s.maps[e].owner]
    | .trans _ p q => next p ++ next q)

def shapeAt (s : Support n m) : Nat → Syntax n m → String :=
  Nat.rec (fun _ => "EXHAUSTED") (fun fuel next e =>
    let one := fun op a => op ++ "(" ++ next a ++ ")"
    let two := fun op a b => op ++ "(" ++ next a ++ "," ++ next b ++ ")"
    match e with
    | .boolean b => toString b | .integer i => toString i | .this => "this"
    | .extent x => s!"extent{s.classes[x]}" | .var i => s!"var{i}"
    | .map e => s!"{kind s.maps[e].kind}{s.maps[e].owner}"
    | .and a b => two "and" a b | .not a => one "not" a
    | .equal _ a b => two "eq" a b | .less a b => two "lt" a b
    | .arithmetic op a b => two (match op with | .add => "add" | .subtract => "sub") a b
    | .integerOf _ a => one "int" a | .cardinality _ a => one "count" a
    | .setOp op _ a b => two (match op with | .union => "union" | .difference => "diff" | .intersection => "inter") a b
    | .subset _ a b => two "subset" a b | .image _ _ a b => two "image" a b
    | .join _ _ _ a b => two "join" a b
    | .widenObjects _ _ p a =>
      (pathAt s (fuel + 1) p).foldl (fun text id => s!"super{id}({text})") (next a)
    | .widenRelation _ _ _ _ _ _ _ => "RELATION-WIDEN"
    | .all b d a => s!"all[{b.id}:{s.classes[b.element]}]({next d},{next a})"
    | .located _ a => next a)

def render (file source : String) : String :=
  let failure := fun e : Diagnostic => s!"error|{e.code}|{e.primary.startByte}|{e.primary.endByte}|{e.line}|{e.column}"
  match parse file source with
  | .error e => failure e
  | .ok doc => match Resolution.elaborate doc with
    | .error e => failure e
    | .ok structural => match Frontend.Constraints.elaborate doc structural with
      | .error e => failure e
      | .ok result => "ok\n" ++ String.intercalate "\n" (result.map fun ⟨o, a⟩ =>
        let term := a.body.checked.term
        s!"{o.owner.val}|{o.group.val}|{o.position.val}|{o.expression.span.startByte}|{o.expression.span.endByte}|" ++
          shapeAt a.layout.support term.budget term.raw)

def run (files : List String) : IO Unit := do
  for file in files do
    IO.println (render file (← IO.FS.readFile file) ++ "\nEND")

end ClaferCompiler.Tests.Constraints
