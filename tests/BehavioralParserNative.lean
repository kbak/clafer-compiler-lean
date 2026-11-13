module

public import ClaferCompiler.Frontend.Behavioral.Parser
public import tests.ParserNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralParser
open Frontend Frontend.Behavioral

inductive Task where
  | text (s : String)
  | expr (e : Behavioral.Expr)
  | element (e : Behavioral.Element)

def render (source : String) (initial : List Task) : Option (String × Bool) := Id.run do
  let mut tasks := initial
  let mut output := ""
  let mut valid := true
  for _ in [:20 * source.utf8ByteSize + 32] do
    let t :: rest := tasks | return some (output, valid)
    tasks := rest
    match t with
    | .text s => output := output ++ s
    | .expr e =>
      valid := valid && Parser.spanValid source e.span
      match e with
      | .name t | .integer t _ => output := output ++ t.text
      | .parens body _ => tasks := .expr body :: tasks
      | .unary t body _ =>
        valid := valid && Parser.spanValid source t.span
        tasks := [.text ("(" ++ t.text ++ " "), .expr body, .text ")"] ++ tasks
      | .binary t left right _ =>
        valid := valid && Parser.spanValid source t.span
        tasks := [.text ("(" ++ t.text ++ " "), .expr left, .text " ", .expr right, .text ")"] ++ tasks
      | .quantified t disj ns domain body _ =>
        valid := valid && Parser.spanValid source t.span &&
          disj.all (fun t => Parser.spanValid source t.span) && ns.all (fun n => Parser.spanValid source n.span)
        tasks := [.text ("(" ++ t.text ++ (if disj.isSome then " disj " else " ") ++
            String.intercalate ";" (ns.map (·.text)) ++ " "),
          .expr domain, .text " ", .expr body, .text ")"] ++ tasks
      | .letSet t n v body _ =>
        valid := valid && [t, n].all (fun t => Parser.spanValid source t.span)
        tasks := [.text ("(let " ++ n.text ++ " "), .expr v, .text " ", .expr body, .text ")"] ++ tasks
      | .conditional _ c a b _ =>
        tasks := [.text "(if ", .expr c, .text " ", .expr a, .text " ", .expr b, .text ")"] ++ tasks
      | .transition op a guard b _ =>
        valid := valid && Parser.spanValid source op.span
        tasks := [.text ("(" ++ op.text ++ " "), .expr a, .text " "] ++
          (guard.toList.map Task.expr) ++ [.text " | ", .expr b, .text ")"] ++ tasks
      | .pattern kind a b scope q r _ =>
        valid := valid && Parser.spanValid source kind.span && scope.all (fun t => Parser.spanValid source t.span)
        tasks := [.text ("(" ++ kind.text ++ " "), .expr a] ++
          (b.toList.flatMap fun e => [.text " ", .expr e]) ++
          [.text (" @" ++ (scope.map (·.text)).getD "suffix")] ++
          ((q.toList ++ r.toList).flatMap fun e => [.text " ", .expr e]) ++ [.text ")"] ++ tasks
    | .element e =>
      valid := valid && Parser.spanValid source e.span
      match e with
      | .property kind es _ =>
        tasks := [.text (if kind == .assertion then "assert[" else "[")] ++
          (es.map Task.expr).intersperse (.text " ") ++ [.text "]"] ++ tasks
      | .enumeration n literals _ =>
        valid := valid && (n :: literals).all (fun n => Parser.spanValid source n.span)
        output := output ++ "(enum " ++ n.text ++ " " ++ String.intercalate "|" (literals.map (·.text)) ++ ")"
      | .declaration h es _ =>
        let s := h.structural
        valid := valid && Parser.spanValid source s.name.span &&
          h.modifiers.all (fun t => Parser.spanValid source t.span) &&
          s.abstractToken.all (fun t => Parser.spanValid source t.span) &&
          s.useToken.all (fun t => Parser.spanValid source t.span) &&
          s.super.all (fun t => Parser.spanValid source t.span) &&
          s.superPath.all (fun p => Parser.spanValid source p.span &&
            (p.first :: p.rest).all (fun t => Parser.spanValid source t.span)) &&
          s.reference.all (fun (a, n) => Parser.spanValid source a.span && Parser.spanValid source n.span) &&
          [s.group, s.cardinality].all (fun c => c.all (fun c => c.tokens.all (fun t => Parser.spanValid source t.span)))
        let superName := s.super.map (·.text) |>.orElse (fun _ =>
          s.superPath.map (fun p => String.intercalate "." ((p.first :: p.rest).map (·.text))))
        let headerText := s!"({if s.useToken.isSome then "use" else "decl"} {s.name.text} {s.abstractToken.isSome} {String.intercalate "," (h.modifiers.map (·.text))} {Parser.cardShape s.group} {Parser.cardShape s.cardinality} {superName.getD "_"} {s.reference.map (fun (a, n) => a.text ++ n.text) |>.getD "_"}"
        let init := h.initializer.toList.flatMap fun (t, e) => [.text (" " ++ t.text ++ " "), .expr e]
        let trans := h.transition.toList.flatMap fun (t, g, e) =>
          [.text (" " ++ t.text ++ " ")] ++ (g.toList.map Task.expr) ++ [.text " | ", .expr e]
        tasks := [.text headerText] ++ init ++ trans ++ [.text " ["] ++
          (es.map Task.element).intersperse (.text " ") ++ [.text "])"] ++ tasks
  return none

-- [utest->req~compiler-behavioral-frontend~1]
-- [utest->req~compiler-diagnostics~1]
def observe (source : String) : IO String := do
  match parseBehavioral IR.BehavioralStructural.profile "fixture.cfr" source with
  | .ok d =>
    let some (shape, spans) := render source ((d.elements.map Task.element).intersperse (.text "\n"))
      | throw (IO.userError "test rendering exhausted")
    unless spans && d.source == source && d.file == "fixture.cfr" do
      throw (IO.userError "source metadata mismatch")
    return "ok\n" ++ shape
  | .error e =>
    unless e.version == 1 && e.primary.file == "fixture.cfr" && Parser.spanValid source e.primary &&
        e.line > 0 && e.column > 0 do throw (IO.userError "invalid diagnostic")
    let category := if e.category == .unsupported then "unsupported" else "malformed"
    return s!"{category}|{e.code}|{e.phase}|{e.primary.startByte}|{e.primary.endByte}|{e.line}|{e.column}"

def run (files : List String) : IO Unit := do
  let .error e := parseBehavioral "structural" "fixture.cfr" "initial A"
    | throw (IO.userError "profile selection was bypassed")
  unless e.code == "behavioral.profile" && e.category == .unsupported do
    throw (IO.userError "wrong profile diagnostic")
  for file in files do
    IO.println (← observe (← IO.FS.readFile file))
    IO.println "END"
end ClaferCompiler.Tests.BehavioralParser
