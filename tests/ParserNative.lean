module

public import ClaferCompiler.Frontend.Parser

@[expose] public section
namespace ClaferCompiler.Tests.Parser
open Frontend

def cardShape (c : Option Cardinality) : String :=
  c.map (fun c => String.join (c.tokens.toList.map (·.text))) |>.getD "_"

def spanValid (source : String) (s : SourceSpan) : Bool :=
  s.startByte ≤ s.endByte && s.endByte ≤ source.utf8ByteSize &&
    (String.fromUTF8? (source.toUTF8.extract 0 s.startByte)).isSome &&
    (String.fromUTF8? (source.toUTF8.extract 0 s.endByte)).isSome

inductive Task where
  | text (s : String)
  | expr (e : Expr)
  | element (e : Element)

/-- Independent test observation using a standard-library loop over an explicit
work list. Parentheses determine the tree but are omitted from this rendering. -/
def render (source : String) (initial : List Task) : Option (String × Bool) := Id.run do
  let mut tasks := initial
  let mut output := ""
  let mut valid := true
  for _ in [:8 * source.utf8ByteSize + 32] do
    let t :: rest := tasks | return some (output, valid)
    tasks := rest
    match t with
    | .text s => output := output ++ s
    | .expr e =>
      valid := valid && spanValid source e.span
      match e with
      | .name t | .integer t _ => output := output ++ t.text
      | .parens body _ => tasks := .expr body :: tasks
      | .unary t body _ =>
        valid := valid && spanValid source t.span
        tasks := [.text ("(" ++ t.text ++ " "), .expr body, .text ")"] ++ tasks
      | .binary t left right _ =>
        valid := valid && spanValid source t.span
        tasks := [.text ("(" ++ t.text ++ " "), .expr left, .text " ", .expr right, .text ")"] ++ tasks
      | .quantified t n domain body _ =>
        valid := valid && spanValid source t.span && spanValid source n.span
        tasks := [.text ("(" ++ t.text ++ " " ++ n.text ++ " "), .expr domain,
          .text " ", .expr body, .text ")"] ++ tasks
    | .element e =>
      valid := valid && spanValid source e.span
      match e with
      | .constraint es _ =>
        tasks := [.text "["] ++ (es.map Task.expr).intersperse (.text " ") ++ [.text "]"] ++ tasks
      | .declaration h es _ =>
        valid := valid && spanValid source h.name.span &&
          h.abstractToken.all (fun t => spanValid source t.span) &&
          h.useToken.all (fun t => spanValid source t.span) &&
          h.super.all (fun t => spanValid source t.span) &&
          h.reference.all (fun (a, n) => spanValid source a.span && spanValid source n.span) &&
          [h.group, h.cardinality].all (fun c => c.all (fun c => c.tokens.all (fun t => spanValid source t.span)))
        let headerText := s!"({if h.useToken.isSome then "use" else "decl"} {h.name.text} {h.abstractToken.isSome} {cardShape h.group} {cardShape h.cardinality} {h.super.map (·.text) |>.getD "_"} {h.reference.map (fun (a, n) => a.text ++ n.text) |>.getD "_"} ["
        tasks := [.text headerText] ++ (es.map Task.element).intersperse (.text " ") ++ [.text "])"] ++ tasks
  return none

-- Requirement: compiler-parser; trace artifacts are in docs/parser.md.
def authoredChecks : IO Unit := do
  let .ok d := parse "authored.cfr" "abstract xor Type 02..*\n  r ->> integer ?\n"
    | throw (IO.userError "authored fixture rejected")
  let [.declaration h [.declaration r [] _] s] := d.elements
    | throw (IO.userError "authored nesting changed")
  unless h.abstractToken.isSome && h.group.map (·.lower) == some 1 &&
      h.group.bind (·.upper) == some 1 && h.cardinality.map (·.lower) == some 2 &&
      h.cardinality.bind (·.upper) == none && cardShape h.cardinality == "02..*" &&
      r.group.isNone && r.super.isNone && r.abstractToken.isNone &&
      r.cardinality.map (·.lower) == some 0 && r.cardinality.bind (·.upper) == some 1 &&
      r.reference.map (fun (a, n) => (a.text, n.text)) == some ("->>", "integer") &&
      s.startByte == 0 && h.name.span.startByte == 13 && h.name.span.endByte == 17 do
    throw (IO.userError "authored flags, bounds, spelling, or spans changed")

-- Requirement: compiler-parser; trace artifacts are in docs/parser.md.
-- Requirement: compiler-diagnostics; trace artifacts are in docs/parser.md.
def observe (source : String) : IO String := do
  let result := parse "fixture.cfr" source
  match result with
  | .ok d =>
    let some (shape, spansValid) := render source ((d.elements.map Task.element).intersperse (.text "\n"))
      | throw (IO.userError "test observation exceeded source-derived budget")
    unless d.source == source && d.file == "fixture.cfr" && spansValid do
      throw (IO.userError "lost source or invalid span")
    return "ok\n" ++ shape
  | .error e =>
    unless e.version == 1 && e.primary.file == "fixture.cfr" && spanValid source e.primary &&
        e.line > 0 && e.column > 0 && e.related.isEmpty do
      throw (IO.userError "invalid diagnostic")
    let category := if e.category == .unsupported then "unsupported" else "malformed"
    return s!"{category}|{e.code}|{e.phase}|{e.primary.startByte}|{e.primary.endByte}|{e.line}|{e.column}"

/-- Separate native harness; production CLI ownership remains #19/#20. -/
def run (files : List String) : IO Unit := do
  authoredChecks
  for file in files do
    IO.println (← observe (← IO.FS.readFile file))
    IO.println "END"

end ClaferCompiler.Tests.Parser
