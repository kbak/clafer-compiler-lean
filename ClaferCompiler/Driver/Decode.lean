module

public import ClaferCompiler.Driver.Json
public import ClaferCompiler.Driver.Diagnostic
public import ClaferCompiler.Backend.Alloy.Structural

@[expose] public section
namespace ClaferCompiler.Driver.Decode
open Lean IR.Structural

/-! Closed schema decoding for the explicit developer interchange.
[impl->req~compiler-cli~1]
[impl->req~compiler-ir~1] -/
structure Node where
  value : Json
  file : String
  pointer : String := ""

def bad (n : Node) (message : String) : Diagnostic := {
  code := "input.schema", phase := "decode", message, file := n.file, pointer := n.pointer }

def pointerKey (key : String) : String := key.replace "~" "~0" |>.replace "/" "~1"

def child (n : Node) (key : String) (value : Json) : Node :=
  ⟨value, n.file, n.pointer ++ "/" ++ pointerKey key⟩

def field (n : Node) (key : String) : Except Diagnostic Node :=
  match n.value.getObjVal? key with
  | .ok v => .ok (child n key v)
  | .error _ => .error (bad (child n key .null) "missing required field or expected object")

def closed (n : Node) (keys : List String) : Except Diagnostic Unit := do
  let .ok obj := n.value.getObj? | throw (bad n "expected object")
  for (key, _) in obj.toList do
    if !keys.contains key then throw (bad (child n key .null) "unknown field")
  for key in keys do
    let _ ← field n key

def string (n : Node) : Except Diagnostic String :=
  n.value.getStr?.mapError fun _ => bad n "expected string"

def natural (n : Node) : Except Diagnostic Nat :=
  n.value.getNat?.mapError fun _ => bad n "expected natural-number token"

def boolean (n : Node) : Except Diagnostic Bool :=
  n.value.getBool?.mapError fun _ => bad n "expected Boolean"

def optional (read : Node → Except Diagnostic α) (n : Node) : Except Diagnostic (Option α) :=
  match n.value with
  | .null => .ok none
  | _ => some <$> read n

def array (read : Node → Except Diagnostic α) (n : Node) : Except Diagnostic (Array α) := do
  let .ok values := n.value.getArr? | throw (bad n "expected array")
  values.zipIdx.mapM fun (v, i) => read (child n (toString i) v)

def interval (n : Node) : Except Diagnostic Bounds := do
  closed n ["lower", "upper"]
  let lower ← natural (← field n "lower")
  let high ← field n "upper"
  let upper ← if high.value == Json.str "*" then pure Upper.unbounded
    else Upper.finite <$> natural high
  return ⟨lower, upper⟩

def reference (n : Node) : Except Diagnostic (Reference Nat) := do
  let kind ← string (← field n "kind")
  match kind with
  | "basic" => closed n ["kind"]; return .basic
  | "set" | "bag" =>
    closed n ["kind", "target"]
    let target ← natural (← field n "target")
    return if kind == "set" then .set target else .bag target
  | _ => throw (bad (← field n "kind") "unknown reference constructor")

def origin (n : Node) : Except Diagnostic Origin := do
  match ← string n with
  | "root" => return .syntheticRoot
  | "user" => return .user
  | "integer" => return .integer
  | "string" => return .string
  | "boolean" => return .boolean
  | _ => throw (bad n "unknown origin constructor")

def source (n : Node) : Except Diagnostic SourceSpan := do
  closed n ["file", "startByte", "endByte"]
  return ⟨← string (← field n "file"), ← natural (← field n "startByte"),
    ← natural (← field n "endByte")⟩

def authored (n : Node) : Except Diagnostic Authored := do
  closed n ["isAbstract", "localBounds", "groupBounds"]
  return ⟨← boolean (← field n "isAbstract"),
    ← optional interval (← field n "localBounds"),
    ← optional interval (← field n "groupBounds")⟩

def declaration (n : Node) : Except Diagnostic (Declaration Nat) := do
  closed n ["id", "name", "origin", "parent", "super", "reference", "isAbstract",
    "localBounds", "groupBounds", "source", "authored"]
  return {
    id := ← natural (← field n "id"), name := ← string (← field n "name")
    origin := ← origin (← field n "origin")
    parent := ← optional natural (← field n "parent")
    super := ← optional natural (← field n "super")
    reference := ← reference (← field n "reference")
    isAbstract := ← boolean (← field n "isAbstract")
    localBounds := ← interval (← field n "localBounds")
    groupBounds := ← interval (← field n "groupBounds")
    source := ← optional source (← field n "source")
    authored := ← optional authored (← field n "authored") }

def parse (file text : String) (signed : Bool := false) : Except Diagnostic Node := do
  let value ← StrictJson.parse text signed |>.mapError fun message =>
    { code := "input.json", phase := "decode", message, file : Diagnostic }
  return ⟨value, file, ""⟩

def version (n : Node) (key expected code : String) : Except Diagnostic Unit := do
  let v ← field n key
  if (← string v) != expected then
    throw { code, phase := "decode", category := .unsupported, file := n.file
            pointer := v.pointer, message := "unsupported version or profile" : Diagnostic }

def document (file text : String) : Except Diagnostic Raw := do
  let n ← parse file text
  version n "version" "clafer-ir/1" "ir.version"
  version n "profile" "m1-effective" "ir.profile"
  closed n ["version", "profile", "root", "declarations", "parentRanks", "superRanks", "unused"]
  return {
    root := ← natural (← field n "root")
    declarations := ← array declaration (← field n "declarations")
    parentRanks := ← array natural (← field n "parentRanks")
    superRanks := ← array natural (← field n "superRanks")
    unused := ← array boolean (← field n "unused") }

def scope (n : Node) : Except Diagnostic (Nat × Backend.Alloy.Scope) := do
  closed n ["id", "size", "exact"]
  return (← natural (← field n "id"),
    ⟨← natural (← field n "size"), ← boolean (← field n "exact")⟩)

def bounds (file text : String) : Except Diagnostic Backend.Alloy.Structural.Bounds := do
  let n ← parse file text
  version n "version" "clafer-bounds/1" "bounds.version"
  closed n ["version", "objects", "bitwidth", "declarations"]
  return {
    objects := ← natural (← field n "objects")
    bitwidth := ← natural (← field n "bitwidth")
    declarations := (← array scope (← field n "declarations")).toList }

end ClaferCompiler.Driver.Decode
