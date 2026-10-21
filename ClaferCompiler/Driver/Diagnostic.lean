module

public import Lean.Data.Json.FromToJson.Basic
public import ClaferCompiler.Frontend.Surface

@[expose] public section
namespace ClaferCompiler.Driver
open Lean

/-! Versioned diagnostics preserve IR identities without fabricating source
coordinates. Source diagnostic serialization is reusable by #20.
[impl->req~compiler-diagnostics~1] -/
inductive Category where
  | malformed | unsupported | operational
  deriving BEq

def Category.name : Category → String
  | .malformed => "malformed" | .unsupported => "unsupported" | .operational => "operational"

def Category.exitCode : Category → UInt32
  | .malformed => 2 | .unsupported => 3 | .operational => 1

structure Diagnostic where
  code : String
  phase : String
  category : Category := .malformed
  message : String
  file : String := ""
  pointer : String := ""
  declaration : Option Nat := none
  source : Option Frontend.Diagnostic := none

def sourceSpanJson (s : IR.Structural.SourceSpan) : Json := Json.mkObj [
  ("kind", toJson "source"), ("file", toJson s.file),
  ("startByte", toJson s.startByte), ("endByte", toJson s.endByte)]

def sourceDiagnosticJson (d : Frontend.Diagnostic) : Json := Json.mkObj [
  ("version", toJson d.version), ("code", toJson d.code), ("phase", toJson d.phase),
  ("category", toJson (match d.category with | .malformed => "malformed" | .unsupported => "unsupported")),
  ("message", toJson d.message),
  ("primary", Json.mkObj [("kind", toJson "source"), ("file", toJson d.primary.file),
    ("startByte", toJson d.primary.startByte), ("endByte", toJson d.primary.endByte),
    ("line", toJson d.line), ("column", toJson d.column)]),
  ("related", Json.arr (d.related.map sourceSpanJson))]

def Diagnostic.json (d : Diagnostic) : Json :=
  if let some source := d.source then sourceDiagnosticJson source else Json.mkObj [
  ("version", toJson (1 : Nat)), ("code", toJson d.code), ("phase", toJson d.phase),
  ("category", toJson d.category.name), ("message", toJson d.message),
  ("primary", Json.mkObj [("kind", toJson "ir"), ("file", toJson d.file),
    ("pointer", toJson d.pointer), ("declaration", toJson d.declaration)]),
  ("related", Json.arr #[])]

def Diagnostic.text (d : Diagnostic) : String :=
  if let some source := d.source then
    s!"{d.category.name} [{d.code}] {toJson source.primary.file |>.compress}:{source.line}:{source.column}: {d.message}"
  else s!"{d.category.name} [{d.code}] {toJson d.file |>.compress}{d.pointer}: {d.message}"

def Diagnostic.ofSource (d : Frontend.Diagnostic) : Diagnostic := {
  code := d.code, phase := d.phase, message := d.message, file := d.primary.file
  category := match d.category with | .malformed => .malformed | .unsupported => .unsupported
  source := some d }

def admissionDiagnostic (file : String) (d : IR.Structural.Diagnostic) : Diagnostic := {
  code := d.code, phase := "admission", file, pointer := d.pointer, declaration := d.declaration
  category := match d.category with | .malformed => .malformed | .unsupported => .unsupported
  message := "IR admission failed; check the M1 guards, identities and certificates" }

end ClaferCompiler.Driver
