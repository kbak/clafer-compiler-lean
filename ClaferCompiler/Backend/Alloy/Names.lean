module

public import ClaferCompiler.Backend.Alloy.Syntax
public import Std.Data.String.ToNat

@[expose] public section

namespace ClaferCompiler.Backend.Alloy.Text

/-! Identity-based names never incorporate source text.
[impl->req~compiler-alloy-text~1] -/
inductive Symbol where
  | signature (id : Nat) | field (id : Nat) | binder (level : Nat) | auxiliary (id : Nat)
  deriving DecidableEq, BEq

def Symbol.number : Symbol → Nat
  | .signature n => 4 * n
  | .field n => 4 * n + 1
  | .binder n => 4 * n + 2
  | .auxiliary n => 4 * n + 3

def Symbol.name (s : Symbol) : String := "cc" ++ s.number.repr

def readSymbol (s : String) : Option Symbol := do
  let n ← (s.drop 2).toString.toNat?
  if s != "cc" ++ n.repr then none else
  match n % 4 with
  | 0 => some (.signature (n / 4))
  | 1 => some (.field (n / 4))
  | 2 => some (.binder (n / 4))
  | _ => some (.auxiliary (n / 4))

/-- Disjoint namespaces, including generated names and lexical binder levels. -/
theorem Symbol.number_injective (a b : Symbol) (h : a.number = b.number) : a = b := by
  cases a <;> cases b <;> simp_all [Symbol.number] <;> omega

/-- Source labels cannot affect this unconditional identity-injectivity result.
[proof->req~compiler-alloy-text~1] -/
theorem Symbol.name_injective (a b : Symbol) (h : a.name = b.name) : a = b := by
  apply Symbol.number_injective a b
  apply Nat.repr_injective
  simpa [Symbol.name] using h

/-- Caller metadata is kept verbatim in the sidecar, never in executable text. -/
structure SourceName where
  displayName : String
  logicalFile : Option String := none
  startByte : Option Nat := none
  endByte : Option Nat := none
  deriving DecidableEq, BEq

structure Names where
  signatures : List (Option SourceName)
  fields : List (Option SourceName)
  deriving DecidableEq, BEq

structure Mapping where
  symbol : Symbol
  name : String
  source : Option SourceName
  /-- Half-open UTF-8 byte range of the declaration's generated identifier. -/
  startByte : Nat
  endByte : Nat
  deriving DecidableEq, BEq

end ClaferCompiler.Backend.Alloy.Text
