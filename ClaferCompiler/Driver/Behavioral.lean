module

public import ClaferCompiler.Driver.Decode
public import ClaferCompiler.Backend.Alloy.Behavioral
public import ClaferCompiler.Backend.Alloy.Temporal.Print

@[expose] public section
namespace ClaferCompiler.Driver.Behavioral
open Lean Decode IR.Behavioral

/-- Construction retains an executable traversal budget and its erased proof. -/
structure Sized (α : Type) [SizeOf α] where
  value : α
  weight : Nat
  enough : sizeOf value < weight

def unsupported (n : Node) (message : String) : Diagnostic :=
  { bad n message with code := "behavioral.constructor", category := .unsupported }

def items (n : Node) : Except Diagnostic (Array Json) :=
  n.value.getArr?.mapError fun _ => bad n "expected tagged array"

def arg (n : Node) (i : Nat) : Except Diagnostic Node := do
  let values ← items n
  let some v := values[i]? | throw (bad n "missing constructor argument")
  return child n (toString i) v

def tag (n : Node) : Except Diagnostic String := do string (← arg n 0)

def arity (n : Node) (size : Nat) : Except Diagnostic Unit := do
  if (← items n).size != size then throw (bad n "wrong constructor arity")

def declarationIndex (m : IR.Structural.Core k) (n : Node) : Except Diagnostic (Fin k) := do
  let id ← natural n
  let some i := IR.Structural.lookup m.declarations id
    | throw (bad n "unknown declaration ID")
  return i

def step (m : IR.Structural.Core k) (n : Node) : Except Diagnostic (Step k) := do
  match ← tag n with
  | "parent" => arity n 1; return .parent
  | "child" => arity n 2; return .child (← declarationIndex m (← arg n 1))
  | "deref" => arity n 2; return .deref (← declarationIndex m (← arg n 1))
  | _ => throw (unsupported n "unsupported navigation constructor")

def stepWeight : Step k → Nat
  | .parent => 2
  | .child d | .deref d => d.val + 3

theorem stepWeight_enough (s : Step k) : sizeOf s < stepWeight s := by
  cases s <;> simp [stepWeight] <;> omega

-- [impl->req~compiler-behavioral-cli~1]
def setStep (m : IR.Structural.Core k)
    (next : {depth : Nat} → Node → Except Diagnostic (Sized (SetExpr k depth)))
    {depth : Nat} (n : Node) : Except Diagnostic (Sized (SetExpr k depth)) := do
  match ← tag n with
  | "empty" => arity n 1; return ⟨.empty, k + depth + 2, by simp <;> omega⟩
  | "this" => arity n 1; return ⟨.this, k + depth + 2, by simp <;> omega⟩
  | "root" => arity n 1; return ⟨.root, k + depth + 2, by simp <;> omega⟩
  | "var" =>
    arity n 2
    let index ← natural (← arg n 1)
    if h : index < depth then return ⟨.var ⟨index, h⟩, k + depth + index + 3, by simp <;> omega⟩
    else throw (bad (← arg n 1) "lexical index is out of range")
  | "extent" =>
    arity n 2
    let d ← declarationIndex m (← arg n 1)
    return ⟨.extent d, k + depth + d.val + 3, by simp <;> omega⟩
  | "union" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.union a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "inter" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.inter a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "diff" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.diff a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "step" =>
    arity n 3
    let s ← step m (← arg n 1)
    let a ← next (← arg n 2)
    return ⟨.step s a.value, stepWeight s + a.weight + k + depth + 1, by
      have := stepWeight_enough s; have := a.enough; simp <;> omega⟩
  | "thisStep" =>
    arity n 2
    let s ← step m (← arg n 1)
    return ⟨.thisStep s, stepWeight s + k + depth + 1, by
      have := stepWeight_enough s; simp <;> omega⟩
  | _ => throw (unsupported n "unsupported set constructor")

def setAt (m : IR.Structural.Core k) : Nat → {depth : Nat} → Node →
    Except Diagnostic (Sized (SetExpr k depth)) :=
  Nat.rec (fun {_} n => .error (bad n "invalid expression nesting"))
    (fun _ next => setStep m next)

def atom (m : IR.Structural.Core k) (fuel : Nat) {depth : Nat} (n : Node) :
    Except Diagnostic (Sized (Atom k depth)) := do
  match ← tag n with
  | "inhabited" =>
    arity n 2
    let a ← setAt m fuel (← arg n 1)
    return ⟨.inhabited a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "equal" =>
    arity n 3
    let a ← setAt m fuel (← arg n 1)
    let b ← setAt m fuel (← arg n 2)
    return ⟨.equal a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "subset" =>
    arity n 3
    let a ← setAt m fuel (← arg n 1)
    let b ← setAt m fuel (← arg n 2)
    return ⟨.subset a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | _ => throw (unsupported n "unsupported atom; primitive observations need a separate profile")

def quantifier (n : Node) : Except Diagnostic Quantifier := do
  match ← string n with
  | "all" => return .all
  | "some" => return .some
  | "no" => return .no
  | "one" => return .one
  | "lone" => return .lone
  | _ => throw (unsupported n "unsupported quantifier")

def quantifierWeight : Quantifier → Nat
  | .all | .some | .no | .one | .lone => 2

theorem quantifierWeight_enough (q : Quantifier) : sizeOf q < quantifierWeight q := by
  cases q <;> decide

-- [impl->req~compiler-behavioral-cli~1]
def formulaStep (m : IR.Structural.Core k) (fuel : Nat)
    (next : {depth : Nat} → Node → Except Diagnostic (Sized (Formula k depth)))
    {depth : Nat} (n : Node) : Except Diagnostic (Sized (Formula k depth)) := do
  match ← tag n with
  | "truth" => arity n 1; return ⟨.truth, k + depth + 2, by simp <;> omega⟩
  | "atom" =>
    arity n 2
    let a ← atom m fuel (← arg n 1)
    return ⟨.atom a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "not" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.not a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "next" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.next a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "eventually" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.eventually a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "always" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.always a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "initially" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.initially a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "finally" =>
    arity n 2
    let a ← next (← arg n 1)
    return ⟨.«finally» a.value, a.weight + k + depth + 1, by have := a.enough; simp <;> omega⟩
  | "and" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.and a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "or" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.or a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "implies" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.implies a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "iff" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.iff a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "xor" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.xor a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "strongUntil" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.strongUntil a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "weakUntil" =>
    arity n 3
    let a ← next (← arg n 1)
    let b ← next (← arg n 2)
    return ⟨.weakUntil a.value b.value, a.weight + b.weight + k + depth + 1, by
      have := a.enough; have := b.enough; simp <;> omega⟩
  | "ite" =>
    arity n 4
    let c ← next (← arg n 1)
    let a ← next (← arg n 2)
    let b ← next (← arg n 3)
    return ⟨.ite c.value a.value b.value, c.weight + a.weight + b.weight + k + depth + 1, by
      have := c.enough; have := a.enough; have := b.enough; simp <;> omega⟩
  | "quant" =>
    arity n 4
    let q ← quantifier (← arg n 1)
    let d ← setAt m fuel (← arg n 2)
    let a ← next (depth := depth + 1) (← arg n 3)
    return ⟨.quant q d.value a.value, quantifierWeight q + d.weight + a.weight + k + depth + 1, by
      have := quantifierWeight_enough q; have := d.enough; have := a.enough; simp <;> omega⟩
  | "letSet" =>
    arity n 3
    let d ← setAt m fuel (← arg n 1)
    let a ← next (depth := depth + 1) (← arg n 2)
    return ⟨.letSet d.value a.value, d.weight + a.weight + k + depth + 1, by
      have := d.enough; have := a.enough; simp <;> omega⟩
  | _ => throw (unsupported n "unsupported formula constructor")

def formulaAt (m : IR.Structural.Core k) : Nat → {depth : Nat} → Node →
    Except Diagnostic (Sized (Formula k depth)) :=
  Nat.rec (fun {_} n => .error (bad n "invalid expression nesting"))
    (fun fuel next => formulaStep m fuel next)

structure ParsedAttachment (k : Nat) where
  entry : Attachment k
  weight : Nat
  enough : ∀ f, entry.body = .formula f → sizeOf f < weight

def attachment (m : IR.Structural.Core k) (fuel : Nat) (n : Node) :
    Except Diagnostic (ParsedAttachment k) := do
  closed n ["id", "owner", "kind", "body", "source"]
  let kind ← field n "kind"
  if (← string kind) != "constraint" then throw (unsupported kind "only hard constraints are admitted")
  let f ← formulaAt m fuel (← field n "body")
  let a : Attachment k := {
    id := ← natural (← field n "id"), owner := ← natural (← field n "owner")
    body := .formula f.value, source := ← optional source (← field n "source") }
  return ⟨a, f.weight, by intro b hb; cases hb; exact f.enough⟩

def budget (as : List (ParsedAttachment k)) : Nat :=
  as.foldr (fun a rest => a.weight + rest) 1

theorem within_budget (as : List (ParsedAttachment k)) (a : ParsedAttachment k)
    (h : a ∈ as) : a.weight ≤ budget as := by
  induction as with
  | nil => simp at h
  | cons b bs ih =>
    simp only [List.mem_cons] at h
    simp only [budget, List.foldr_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; change a.weight ≤ b.weight + budget bs; omega

structure Input (k : Nat) where
  admitted : Admitted k
  fuel : Nat
  enough : ∀ a ∈ admitted.document.attachments, ∀ f,
    a.body = .formula f → sizeOf f < fuel

-- [impl->req~compiler-behavioral-cli~1]
def document (file text : String) : Except Diagnostic (Σ k, Input k) := do
  let n ← parse file text
  version n "version" "clafer-behavioral-ir/1" "behavioral.version"
  version n "profile" "behavioral-core/1" "behavioral.profile"
  closed n ["version", "profile", "structure", "attachments"]
  let rawNode ← field n "structure"
  let raw ← Decode.document file rawNode.value.compress |>.mapError fun d =>
    { d with pointer := rawNode.pointer ++ d.pointer }
  let v ← IR.Structural.validateRaw raw |>.mapError (admissionDiagnostic file)
  let entries ← array (attachment v.core (text.utf8ByteSize + 1)) (← field n "attachments")
  let doc : Document raw.declarations.size := {
    version := "clafer-behavioral-ir/1", profile := "behavioral-core/1"
    core := v.core, certificate := v.certificate
    attachments := entries.toList.map (·.entry) }
  if hm : metadataChecks doc then
    if hb : supportedBodies doc then
      pure ⟨_, ⟨⟨doc, rfl, rfl, v.coreChecked, v.supportChecked, hm, hb⟩,
        budget entries.toList, by
          intro a ha f hf
          obtain ⟨entry, he, rfl⟩ := List.mem_map.mp ha
          exact Nat.lt_of_lt_of_le (entry.enough f hf) (within_budget _ entry he)⟩⟩
    else throw (unsupported n "unsupported attachment body")
  else throw (admissionDiagnostic file ⟨.malformed, "behavioral.metadata", "/attachments", none⟩)

-- [impl->req~compiler-behavioral-cli~1]
def bounds (file text : String) : Except Diagnostic Backend.Alloy.Behavioral.Bounds := do
  let n ← parse file text
  version n "version" "clafer-behavioral-bounds/1" "bounds.version"
  closed n ["version", "objects", "bitwidth", "declarations", "minSteps", "maxSteps"]
  let low ← natural (← field n "minSteps")
  let high ← natural (← field n "maxSteps")
  if low == 0 || high < low then throw (bad n "expected 1 ≤ minSteps ≤ maxSteps")
  return { objects := ← natural (← field n "objects")
           bitwidth := ← natural (← field n "bitwidth")
           declarations := (← array scope (← field n "declarations")).toList
           minSteps := low, maxSteps := high }

structure Product where
  text : String
  compiled : Backend.Alloy.Behavioral.Compiled
  mappings : List Backend.Alloy.Text.Mapping

def signatureName (i : Nat) : String := "this/" ++ (Backend.Alloy.Text.Symbol.signature i).name
def fieldName (owner i : Nat) : String :=
  signatureName owner ++ "/" ++ (Backend.Alloy.Text.Symbol.field i).name

-- [impl->req~compiler-behavioral-cli~1]
def Product.json (p : Product) : Json :=
  let m := p.compiled.module.raw
  Json.mkObj [
    ("version", toJson "clafer-behavioral-compilation/1"),
    ("profile", toJson "behavioral-core/1"), ("alloy", toJson p.text),
    ("declarations", toJson (p.compiled.declarations.map fun d => Json.mkObj [
      ("id", toJson d.id), ("name", toJson d.name),
      ("signature", toJson (signatureName d.signature)),
      ("referenceField", toJson (d.dereference.map (fieldName 0)))])),
    ("signatures", Json.mkObj (m.schema.declarations.signatures.zipIdx.map fun (s, i) =>
      (signatureName i, Json.mkObj [
        ("mutable", toJson (m.schema.mutableSignatures[i]?.getD false)),
        ("abstract", toJson s.isAbstract),
        ("parent", toJson (s.parent.map signatureName |>.getD "univ"))]))),
    ("fields", Json.mkObj (m.schema.declarations.fields.zipIdx.map fun (f, i) =>
      (fieldName f.owner i, Json.mkObj [
        ("mutable", toJson (m.schema.mutableFields[i]?.getD false)), ("arity", toJson (2 : Nat))]))),
    ("scopes", Json.mkObj (m.command.scopes.zipIdx.map fun (s, i) =>
      (signatureName i, Json.mkObj [("count", toJson s.size), ("exact", toJson s.exact)]))),
    ("bitwidth", toJson m.command.bitwidth),
    ("minSteps", toJson m.command.minSteps), ("maxSteps", toJson m.command.maxSteps),
    ("attachments", toJson p.compiled.attachments)]

def compileText (inputFile input boundsFile boundsText : String)
    (objects bitwidth : Option Nat := none) : Except Diagnostic Product := do
  let ⟨_, doc⟩ ← document inputFile input
  let b ← bounds boundsFile boundsText
  let b := { b with objects := objects.getD b.objects, bitwidth := bitwidth.getD b.bitwidth }
  let compiled ← Backend.Alloy.Behavioral.compile doc.admitted b doc.fuel doc.enough
    |>.mapError (backendDiagnostic boundsFile (admissionDiagnostic inputFile))
  let rendered ← Backend.Alloy.Temporal.Text.render compiled.module
      (Backend.Alloy.Temporal.Text.anonymousNames compiled.module.raw) |>.mapError fun _ =>
    { code := "compiler.render", phase := "serialization", category := .operational
      message := "generated temporal text failed checked reconstruction" : Diagnostic }
  return ⟨rendered.text, compiled, rendered.mappings⟩

end ClaferCompiler.Driver.Behavioral
