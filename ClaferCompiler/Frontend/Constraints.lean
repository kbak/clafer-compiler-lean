module

public import ClaferCompiler.Frontend.ConstraintsOps
public import ClaferCompiler.Frontend.ConstraintsNames
public import ClaferCompiler.Frontend.Resolve

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr

abbrev cursorSyntax (cursor : Option (Fin n × Term n m)) : Cursor n m :=
  cursor.map fun (x, a) => (x, a.raw)

def failure (doc : Document) (e : Frontend.Expr) (code : String) : Diagnostic :=
  errorAt doc e.span code "Cannot elaborate this static expression."
    (if code.startsWith "constraint.unsupported" || code == "constraint.infinite-primitive-extent"
     then .unsupported else .malformed)

def synthAt (doc : Document) (c : IR.Structural.Core n) (s : Support n m) : Nat →
    (Γ : List (Local n)) → (cursor : Option (Fin n × Term n m)) → (e : Frontend.Expr) →
    Except Diagnostic (Synth c s Γ (cursorSyntax cursor) e) :=
  Nat.rec (fun _ _ e => .error (errorAt doc e.span "constraint.traversal-budget" "Expression traversal exhausted."))
    (fun _ next Γ cursor e =>
      match e with
      | .name token => do
        let a ← (nameAt c s Γ cursor token.text).mapError (failure doc e)
        return ⟨a.type, .located token.span a.term, .name a.derivation⟩
      | .integer token value => do return ⟨.integer, .located token.span (.integer value), .integer⟩
      | .parens e span => do
        let a ← next Γ cursor e
        return ⟨a.type, .located span a.term, .parens a.derivation⟩
      | .unary op e span => do
        let a ← next Γ cursor e
        (unary op span a).mapError (failure doc e)
      | .binary op left right span => do
        let a ← next Γ cursor left
        if ho : op.text = "." then
          match ht : a.type with
          | .collection (.objects x) =>
            let b ← next Γ (some (x, a.term)) right
            return ⟨b.type, .located span b.term,
              .dot ho (by rw [← ht]; exact a.derivation) b.derivation⟩
          | _ => throw ((failure doc e) "constraint.join-endpoint")
        else
          let b ← next Γ cursor right
          (binary op span a b).mapError (failure doc e)
      | .quantified op binder domain body span => do
        if Resolution.reserved binder.text then
          throw (errorAt doc binder.span "constraint.reserved-binder" "Reserved binder name.")
        let d ← next Γ cursor domain
        match ht : d.type with
        | .collection (.objects x) =>
          let b : Local n := ⟨(Γ.map (·.id)).foldl max 0 + 1, binder.text, x⟩
          if hf : ∀ old ∈ Γ, old.id ≠ b.id then
            let a ← next (b :: Γ) none body
            let a ← (expect a .boolean).mapError (failure doc e)
            (quantify op binder span b rfl hf ⟨d.term, by rw [← ht]; exact d.derivation⟩ a).mapError (failure doc e)
          else throw ((failure doc e) "constraint.internal-binder")
        | _ => throw ((failure doc e) "constraint.binder-domain"))

structure Body (c : IR.Structural.Core n) (s : Support n m) (e : Frontend.Expr) where
  checked : Checked s [] .boolean
  derivation : Elaborates c s [] none true e .boolean checked.term.raw

/-- Type checking does not discharge singleton or target range obligations. -/
def elaborateBody (doc : Document) (c : IR.Structural.Core n) (s : Support n m)
    (e : Frontend.Expr) : Except Diagnostic (Body c s e) := do
  let a ← synthAt doc c s (doc.source.utf8ByteSize + 1) [] none e
  let b ← (expect a .boolean).mapError fun code => errorAt doc e.span code "Expected a hard constraint."
  if ht : b.term.Typed s [] .boolean then
    if ho : b.term.Observed s then return ⟨⟨b.term, ht, ho⟩, b.derivation⟩
    else throw (errorAt doc e.span "constraint.infinite-primitive-extent" "Infinite primitive observation." .unsupported)
  else throw (errorAt doc e.span "constraint.type-scope-or-span" "Invalid type, lexical scope or source span.")

/-- Attachment identity indexes the unchanged authored body list, including
empty brackets and multiple bodies at one occurrence. -/
structure Occurrence (doc : Document) (c : Resolution.Candidate n) where
  owner : Fin n
  group : Fin (Resolution.constraints doc c owner).length
  position : Fin ((Resolution.constraints doc c owner)[group].1.length)

def Occurrence.expression (o : Occurrence doc c) : Frontend.Expr :=
  (Resolution.constraints doc c o.owner)[o.group].1[o.position]

def Occurrence.span (o : Occurrence doc c) : SourceSpan :=
  (Resolution.constraints doc c o.owner)[o.group].2

def occurrences (doc : Document) (c : Resolution.Candidate n) : List (Occurrence doc c) :=
  (List.finRange n).flatMap fun owner =>
    (List.finRange (Resolution.constraints doc c owner).length).flatMap fun group =>
      (List.finRange ((Resolution.constraints doc c owner)[group].1.length)).map fun position =>
        ⟨owner, group, position⟩

structure Attached (doc : Document) (c : Resolution.Candidate n) (o : Occurrence doc c) where
  layout : Layout c.core o.owner
  body : Body c.core layout.support o.expression

def elaborateOccurrence (doc : Document) (c : Resolution.Candidate n) (o : Occurrence doc c) :
    Except Diagnostic (Attached doc c o) := do
  let l ← (layout c.core o.owner).mapError fun code => errorAt doc o.span code "Invalid support."
  let b ← elaborateBody doc c.core l.support o.expression
  return ⟨l, b⟩

/-- Every authored body is returned in owner/group/body order; no inherited
copies are invented. The dependent pair retains its original occurrence. -/
def elaborate (doc : Document) (e : Resolution.Elaborated doc) :
    Except Diagnostic (List ((o : Occurrence doc e.candidate) × Attached doc e.candidate o)) :=
  (occurrences doc e.candidate).mapM fun o => do
    return ⟨o, ← elaborateOccurrence doc e.candidate o⟩

end ClaferCompiler.Frontend.Constraints
