module

public import ClaferCompiler.Frontend.Defaults

@[expose] public section
namespace ClaferCompiler.Frontend.BehavioralLookup
open Resolution

/-- Requests keep dependency traversal distinct from a completed absent edge. -/
inductive Request where
  | super (path : Path)
  | child (owner : Path) (name : Name) (exclude : Path)
  deriving BEq

def diagnostic (name : Name) (code message : String)
    (category : Category := .malformed) (related : Array SourceSpan := #[]) : Diagnostic :=
  { code, message, category, related, phase := "resolve", primary := name.span,
    line := name.line, column := name.column }

def header (doc : Document) (path : Path) : Header :=
  (headerAt doc path).getD { name := ⟨"", ⟨doc.file, 0, 0⟩, 1, 1, 1⟩ }

def choose (doc : Document) (name : Name) : List Path → Except Diagnostic (Option Path)
  | [] => .ok none
  | [p] => .ok (some p)
  | ps => .error (diagnostic name "resolve.ambiguous-name" "several declarations match this name"
      .malformed (ps.toArray.map (fun p => (header doc p).name.span)))

def matching (doc : Document) (paths : Array Path) (name : Name) (exclude : Path) : List Path :=
  paths.toList.filter fun p => p != exclude && (header doc p).name.text == name.text

def requireTarget (_doc : Document) (name : Name) (self : Path)
    (answer : Option Path) : Except Diagnostic (Option Path) :=
  match answer with
  | some p => if p == self then .error (diagnostic name "resolve.inheritance-cycle" "self inheritance")
    else .ok answer
  | none => .error (diagnostic name "resolve.missing-name" "no declaration matches this name")

-- [impl->req~compiler-behavioral-structural-bridge~1]
/-- Resolve dependencies recursively, retaining cycle and exhaustion failures.
Neither an unresolved parent nor an exhausted walk is an absent superclass. -/
def resolveAt (doc : Document) (paths : Array Path) :
    Nat → List Request → Request → Except Diagnostic (Option Path) :=
  Nat.rec (fun _ request =>
      let name := match request with
        | .super p => (header doc p).name
        | .child _ name _ => name
      .error (diagnostic name "resolve.lookup-budget" "super lookup dependency bound exhausted"))
    (fun _ next active request => do
      let name := match request with
        | .super p => (header doc p).name
        | .child _ name _ => name
      if active.contains request then
        throw (diagnostic name "resolve.inheritance-cycle" "cyclic super lookup dependency")
      let next := next (request :: active)
      match request with
      | .child owner name exclude =>
        let own := (matching doc paths name exclude).filter (fun p => p.dropLast == owner)
        if !own.isEmpty then choose doc name own
        else match ← next (.super owner) with
          | none => pure none
          | some parent => next (.child parent name exclude)
      | .super self =>
        let h := header doc self
        match h.superPath with
        | some path =>
          if h.super.isSome || h.useToken.isSome || path.rest.isEmpty then
            throw (diagnostic path.first "resolve.super-shape" "invalid authored super path")
          let all := matching doc paths path.first []
          let enclosing := all.filter (fun p => p.isPrefixOf self.dropLast)
          let first ← if !enclosing.isEmpty then
              let depth := enclosing.foldl (fun n p => max n p.length) 0
              choose doc path.first (enclosing.filter (fun p => p.length == depth))
            else if all.length == 1 then choose doc path.first all
            else
              let top := all.filter (fun p => p.length == 1)
              choose doc path.first (if top.isEmpty then all else top)
          let some first ← requireTarget doc path.first [] first | return none
          let mut target := first
          for segment in path.rest do
            let some found ← requireTarget doc segment [] (← next (.child target segment []))
              | throw (diagnostic segment "resolve.missing-name" "missing path segment")
            target := found
          requireTarget doc (path.rest.getLast?.getD path.first) self (some target)
        | none =>
          match h.super.orElse (fun _ => if h.useToken.isSome then some h.name else none) with
          | none => pure none
          | some name =>
            if integerName name.text then
              throw (diagnostic name "resolve.primitive-super" "a primitive cannot be a superclass" .unsupported)
            if reserved name.text then
              throw (diagnostic name "resolve.reserved-target" "reserved name is not a declaration target" .unsupported)
            let all := matching doc paths name self
            let own := all.filter (fun p => p.dropLast == self.dropLast)
            if !own.isEmpty then choose doc name own
            else
              let inherited ← if self.dropLast.isEmpty then pure none
                else match ← next (.super self.dropLast) with
                  | none => pure none
                  | some parent => next (.child parent name self)
              if inherited.isSome then pure inherited
              else
                let best := all.foldl (fun n p => max n (proximity self.dropLast p)) 0
                let result ← choose doc name (all.filter (fun p => proximity self.dropLast p == best))
                if result.isNone && h.name.text == name.text then
                  throw (diagnostic name "resolve.inheritance-cycle" "self inheritance")
                requireTarget doc name self result)

def resolve (doc : Document) (paths : Array Path) (path : Path) : Except Diagnostic (Option Path) :=
  resolveAt doc paths (4 * (paths.size + 1) * (doc.source.utf8ByteSize + 1)) [] (.super path)

end ClaferCompiler.Frontend.BehavioralLookup
