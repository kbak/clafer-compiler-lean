module

public import ClaferCompiler.Frontend.ConstraintsRules
public import ClaferCompiler.Frontend.Defaults

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr

structure Navigation (c : IR.Structural.Core n) (s : Support n m)
    (x : Fin n) (a : Syntax n m) (name : String) where
  target : Fin n
  term : Term n m
  derivation : Navigate c s x a name target term.raw

def navigateAt (c : IR.Structural.Core n) (s : Support n m) :
    Nat → (x : Fin n) → (a : Term n m) → (name : String) →
      Except String (Navigation c s x a.raw name) :=
  Nat.rec (fun _ _ _ => .error "constraint.reference-cycle") (fun _ next x a name => do
    if Resolution.integerName name then throw "constraint.infinite-primitive-extent"
    if hn : name = "parent" then
      for e in List.finRange m do
        if h : s.maps[e].kind = .parent ∧ s.maps[e].source = x then
          return ⟨s.maps[e].target, .image x s.maps[e].target a (.map e), by subst name; exact .parent h.1 h.2⟩
      throw "constraint.no-parent"
    if hn : name = "dref" then
      for e in List.finRange m do
        if h : s.maps[e].kind = .dereference ∧ s.maps[e].source = x then
          return ⟨s.maps[e].target, .image x s.maps[e].target a (.map e), by subst name; exact .dereference h.1 h.2⟩
      throw "constraint.not-reference"
    let paths := superPaths s x
    for (depth, (p, path)) in paths.zipIdx |>.map (fun (p, i) => (i, p)) do
      for y in List.finRange n do
        if hf : Field c x name depth p y then
          if hp : ValidWiden s x p path then
            for e in List.finRange m do
              if he : s.maps[e].kind = .head ∧ s.maps[e].source = p ∧ s.maps[e].target = y then
                return ⟨y, .image p y (.widenObjects x p path a) (.map e),
                  .field hf hp he.1 he.2.1 he.2.2⟩
    if hf : HasField c x name then throw "constraint.ambiguous-navigation"
    else
      for e in List.finRange m do
        if he : s.maps[e].kind = .dereference ∧ s.maps[e].source = x then
          let b ← next s.maps[e].target (.image x s.maps[e].target a (.map e)) name
          return ⟨b.target, b.term, .throughReference hf he.1 he.2 b.derivation⟩
      throw "constraint.missing-navigation")

structure ScopeEntry (s : Support n m) where
  depth : Nat
  vertex : Fin n
  term : Term n m
  derivation : ScopePath s s.context .this depth vertex term.raw

def scopes (s : Support n m) : List (ScopeEntry s) :=
  (List.range n).foldl (fun (acc : List (ScopeEntry s)) _ =>
    match acc.getLast? with
    | none => acc
    | some p =>
      (List.finRange m).foldl (fun found e =>
        if h : s.maps[e].kind = .parent ∧ s.maps[e].source = p.vertex then
          acc ++ [(⟨p.depth + 1, s.maps[e].target,
            .image p.vertex s.maps[e].target p.term (.map e), .parent p.derivation h.1 h.2⟩ : ScopeEntry s)]
        else found) acc) [(⟨0, s.context, .this, .here⟩ : ScopeEntry s)]

structure BoundName (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (cursor : Cursor n m) (name : String) where
  type : Ty n
  term : Term n m
  derivation : NameRule c s Γ cursor name type term.raw

def absoluteName (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (name : String) : Except String (BoundName c s Γ none name) := do
  if hn : name = "this" then return ⟨.collection (.objects s.context), .this, by subst name; exact .this⟩
  if hn : name = "parent" ∨ name = "dref" then
    let b ← navigateAt c s (n + 1) s.context .this name
    return ⟨_, b.term, .special hn b.derivation⟩
  for i in List.range Γ.length do
    match hi : Γ[i]? with
    | none => pure ()
    | some b =>
      if hn : b.name = name then
        if hf : ∀ k : Fin i, ∀ a, Γ[k.val]? = some a → a.name ≠ name then
          return ⟨_, .var i, .local hi hn hf⟩
  if hl : NoLocal Γ name then
    if hn : name ≠ "this" ∧ name ≠ "parent" ∧ name ≠ "dref" then
      for p in scopes s do
        if hp : p.vertex ≠ c.root then
          if hc : NoContext c s.context name p.depth then
            if decide (ReachableName c p.vertex name) then
              let b ← navigateAt c s (n + 1) p.vertex p.term name
              return ⟨_, b.term, .contextual hl hn.1 hn.2.1 hn.2.2 hp hc p.derivation b.derivation⟩
      if hc : NoContext c s.context name (n + 1) then
        for y in List.finRange n do
          if hg : Global c name y then
            return ⟨_, .extent y, .global hl hn.1 hn.2.1 hn.2.2 hc hg⟩
        let candidates := (List.finRange n).filter fun y => (c.get y).name == name
        if candidates.length > 1 then throw "constraint.ambiguous-name"
  if Resolution.integerName name then throw "constraint.infinite-primitive-extent"
  throw "constraint.missing-name"

def nameAt (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (cursor : Option (Fin n × Term n m)) (name : String) :
    Except String (BoundName c s Γ (cursor.map fun (x, a) => (x, a.raw)) name) :=
  match cursor with
  | none => absoluteName c s Γ name
  | some (x, a) => do
    let b ← navigateAt c s (n + 1) x a name
    return ⟨_, b.term, .relative b.derivation⟩

end ClaferCompiler.Frontend.Constraints
