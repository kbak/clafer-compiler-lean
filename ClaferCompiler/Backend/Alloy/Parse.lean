module

public import ClaferCompiler.Backend.Alloy.Names
public import Std.Internal.Parsec.String

@[expose] public section

namespace ClaferCompiler.Backend.Alloy.Text

/-! An independent Parsec grammar for the canonical emitted subset. It consumes
text and resolves names/binders without importing the printer. Recursive nesting
is bounded by input length, not an arbitrary configured depth limit.
[impl->req~compiler-alloy-text~1] -/

open Std.Internal.Parsec Std.Internal.Parsec.String

inductive Piece where
  | word (s : String)
  | rel (r : Rel)
  | grouped (r : Rel)
  | integer (i : Integer)
  | formula (p : Formula)

def required (value : Option α) : Parser α :=
  match value with | some a => pure a | none => fail "invalid canonical Alloy"

/-- Only spaces separate tokens within a line; punctuation must be separate. -/
def word : Parser String := many1Chars (satisfy (· != ' ')) <* many (pchar ' ')

def token (expected : String) : Parser Unit := attempt do
  if (← word) != expected then fail s!"expected {expected}"

def readMult : String → Option Multiplicity
  | "set" => some .set | "lone" => some .lone
  | "one" => some .one | "some" => some .some | _ => none

def signatureId : Parser Nat := do
  let some (.signature n) := readSymbol (← word) | fail "expected signature"
  return n

def leaf (depth : Nat) (s : String) : Option Piece :=
  if s == "none" then some (.rel (.empty .unary)) else
  match readSymbol s with
  | some (.signature n) => some (.rel (.sig n))
  | some (.field n) => some (.rel (.field n))
  | some (.binder n) => if n < depth then some (.rel (.var (depth - n - 1))) else none
  | _ => (s.toInt?).map fun n => .integer (.literal n)

/-- Each parenthesized form independently reconstructs its target constructor.
Extra relation grouping distinguishes the canonical tautological `set` predicate. -/
def reduce (depth : Nat) : List Piece → Option Piece
  | [.word s] => leaf depth s
  | [.rel r] => some (.grouped r)
  | [.word "none", .word "->", .word "none"] => some (.rel (.empty .binary))
  | [.word "no", .word "none"] => some (.formula .truth)
  | [.word "some", .word "none"] => some (.formula .falsity)
  | [.grouped r, .word "in", .grouped s] =>
      if r = s then some (.formula (.mult .set r)) else none
  | [.word "~", .rel r] => some (.rel (.transpose r))
  | [.word "#", .rel r] => some (.integer (.count r))
  | [.word "not", .formula p] => some (.formula (.neg p))
  | [.word m, .rel r] => do
      let m ← readMult m
      if m == .set then none else some (.formula (.mult m r))
  | [.rel a, .word op, .rel b] => match op with
      | "+" => some (.rel (.union a b)) | "&" => some (.rel (.inter a b))
      | "-" => some (.rel (.diff a b)) | "->" => some (.rel (.product a b))
      | "." => some (.rel (.join a b)) | "=" => some (.formula (.equal a b))
      | "in" => some (.formula (.subset a b)) | _ => none
  | [.integer a, .word op, .integer b] => match op with
      | "=" => some (.formula (.compare .eq a b))
      | "<" => some (.formula (.compare .lt a b))
      | "=<" => some (.formula (.compare .le a b)) | _ => none
  | [.formula a, .word op, .formula b] => match op with
      | "and" => some (.formula (.conj a b)) | "or" => some (.formula (.disj a b))
      | "implies" => some (.formula (.implies a b)) | _ => none
  | _ => none

/-- Quantifier domains use the outer depth; bodies use the extended depth.
Every recursive call follows an opening parenthesis, so input length bounds nesting. -/
def piece : Nat → Nat → Parser Piece := Nat.rec
  (fun _ => fail "nesting exceeds input length")
  (fun _ recur depth => do
    token "("
    let p ← (do
      let q ← attempt do
        let q ← word
        if q != "all" && q != "some" then fail "expected quantifier"
        let some (.binder n) := readSymbol (← word) | fail "expected binder"
        if n != depth then fail "wrong binder level"
        token ":"
        pure q
      let .rel domain ← recur depth | fail "expected domain"
      token "|"
      let .formula body ← recur (depth + 1) | fail "expected body"
      pure (.formula (if q == "all" then .all domain body else .exists_ domain body))) <|> (do
      let items ← many (recur depth <|> attempt (do
        let s ← word
        if s == "(" || s == ")" then fail "expected operand or operator"
        pure (.word s)))
      required (reduce depth items.toList))
    token ")"
    return p)

def formula (fuel : Nat) : Parser Formula := do
  let .formula p ← piece fuel 0 | fail "expected formula"
  return p

def commaSeparated (p : Parser α) : Parser (List α) :=
  (do let first ← attempt p; return first :: (← many (token "," *> p)).toList) <|> pure []

def field (owner : Nat) : Parser (Nat × Field) := do
  let some (.field id) := readSymbol (← word) | fail "expected field"
  token ":"
  let mult ← required (readMult (← word))
  return (id, ⟨owner, ← signatureId, mult⟩)

def signature : Parser (Nat × Signature × List (Nat × Field)) := do
  let abstract_ ← (token "abstract" *> pure true) <|> pure false
  let mult ← (token "lone" *> pure .lone) <|> (token "one" *> pure .one) <|>
    (token "some" *> pure .some) <|> pure .set
  token "sig"
  let id ← signatureId
  let parent ← (token "extends" *> (some <$> signatureId)) <|> pure none
  token "{"
  let fields ← commaSeparated (field id)
  token "}"
  return (id, ⟨parent, abstract_, mult⟩, fields)

def scope : Parser (Nat × Scope) := do
  let exact ← (token "exactly" *> pure true) <|> pure false
  let size ← required (← word).toNat?
  return (← signatureId, ⟨size, exact⟩)

/-- IDs must be a permutation of a complete positional table; duplicates and gaps
fail. Fields may appear under owners in a different order from their identities. -/
def table (rows : List (Nat × α)) : Option (List α) := do
  if !(rows.map Prod.fst).all (fun id => id < rows.length) ||
      !(rows.map Prod.fst).Pairwise (· ≠ ·) then none else
  (List.range rows.length).mapM fun i => (rows.find? (fun row => row.1 == i)).map Prod.snd

structure ParseState where
  signatures : List (Nat × Signature) := []
  fields : List (Nat × Field) := []
  facts : List Formula := []
  command : Option Command := none

/-- One complete declaration, fact or final command occupies each emitted line. -/
def line (fuel : Nat) (st : ParseState) : Parser ParseState := do
  if st.command.isSome then fail "command must be last"
  let _ ← many (pchar ' ')
  let next ← (do
    token "fact"
    token "{"
    let p ← formula fuel
    token "}"
    pure { st with facts := st.facts ++ [p] }) <|> (do
    let kind ← (token "run" *> pure .run) <|> (token "check" *> pure .check)
    token "{"
    let p ← formula fuel
    token "}"
    token "for"
    let width ← required (← word).toNat?
    token "Int"
    let scopes ← many (token "," *> scope)
    pure { st with command := some ⟨kind, p, ← required (table scopes.toList), width⟩ }) <|> (do
    if !st.facts.isEmpty then fail "signatures must precede facts"
    let (id, sig, fields) ← signature
    pure { st with signatures := st.signatures ++ [(id, sig)], fields := st.fields ++ fields })
  eof
  return next

def parse (text : String) : Option Module := do
  let lines := (text.splitOn "\n").filter (· != "")
  let st ← lines.foldlM (fun st text =>
    match (line text.length st).run text with
    | .ok next => some next | .error _ => none) {}
  return ⟨⟨← table st.signatures, ← table st.fields⟩, st.facts, ← st.command⟩

end ClaferCompiler.Backend.Alloy.Text
