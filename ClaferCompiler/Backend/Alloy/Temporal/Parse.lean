module

public import ClaferCompiler.Backend.Alloy.Temporal.Syntax
public import ClaferCompiler.Backend.Alloy.Parse

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Temporal.Text
open Std.Internal.Parsec Std.Internal.Parsec.String
open Alloy.Text (Symbol readSymbol required word token readMult signatureId commaSeparated table scope)

-- [impl->req~compiler-alloy-temporal-text~1]
/-- Independent canonical grammar. Reuses Parsec and static token/table helpers,
but never imports the temporal printer or receives its input module. -/
inductive Piece where
  | word (s : String) | rel (r : Rel) | grouped (r : Rel)
  | integer (n : Integer) | formula (p : Formula)

def readUnary : String → Option Unary
  | "not" => some .neg | "after" => some .after | "always" => some .always
  | "eventually" => some .eventually | "before" => some .before
  | "once" => some .once | "historically" => some .historically | _ => none

def readBinary : String → Option Binary
  | "and" => some .conj | "or" => some .disj | "implies" => some .implies
  | "until" => some .until | "releases" => some .releases
  | "since" => some .since | "triggered" => some .triggered | _ => none

def leaf (depth : Nat) (s : String) : Option Piece :=
  match s with
  | "none" => some (.rel (.empty .unary))
  | "univ" => some (.rel .univ) | "iden" => some (.rel .iden) | "Int" => some (.rel .ints)
  | _ => match readSymbol s with
    | some (.signature n) => some (.rel (.sig n))
    | some (.field n) => some (.rel (.field n))
    | some (.binder n) => if n < depth then some (.rel (.var (depth - n - 1))) else none
    | _ => s.toInt?.map fun n => .integer (.literal n)

def reduce (depth : Nat) : List Piece → Option Piece
  | [.word s] => leaf depth s
  | [.rel r] => some (.grouped r)
  | [.word "none", .word "->", .word "none"] => some (.rel (.empty .binary))
  | [.word "no", .word "none"] => some (.formula .truth)
  | [.word "some", .word "none"] => some (.formula .falsity)
  | [.grouped r, .word "in", .grouped s] =>
      if r == s then some (.formula (.mult .set r)) else none
  | [.rel r, .word "'"] => some (.rel (.prime r))
  | [.word "~", .rel r] => some (.rel (.transpose r))
  | [.word "#", .rel r] => some (.integer (.count r))
  | [.word "plus", .word "[", .integer a, .word ",", .integer b, .word "]"] =>
      some (.integer (.add a b))
  | [.word "minus", .word "[", .integer a, .word ",", .integer b, .word "]"] =>
      some (.integer (.subtract a b))
  | [.word op, .formula p] => (readUnary op).map fun u => .formula (.unary u p)
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
  | [.formula p, .word op, .formula q] => (readBinary op).map fun b => .formula (.binary b p q)
  | _ => none

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
  pure p

def field (owner : Nat) : Parser (Nat × (Alloy.Field × Bool)) := do
  let mutable ← (token "var" *> pure true) <|> pure false
  let some (.field id) := readSymbol (← word) | fail "expected field"
  token ":"
  let mult ← required (readMult (← word))
  pure (id, (⟨owner, ← signatureId, mult⟩, mutable))

def signature : Parser (Nat × (Alloy.Signature × Bool) × List (Nat × (Alloy.Field × Bool))) := do
  let mutable ← (token "var" *> pure true) <|> pure false
  let abstract_ ← (token "abstract" *> pure true) <|> pure false
  let mult ← (token "lone" *> pure .lone) <|> (token "one" *> pure .one) <|>
    (token "some" *> pure .some) <|> pure .set
  token "sig"
  let id ← signatureId
  let parent ← (token "extends" *> (some <$> signatureId)) <|> pure none
  token "{"
  let fields ← commaSeparated (field id)
  token "}"
  pure (id, (⟨parent, abstract_, mult, false⟩, mutable), fields)

structure ParseState where
  signatures : List (Nat × (Alloy.Signature × Bool)) := []
  fields : List (Nat × (Alloy.Field × Bool)) := []
  facts : List Formula := []
  command : Option Command := none

def line (fuel : Nat) (st : ParseState) : Parser ParseState := do
  if st.command.isSome then fail "command must be last"
  let _ ← many (pchar ' ')
  let next ← (do
    token "fact"; token "{"
    let p ← formula fuel
    token "}"
    pure { st with facts := st.facts ++ [p] }) <|> (do
    let kind ← (token "run" *> pure .run) <|> (token "check" *> pure .check)
    token "{"
    let p ← formula fuel
    token "}"; token "for"
    let width ← required (← word).toNat?
    token "Int"; token ","
    let lo ← required (← word).toNat?
    token ".."
    let hi ← required (← word).toNat?
    token "steps"
    let scopes ← many (token "," *> scope)
    pure { st with command := some ⟨kind, p, ← required (table scopes.toList), width, lo, hi⟩ }) <|> (do
    if !st.facts.isEmpty then fail "signatures must precede facts"
    let (id, sig, fields) ← signature
    pure { st with signatures := st.signatures ++ [(id, sig)], fields := st.fields ++ fields })
  eof
  pure next

def parse (text : String) : Option Module := do
  let lines := (text.splitOn "\n").filter (· != "")
  let st ← lines.foldlM (fun st text =>
    match (line text.length st).run text with
    | .ok next => some next | .error _ => none) {}
  let sigs ← table st.signatures
  let fields ← table st.fields
  pure ⟨⟨⟨sigs.map Prod.fst, fields.map Prod.fst⟩, sigs.map Prod.snd, fields.map Prod.snd⟩,
    st.facts, ← st.command⟩

end ClaferCompiler.Backend.Alloy.Temporal.Text
