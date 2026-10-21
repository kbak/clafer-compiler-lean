module

public import Lean.Data.Json.Parser
public import Lean.Data.Json.FromToJson.Basic

@[expose] public section
namespace ClaferCompiler.Driver.StrictJson
open Lean Std.Internal.Parsec Std.Internal.Parsec.String

/-! The developer protocol uses only natural-number tokens. Reuse Parsec and
JSON values/escaping, but reject information loss in the generic JSON parser.
[impl->req~compiler-cli~1]
[impl->req~compiler-ir~1] -/

def escaped : Parser Char := do
  if (← peek!) != 'u' then
    Lean.Json.Parser.escapedChar
  else
    skip
    let a ← Lean.Json.Parser.hexChar
    let b ← Lean.Json.Parser.hexChar
    let c ← Lean.Json.Parser.hexChar
    let d ← Lean.Json.Parser.hexChar
    let n := (a <<< 12) ||| (b <<< 8) ||| (c <<< 4) ||| d
    if n < 0xD800 || n ≥ 0xE000 then
      return Char.ofNat n.toNat
    else if n < 0xDC00 then
      Lean.Json.Parser.finishSurrogatePair n
    else fail "unpaired surrogate"

def stringChar : Parser Char := do
  let c ← peek!
  if c == '"' then fail "end of string"
  skip
  if c == '\\' then escaped
  else if c.toNat < 32 then fail "control character in string"
  else return c

def string : Parser String := do
  skipChar '"'
  let s ← manyChars stringChar
  skipChar '"'
  return s

def natural : Parser Json := do
  let s ← many1Chars digit
  if s.length > 1 && s.startsWith "0" then fail "leading zero"
  match s.toNat? with
  | some n => return toJson n
  | none => fail "expected a natural-number token"

def entries (p : Parser α) (close : Char) : Parser (Array α) := do
  if (← peek!) == close then
    skip
    return #[]
  let first ← p
  let rest ← many (skipChar ',' *> ws *> p)
  skipChar close
  return #[first] ++ rest

/-- Nesting consumes fuel derived from input bytes; no arbitrary depth profile. -/
def valueStep (previous : Parser Json) : Parser Json := do
  let c ← peek!
  let result ← if c == '{' then do
    skip; ws
    let pairs ← entries (do
      let key ← string
      ws; skipChar ':'; ws
      let v ← previous
      return (key, v)) '}'
    let mut seen : List String := []
    for (key, _) in pairs do
      if seen.contains key then fail "duplicate object key"
      seen := key :: seen
    pure (Json.mkObj pairs.toList)
  else if c == '[' then do
    skip; ws
    Json.arr <$> entries previous ']'
  else if c == '"' then Json.str <$> string
  else if c == 't' then skipString "true" *> pure (Json.bool true)
  else if c == 'f' then skipString "false" *> pure (Json.bool false)
  else if c == 'n' then skipString "null" *> pure Json.null
  else natural
  ws
  return result

def parse (input : String) : Except String Json :=
  let grammar := Nat.repeat valueStep (input.utf8ByteSize + 1)
    (fail "JSON nesting exceeds input length")
  Parser.run (ws *> grammar <* eof) input

end ClaferCompiler.Driver.StrictJson
