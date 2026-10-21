module

public import ClaferCompiler.Backend.Alloy.Names

@[expose] public section

namespace ClaferCompiler.Backend.Alloy.Text

/-! An independent recognizer for the canonical emitted subset. It consumes text,
resolves names and binders, and reconstructs target instructions. It imports no
printer. Delimiter reduction is a finite fold, with no recursion/fuel cutoff.
[impl->req~compiler-alloy-text~1] -/

inductive Piece where
  | word (s : String)
  | rel (r : Rel)
  | grouped (r : Rel)
  | integer (i : Integer)
  | formula (p : Formula)

def readMult : String → Option Multiplicity
  | "set" => some .set | "lone" => some .lone
  | "one" => some .one | "some" => some .some | _ => none

def leaf (s : String) : Option Piece :=
  if s == "none" then some (.rel (.empty .unary)) else
  match readSymbol s with
  | some (.signature n) => some (.rel (.sig n))
  | some (.field n) => some (.rel (.field n))
  | some (.binder n) => some (.rel (.var n))
  | _ => (s.toInt?).map fun n => .integer (.literal n)

/-- Parentheses are recognized by shape, not by reprinting or comparing strings.
Extra relation grouping distinguishes the canonical tautological `set` predicate.
Binary `none` and truth constants have their own unambiguous canonical forms. -/
def reduce : List Piece → Option Piece
  | [.word s] => leaf s
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
  | [.word q, .word name, .word ":", .rel domain, .word "|", .formula body] => do
      let .binder _ ← readSymbol name | none
      match q with
      | "all" => some (.formula (.all domain body))
      | "some" => some (.formula (.exists_ domain body))
      | _ => none
  | _ => none

/-- Flat space-delimited tokens are the lexical contract of emitted text.
Newline is a paragraph boundary; no comments, strings or arbitrary escapes occur. -/
def tokens (s : String) : List String := (s.splitOn " ").filter (· != "")

def parsePiece (ts : List String) : Option Piece := do
  let frames ← ts.foldl (fun state t => do
    let frames ← state
    match t, frames with
    | "(", _ => some ([] :: frames)
    | ")", current :: parent :: rest => do
        let p ← reduce current.reverse
        some ((p :: parent) :: rest)
    | ")", _ => none
    | _, current :: rest => some ((.word t :: current) :: rest)
    | _, [] => none) (some [[]])
  match frames with | [[p]] => some p | _ => none

/-- Resolve absolute binder levels to de Bruijn indices, in the outer domain and
extended body contexts. Unbound levels fail even if their occurrence is vacuous. -/
def resolveRel (depth : Nat) (r : Rel) : Option Rel := do
  let ops ← r.code.mapM fun op => match op with
    | .var level => if level < depth then some (.var (depth - level - 1)) else none
    | other => some other
  some ⟨ops⟩

def resolveInt (depth : Nat) : Integer → Option Integer
  | .literal n => some (.literal n)
  | .count r => (resolveRel depth r).map Integer.count

def resolveFormula (p : Formula) (depth : Nat) : Option Formula :=
  p.fold {
    truth := fun _ => some .truth, falsity := fun _ => some .falsity
    equal := fun a b d => return .equal (← resolveRel d a) (← resolveRel d b)
    subset := fun a b d => return .subset (← resolveRel d a) (← resolveRel d b)
    mult := fun m r d => return .mult m (← resolveRel d r)
    compare := fun op a b d => return .compare op (← resolveInt d a) (← resolveInt d b)
    neg := fun p d => return .neg (← p d)
    conj := fun p q d => return .conj (← p d) (← q d)
    disj := fun p q d => return .disj (← p d) (← q d)
    implies := fun p q d => return .implies (← p d) (← q d)
    all := fun r p d => return .all (← resolveRel d r) (← p (d + 1))
    exists_ := fun r p d => return .exists_ (← resolveRel d r) (← p (d + 1))
  } (fun _ => none) depth

/-- Declaration positions have `all/some NAME :` and get checked against nesting
of quantified parentheses. Multiplicity `some` does not introduce a binder. -/
def checkBinders (ts : List String) : Bool :=
  let annotated := ts.zipIdx
  let result := annotated.foldl (fun (st : Option (List Bool × Nat)) (t, i) => do
    let (stack, d) ← st
    if t == "(" then
      let q := ts[i + 1]?.getD ""
      let isBinder := (q == "all" || q == "some") && ts[i + 3]? == some ":"
      if isBinder then
        if (ts[i + 2]?).bind readSymbol == some (.binder d)
        then some (true :: stack, d + 1) else none
      else some (false :: stack, d)
    else if t == ")" then
      match stack with
      | b :: rest => some (rest, if b then d - 1 else d)
      | [] => none
    else some (stack, d)) (some ([], 0))
  result == some ([], 0)

def parseFormula (ts : List String) : Option Formula := do
  if !checkBinders ts then none else
  let .formula p ← parsePiece ts | none
  resolveFormula p 0

def readSignature (s : String) : Option Nat := do
  let .signature n ← readSymbol s | none
  some n

def readField (s : String) : Option Nat := do
  let .field n ← readSymbol s | none
  some n

def parseField (owner : Nat) (ts : List String) : Option (Nat × Field) := do
  let [name, ":", mult, target] := ts | none
  return (← readField name, ⟨owner, ← readSignature target, ← readMult mult⟩)

/-- Split punctuation-separated lists without recursive parser helpers. -/
def groups (separator : String) (ts : List String) : List (List String) :=
  (ts.foldl (fun (parts : List (List String)) t =>
    match parts with
    | [] => [[t]]
    | p :: rest => if t == separator then [] :: p :: rest else (t :: p) :: rest)
      [[]]).reverse.map List.reverse

def parseSignature (header body : List String) : Option (Nat × Signature × List (Nat × Field)) := do
  let (abstract_, header) := if header.head? == some "abstract"
    then (true, header.drop 1) else (false, header)
  let (mult, header) ← match header.head?.bind readMult with
    | some .set => none -- Alloy permits `set` on fields, not signatures.
    | some m => some (m, header.drop 1) | none => some (.set, header)
  let "sig" :: name :: tail := header | none
  let id ← readSignature name
  let parent ← match tail with
    | [] => some none
    | ["extends", n] => (readSignature n).map some
    | _ => none
  let fields ← if body.isEmpty then some [] else (groups "," body).mapM (parseField id)
  return (id, ⟨parent, abstract_, mult⟩, fields)

def parseScope (ts : List String) : Option (Nat × Scope) := do
  let (exact, ts) := if ts.head? == some "exactly" then (true, ts.drop 1) else (false, ts)
  let [size, name] := ts | none
  return (← readSignature name, ⟨← size.toNat?, exact⟩)

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
def parseLine (st : ParseState) (line : String) : Option ParseState := do
  if st.command.isSome then none else
  let ts := tokens line
  let header := ts.takeWhile (· != "{")
  let rest := ts.drop (header.length + 1)
  let body := rest.takeWhile (· != "}")
  let tail := rest.drop (body.length + 1)
  if ts[header.length]? != some "{" || rest[body.length]? != some "}" then none else
  match header with
  | ["fact"] =>
      if !tail.isEmpty then none else
      return { st with facts := st.facts ++ [← parseFormula body] }
  | [kind] => do
      let kind ← match kind with | "run" => some .run | "check" => some .check | _ => none
      let "for" :: width :: "Int" :: scopes := tail | none
      let scopes ← match scopes with
        | [] => some []
        | "," :: more => (groups "," more).mapM parseScope
        | _ => none
      return { st with command := some ⟨kind, ← parseFormula body, ← table scopes, ← width.toNat?⟩ }
  | _ =>
      if !tail.isEmpty || !st.facts.isEmpty then none else
      let (id, sig, fields) ← parseSignature header body
      return { st with signatures := st.signatures ++ [(id, sig)], fields := st.fields ++ fields }

def parse (text : String) : Option Module := do
  let lines := (text.splitOn "\n").filter (· != "")
  let st ← lines.foldl (fun st line => st.bind (fun s => parseLine s line)) (some {})
  return ⟨⟨← table st.signatures, ← table st.fields⟩, st.facts, ← st.command⟩

end ClaferCompiler.Backend.Alloy.Text
