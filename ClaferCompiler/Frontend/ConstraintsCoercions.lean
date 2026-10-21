module

public import ClaferCompiler.Frontend.ConstraintsRules

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr
variable {n m : Nat} {c : IR.Structural.Core n} {s : Support n m}
  {Γ : List (Local n)} {cursor : Cursor n m} {e a b : Frontend.Expr}

structure Conversion (s : Support n m) (t : Ty n) (a : Syntax n m) (u : Ty n) where
  term : Term n m
  derivation : Coerces s t a u term.raw

def convertAt (s : Support n m) : Nat → (t : Ty n) → (a : Term n m) → (u : Ty n) →
    Except String (Conversion s t a.raw u) :=
  Nat.rec (fun _ _ _ => .error "constraint.coercion-cycle") (fun _ next t a u => do
    if ht : t = u then return ⟨a, by subst u; exact .same⟩
    match ht : t, hu : u with
    | .collection k, .boolean =>
      return ⟨.less (.integer 0) (.cardinality k a), by simp only [ht, hu]; exact .some⟩
    | .collection (.objects x), .integer =>
      if hi : s.integer[x] = true then return ⟨.integerOf x a, by simp only [ht, hu]; exact .integer hi⟩
      for e in List.finRange m do
        if he : s.maps[e].kind = .dereference ∧ s.maps[e].source = x then
          let b ← next (.collection (.objects s.maps[e].target))
            (.image x s.maps[e].target a (.map e)) .integer
          return ⟨b.term, by simpa only [ht, hu] using (Coerces.trans (.dereference (a := a.raw) he.1 he.2) b.derivation (by intro h; cases h))⟩
      throw "constraint.expected-integer"
    | .collection (.objects x), .collection (.objects y) =>
      for (z, p) in superPaths s x do
        if z = y then
          if hp : ValidWiden s x y p then return ⟨.widenObjects x y p a, by simp only [ht, hu]; exact .widen hp⟩
      for e in List.finRange m do
        if he : s.maps[e].kind = .dereference ∧ s.maps[e].source = x then
          let b ← next (.collection (.objects s.maps[e].target))
            (.image x s.maps[e].target a (.map e)) u
          return ⟨b.term, by simpa only [ht, hu] using (Coerces.trans (.dereference (a := a.raw) he.1 he.2) b.derivation (by simp [hu]))⟩
      throw "constraint.incompatible-endpoints"
    | _, _ => throw "constraint.type-mismatch")

structure RawAt (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (cursor : Cursor n m) (e : Frontend.Expr) (t : Ty n) where
  term : Term n m
  derivation : Elaborates c s Γ cursor false e t term.raw

structure At (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (cursor : Cursor n m) (e : Frontend.Expr) (t : Ty n) where
  term : Term n m
  originalType : Ty n
  original : Term n m
  source : Elaborates c s Γ cursor false e originalType original.raw
  conversion : Coerces s originalType original.raw t term.raw

theorem At.derivation (a : At c s Γ cursor e t) : Elaborates c s Γ cursor true e t a.term.raw :=
  .coerce a.source a.conversion

def expect (a : Synth c s Γ cursor e) (t : Ty n) : Except String (At c s Γ cursor e t) := do
  let b ← convertAt s (n + 2) a.type a.term t
  return ⟨b.term, a.type, a.term, a.derivation, b.derivation⟩

def valueAt (s : Support n m) : Nat → (t : Ty n) → (a : Term n m) →
    Except String ((u : Ty n) × Conversion s t a.raw u) :=
  Nat.rec (fun _ _ => .error "constraint.coercion-cycle") (fun _ next t a => do
    match ht : t with
    | .collection (.objects x) =>
      if hi : s.integer[x] = true then return ⟨.integer, ⟨.integerOf x a, by simp only [ht]; exact .integer hi⟩⟩
      for e in List.finRange m do
        if he : s.maps[e].kind = .dereference ∧ s.maps[e].source = x then
          let result ← next (.collection (.objects s.maps[e].target)) (.image x s.maps[e].target a (.map e))
          let u := result.1
          let b := result.2
          if hb : u ≠ .boolean then
            return ⟨u, ⟨b.term, by simpa only [ht] using (Coerces.trans (.dereference (a := a.raw) he.1 he.2) b.derivation hb)⟩⟩
          else throw "constraint.internal-value"
      return ⟨t, ⟨a, .same⟩⟩
    | _ => return ⟨t, ⟨a, .same⟩⟩)

def value (a : Synth c s Γ cursor e) : Except String ((t : Ty n) × At c s Γ cursor e t) := do
  let result ← valueAt s (n + 2) a.type a.term
  return ⟨result.1, ⟨result.2.term, a.type, a.term, a.derivation, result.2.derivation⟩⟩

structure Pair (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n))
    (cursor : Cursor n m) (left right : Frontend.Expr) where
  type : Ty n
  left : At c s Γ cursor left type
  right : At c s Γ cursor right type

def adapt (a : At c s Γ cursor e t) (u : Ty n) : Except String (At c s Γ cursor e u) := do
  let b ← convertAt s (n + 2) t a.term u
  if hu : u ≠ .boolean then
    return ⟨b.term, a.originalType, a.original, a.source, .trans a.conversion b.derivation hu⟩
  else throw "constraint.internal-adaptation"

def alignValues (l : (t : Ty n) × At c s Γ cursor a t)
    (r : (t : Ty n) × At c s Γ cursor b t) : Except String (Pair c s Γ cursor a b) := do
  if h : l.1 = r.1 then
    return ⟨l.1, l.2, h.symm ▸ r.2⟩
  match l.1, r.1 with
  | .collection (.objects x), .collection (.objects _) =>
    for (z, _) in superPaths s x do
      match adapt l.2 (.collection (.objects z)), adapt r.2 (.collection (.objects z)) with
      | .ok ll, .ok rr => return ⟨.collection (.objects z), ll, rr⟩
      | _, _ => pure ()
    throw "constraint.incompatible-endpoints"
  | .integer, _ | _, .integer => return ⟨.integer, ← adapt l.2 .integer, ← adapt r.2 .integer⟩
  | _, _ => throw "constraint.type-mismatch"


def align (left : Synth c s Γ cursor a) (right : Synth c s Γ cursor b)
    (values : Bool) : Except String (Pair c s Γ cursor a b) := do
  if !values then
    let direct := alignValues ⟨left.type, ← expect left left.type⟩ ⟨right.type, ← expect right right.type⟩
    if let .ok pair := direct then return pair
  alignValues (← value left) (← value right)

end ClaferCompiler.Frontend.Constraints
