module

public import ClaferCompiler.Frontend.Behavioral.Values
public import ClaferCompiler.Frontend.Behavioral.Names

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Expressions
open IR.Behavioral Values

def failure (doc : Document) (e : Expr) (code : String) : Diagnostic :=
  Constraints.errorAt ⟨doc.file, doc.source, []⟩ e.span code
    "Cannot elaborate this behavioral expression."
    (if code.startsWith "behavioral.unsupported" || code == "behavioral.infinite-primitive-extent" ||
      code == "behavioral.heterogeneous-parent-type" then .unsupported else .malformed)

def push (Γ : Context k n) (name : Name) (type : Ty k) : Context k (n + 1) :=
  Vector.ofFn fun i => if h : i.val = 0 then some (name, type)
    else Γ[(⟨i.val - 1, by omega⟩ : Fin n)]

/-- Only syntactic unions and parentheses split occurrence families. Other
operators, including intersection and difference, keep ordinary set semantics. -/
def AtomicOperand : Expr → Prop
  | .binary op _ _ _ => ¬ (op.text = "++" ∨ op.text = ",")
  | .parens _ _ => False
  | _ => True

instance (e : Expr) : Decidable (AtomicOperand e) := by
  unfold AtomicOperand; split <;> infer_instance

/-- Independent source rules for occurrence-preserving aggregate operands. -/
inductive Operands : Expr → List Expr → Prop where
  | atomic (h : AtomicOperand e) : Operands e [e]
  | parens (body : Operands e xs) : Operands (.parens e span) xs
  | union (spelling : op.text = "++" ∨ op.text = ",")
      (left : Operands a xs) (right : Operands b ys) :
      Operands (.binary op a b span) (xs ++ ys)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Exhaustion never returns a collapsed occurrence family. Every successful
split carries its derivation from the independent source rules above. -/
def operandsAt : Nat → (e : Expr) → Option {xs // Operands e xs} :=
  Nat.rec (fun _ => none) (fun _ next e => match e with
    | .binary op a b span =>
      if h : op.text = "++" ∨ op.text = "," then do
        let a ← next a
        let b ← next b
        return ⟨a.val ++ b.val, .union h a.property b.property⟩
      else some ⟨[.binary op a b span], .atomic h⟩
    | .parens a _ => do
      let a ← next a
      return ⟨a.val, .parens a.property⟩
    | e => if h : AtomicOperand e then some ⟨[e], .atomic h⟩ else none)

/-- Only parsed navigation names form the skipped tail. Primitive extents keep
 their existing rejection; scalar/formula expressions are not navigation names. -/
inductive NamePath : Expr → Prop where
  | name (ordinary : Resolution.integerName token.text = false) : NamePath (.name token)
  | parens (body : NamePath e) : NamePath (.parens e span)
  | dot (spelling : op.text = ".") (left : NamePath a) (right : NamePath b) :
      NamePath (.binary op a b span)

/-- A literal syntactic root, never a computed empty collection or an empty type. -/
inductive EmptyPath : Expr → Prop where
  | literal (spelling : token.text = "noclafer") : EmptyPath (.name token)
  | parens (body : EmptyPath e) : EmptyPath (.parens e span)
  | dot (spelling : op.text = ".") (left : EmptyPath a) (right : NamePath b) :
      EmptyPath (.binary op a b span)

inductive EmptyNavigation : Expr → Prop where
  | dot (spelling : op.text = ".") (left : EmptyPath a) (right : NamePath b) :
      EmptyNavigation (.binary op a b span)

-- [impl->req~compiler-behavioral-elaboration~1]
-- [proof->req~compiler-behavioral-elaboration~1]
/-- A bounded decision carries either the path derivation or its negation.
Exhaustion is separate from a negative decision and cannot select ordinary dot. -/
def namePathAt : Nat → (e : Expr) → Option (Decidable (NamePath e)) :=
  Nat.rec (fun _ => none) (fun _ next e => match e with
    | .name token => some <| if h : Resolution.integerName token.text = false then
        .isTrue (.name h) else .isFalse (by intro p; cases p; contradiction)
    | .parens e _ => do
        match ← next e with
        | .isTrue h => return .isTrue (.parens h)
        | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
    | .binary op a b _ =>
        if h : op.text = "." then do
          match ← next a with
          | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
          | .isTrue left =>
            match ← next b with
            | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
            | .isTrue right => return .isTrue (.dot h left right)
        else some (.isFalse (by intro p; cases p; contradiction))
    | .integer .. | .unary .. | .quantified .. | .letSet .. | .conditional .. | .transition .. | .pattern .. =>
        some (.isFalse (by intro p; cases p)))

def emptyPathAt : Nat → (e : Expr) → Option (Decidable (EmptyPath e)) :=
  Nat.rec (fun _ => none) (fun fuel next e => match e with
    | .name token => some <| if h : token.text = "noclafer" then
        .isTrue (.literal h) else .isFalse (by intro p; cases p; contradiction)
    | .parens e _ => do
        match ← next e with
        | .isTrue h => return .isTrue (.parens h)
        | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
    | .binary op a b _ =>
        if h : op.text = "." then do
          match ← next a with
          | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
          | .isTrue left =>
            match ← namePathAt fuel b with
            | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
            | .isTrue right => return .isTrue (.dot h left right)
        else some (.isFalse (by intro p; cases p; contradiction))
    | .integer .. | .unary .. | .quantified .. | .letSet .. | .conditional .. | .transition .. | .pattern .. =>
        some (.isFalse (by intro p; cases p)))

def emptyNavigationAt (fuel : Nat) : (e : Expr) → Option (Decidable (EmptyNavigation e))
  | .binary op a b _ =>
      if h : op.text = "." then do
        match ← emptyPathAt fuel a with
        | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
        | .isTrue left =>
          match ← namePathAt fuel b with
          | .isFalse h => return .isFalse (by intro p; cases p; contradiction)
          | .isTrue right => return .isTrue (.dot h left right)
      else some (.isFalse (by intro p; cases p; contradiction))
  | .name .. | .integer .. | .parens .. | .unary .. | .quantified .. | .letSet .. |
      .conditional .. | .transition .. | .pattern .. => some (.isFalse (by intro p; cases p))

end ClaferCompiler.Frontend.Behavioral.Expressions
