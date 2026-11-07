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
def namePath : (e : Expr) → Option {_u : Unit // NamePath e}
  | .name token => if h : Resolution.integerName token.text = false then some ⟨(), .name h⟩ else none
  | .parens e _ => do let body ← namePath e; return ⟨(), .parens body.property⟩
  | .binary op a b _ => if h : op.text = "." then do
      let left ← namePath a
      let right ← namePath b
      return ⟨(), .dot h left.property right.property⟩
    else none
  | _ => none

def emptyPath : (e : Expr) → Option {_u : Unit // EmptyPath e}
  | .name token => if h : token.text = "noclafer" then some ⟨(), .literal h⟩ else none
  | .parens e _ => do let body ← emptyPath e; return ⟨(), .parens body.property⟩
  | .binary op a b _ => if h : op.text = "." then do
      let left ← emptyPath a
      let right ← namePath b
      return ⟨(), .dot h left.property right.property⟩
    else none
  | _ => none

def emptyNavigation : (e : Expr) → Option {_u : Unit // EmptyNavigation e}
  | .binary op a b _ => if h : op.text = "." then do
      let left ← emptyPath a
      let right ← namePath b
      return ⟨(), .dot h left.property right.property⟩
    else none
  | _ => none

-- [proof->req~compiler-behavioral-elaboration~1]
theorem namePath_complete (h : NamePath e) : (namePath e).isSome = true := by
  induction h with
  | name h => simp [namePath, h]
  | parens h ih =>
    rename_i body span
    cases he : namePath body <;> simp_all [namePath]
  | dot h left right ihl ihr =>
    rename_i a b op span
    cases ha : namePath a <;> cases hb : namePath b <;> simp_all [namePath]

theorem emptyPath_complete (h : EmptyPath e) : (emptyPath e).isSome = true := by
  induction h with
  | literal h => simp [emptyPath, h]
  | parens h ih =>
    rename_i body span
    cases he : emptyPath body <;> simp_all [emptyPath]
  | dot h left right ih =>
    rename_i a b op span
    have hr := namePath_complete right
    cases ha : emptyPath a <;> cases hb : namePath b <;> simp_all [emptyPath]

theorem emptyNavigation_complete (h : EmptyNavigation e) : (emptyNavigation e).isSome = true := by
  cases h with
  | dot h left right =>
    rename_i a b op span
    have hl := emptyPath_complete left
    have hr := namePath_complete right
    cases ha : emptyPath a <;> cases hb : namePath b <;> simp_all [emptyNavigation]

end ClaferCompiler.Frontend.Behavioral.Expressions
