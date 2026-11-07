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

end ClaferCompiler.Frontend.Behavioral.Expressions
