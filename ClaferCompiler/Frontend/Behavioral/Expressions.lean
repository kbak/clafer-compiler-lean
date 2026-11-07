module

public import ClaferCompiler.Frontend.Behavioral.Values

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

/-- Only syntactic union operands split occurrence families. Arbitrary set
expressions retain their ordinary distinct-head semantics. -/
def operandsAt : Nat → Expr → List Expr :=
  Nat.rec (fun e => [e]) (fun _ next e => match e with
    | .binary op a b _ => if op.text == "++" || op.text == "," then next a ++ next b else [e]
    | .parens a _ => next a
    | _ => [e])

-- [impl->req~compiler-behavioral-elaboration~1]
def aggregate (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold)
    (operands : List (Value k n)) : Except String (Value k n) := do
  let terms ← operands.mapM fun operand => do
    let (type, domain) ← heads operand
    let body : Primitive.Integer k (n + 1) ← match type with
      | .integers | .empty => pure (.extract (.set (.var 0)))
      | .objects d =>
        match IR.BehavioralSupport.referenceView v d with
        | some r =>
          if isInteger v r.target then pure (.extract (.set (.step (.deref d) (.var 0))))
          else throw "behavioral.expected-integer"
        | none => throw "behavioral.expected-integer"
    pure (Primitive.Integer.fold op (.cons domain .nil) body)
  let identity := if op == .sum then 0 else 1
  let binary := if op == .sum then IR.BehavioralArithmetic.Binary.add else .multiply
  return .integer (terms.foldl (fun acc term => .binary binary acc term) (.literal identity))

def chain (arrow : Token) (source : Value k n) (guard : Option (Value k n))
    (target : Value k n) : Except String (Value k n) := do
  let arrow ← if arrow.text == "-->" then pure Surface.Transitions.Arrow.immediate
    else if arrow.text == "-->>" then pure .eventual
    else throw "behavioral.arrow"
  let source ← boolean source
  let guard ← guard.mapM boolean
  let target ← match target with
    | .chain rest => pure rest
    | a => do pure ⟨[], ← boolean a⟩
  return .chain ⟨⟨source, guard, arrow⟩ :: target.links, target.target⟩

def pattern (kind : Token) (first : Value k n) (second : Option (Value k n))
    (scope : Option Token) (opener closer : Option (Value k n)) : Except String (Value k n) := do
  let p ← boolean first
  let s ← second.mapM boolean
  let q ← opener.mapM boolean
  let r ← closer.mapM boolean
  let pat ← match kind.text, s with
    | "never", none => pure (.never p)
    | "sometime", none => pure (.sometime p)
    | "lonce", none => pure (.lonce p)
    | "always", none => pure (.always p)
    | "precede", some s => pure (.precede p s)
    | "follow", some s => pure (.follow p s)
    | _, _ => throw "behavioral.pattern-shape"
  let sc ← match scope.map (·.text), q, r with
    | none, none, none => pure .suffix
    | some "before", none, some r => pure (.before r)
    | some "after", some q, none => pure (.after q)
    | some "between", some q, some r => pure (.between q r)
    | some "after until", some q, some r => pure (.afterUntil q r)
    | _, _, _ => throw "behavioral.scope-shape"
  return .formula (Surface.Patterns.expand pat sc)

/-- This frontend retains source polarity and attachment, and builds the raw
formula. Signed normalization runs only after elaboration and keeps this domain.
A successful result is not a proof of source elaboration correctness. -/
-- [impl->req~compiler-behavioral-elaboration~1]
def synthAt (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k) : Nat →
    {n : Nat} → Context k n → Option (Value k n) → Expr → Except Diagnostic (Value k n) :=
  Nat.rec (fun {_} _ _ e => .error (failure doc e "behavioral.expression-budget"))
    (fun fuel next {_} Γ cursor e => do
      let lift := fun {α : Type} (a : Except String α) => a.mapError (failure doc e)
      match e with
      | .name token => lift (Values.name v owner Γ cursor token.text)
      | .integer _ i => return .integer (.literal (Int.ofNat i))
      | .parens a _ => next Γ cursor a
      | .unary op a _ =>
        if op.text == "sum" || op.text == "product" then
          let terms ← (operandsAt (fuel + 1) a).mapM (next Γ cursor)
          lift (aggregate v (if op.text == "sum" then .sum else .product) terms)
        else lift (unary v op.text (← next Γ cursor a))
      | .binary op a b _ =>
        let a ← next Γ cursor a
        if op.text == "." then next Γ (some a) b
        else lift (binary v op.text a (← next Γ cursor b))
      | .quantified op disjoint names domain body _ =>
        let (type, domain) ← lift (heads (← next Γ cursor domain))
        let plan ← Binders.prepare Γ op names type
        let q ← Binders.quantifier op
        let body ← lift (boolean (← next plan.bodyContext none body))
        return .formula (IR.Behavioral.Binders.elaborate q.val names.length disjoint.isSome domain body)
      | .letSet _ binder value body _ =>
        if Resolution.reserved binder.text then
          throw (Resolution.errorAt binder "behavioral.reserved-binder" "Reserved binder name.")
        let (type, domain) ← lift (heads (← next Γ cursor (.name value)))
        let body ← lift (boolean (← next (push Γ binder type) none body))
        return .formula (.letSet domain body)
      | .conditional _ condition yes no _ =>
        let condition ← lift (boolean (← next Γ cursor condition))
        let yes ← next Γ cursor yes
        let no ← next Γ cursor no
        -- Only the Boolean conditional has an accepted FormulaF constructor.
        -- A collection branch must not be silently converted to presence here.
        match yes, no with
        | .formula _, .formula _ | .chain _, .formula _ | .formula _, .chain _ | .chain _, .chain _ =>
          return .formula (.ite condition (← lift (boolean yes)) (← lift (boolean no)))
        | _, _ => throw (failure doc e "behavioral.unsupported-value-conditional")
      | .transition arrow a guard b _ =>
        let a ← next Γ cursor a
        let guard ← guard.mapM (next Γ cursor)
        let b ← next Γ cursor b
        lift (chain arrow a guard b)
      | .pattern kind first second scope opener closer _ =>
        let first ← next Γ cursor first
        let second ← second.mapM (next Γ cursor)
        let opener ← opener.mapM (next Γ cursor)
        let closer ← closer.mapM (next Γ cursor)
        lift (pattern kind first second scope opener closer))

-- [impl->req~compiler-behavioral-elaboration~1]
def elaborate (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (budget : Nat) (e : Expr) : Except Diagnostic (Grouped.Formula k 0) := do
  let value ← synthAt doc v owner budget #v[] none e
  (boolean value).mapError (failure doc e)

end ClaferCompiler.Frontend.Behavioral.Expressions
