module

public import ClaferCompiler.Frontend.Behavioral.ExpressionRules

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Expressions
open IR.Behavioral Values ValueRules

/-- Every successful branch returns its derivation from `Elaborates`. The
traversal budget affects only diagnostics, never the meaning of a successful tree.
Signed normalization runs later, preserving the original strict domain. -/
-- [impl->req~compiler-behavioral-elaboration~1]
-- [proof->req~compiler-behavioral-elaboration~1]
def certifiedAt (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k) : Nat →
    {n : Nat} → (Γ : Context k n) → (cursor : Option (Value k n)) → (e : Expr) →
      Except Diagnostic {value // Elaborates v owner Γ cursor e value} :=
  Nat.rec (fun {_} _ _ e => .error (failure doc e "behavioral.expression-budget"))
    (fun fuel next {_} Γ cursor e =>
      let lift := fun {α : Type} (a : Except String α) => a.mapError (failure doc e)
      match (motive := ∀ source, Except Diagnostic {value // Elaborates v owner Γ cursor source value}) e with
      | .name token => do
        let result ← lift (Names.name v owner Γ cursor token.text)
        return ⟨result.value, .name result.derivation⟩
      | .integer _ i => .ok ⟨.integer (.literal (Int.ofNat i)), .integer⟩
      | .parens a _ => do
        let a ← next Γ cursor a
        return ⟨a.val, .parens a.property⟩
      | .unary op a _ => do
        if hop : op.text = "sum" ∨ op.text = "product" then
          let some operands := operandsAt (fuel + 1) a
            | throw (failure doc e "behavioral.expression-budget")
          let terms ← Traversal.list (next Γ cursor) operands.val
          let result ← lift (aggregateCertified v (if op.text == "sum" then .sum else .product) terms.val)
          return ⟨result.val, .aggregate hop operands.property (elaboratesList terms.property) result.property⟩
        else
          let a ← next Γ cursor a
          let result ← lift (MonadAttach.attach (unary v op.text a.val))
          return ⟨result.val, .unary a.property (unary_sound v result.property)⟩
      | .binary op a b span => do
        if hop : op.text = "." then
          match emptyNavigationAt (fuel + 1) (.binary op a b span) with
          | none => throw (failure doc e "behavioral.expression-budget")
          | some (.isTrue path) =>
            let root ← lift (Names.name v owner Γ cursor "noclafer")
            return ⟨root.value, .emptyNavigation path root.derivation⟩
          | some (.isFalse ordinary) =>
            let left ← next Γ cursor a
            let right ← next Γ (some left.val) b
            return ⟨right.val, .dot hop ordinary left.property right.property⟩
        else
          let a ← next Γ cursor a
          let b ← next Γ cursor b
          let result ← lift (MonadAttach.attach (binary v op.text a.val b.val))
          return ⟨result.val, .binary a.property b.property (binary_sound result.property)⟩
      | .quantified op disjoint names domain body _ => do
        let domain ← next Γ cursor domain
        let heads ← lift (MonadAttach.attach (Values.heads domain.val))
        let plan ← Binders.prepare Γ op names heads.val.1
        let q ← Binders.quantifier op
        let body ← next plan.bodyContext none body
        let boolean ← lift (booleanCertified body.val)
        return ⟨.formula (Expression.binders q.val names.length disjoint.isSome heads.val.2 boolean.val),
          .quantified plan.legal q.property domain.property (heads_sound heads.property) body.property boolean.property⟩
      | .letSet _ binder value body _ => do
        if hb : Resolution.reserved binder.text = true then
          throw (Resolution.errorAt binder "behavioral.reserved-binder" "Reserved binder name.")
        else
          let value ← next Γ cursor (.name value)
          let heads ← lift (MonadAttach.attach (Values.heads value.val))
          let body ← next (push Γ binder heads.val.1) none body
          let boolean ← lift (booleanCertified body.val)
          return ⟨.formula (.letSet heads.val.2 boolean.val), .letSet (Bool.eq_false_iff.mpr hb)
            value.property (heads_sound heads.property) body.property boolean.property⟩
      | .conditional _ condition yes no _ => do
        let condition ← next Γ cursor condition
        let boolean ← lift (booleanCertified condition.val)
        let yes ← next Γ cursor yes
        let no ← next Γ cursor no
        let result ← lift (MonadAttach.attach (Values.conditional v boolean.val yes.val no.val))
        return ⟨result.val, .conditional condition.property boolean.property yes.property no.property
          (conditional_sound result.property)⟩
      | .transition arrow a guard b _ => do
        let a ← next Γ cursor a
        let guard ← Traversal.option (next Γ cursor) guard
        let b ← next Γ cursor b
        let result ← lift (chainCertified arrow a.val guard.val b.val)
        return ⟨result.val, .transition a.property (elaboratesOption guard.property) b.property result.property⟩
      | .pattern kind first second scope opener closer _ => do
        let first ← next Γ cursor first
        let second ← Traversal.option (next Γ cursor) second
        let opener ← Traversal.option (next Γ cursor) opener
        let closer ← Traversal.option (next Γ cursor) closer
        let result ← lift (patternCertified kind first.val second.val scope opener.val closer.val)
        return ⟨result.val, .pattern first.property (elaboratesOption second.property) (elaboratesOption opener.property)
          (elaboratesOption closer.property) result.property⟩)

-- [impl->req~compiler-behavioral-elaboration~1]
def synthAt (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (budget : Nat)
    {n : Nat} (Γ : Context k n) (cursor : Option (Value k n)) (e : Expr) : Except Diagnostic (Value k n) :=
  (certifiedAt doc v owner budget Γ cursor e).map Subtype.val

def elaborateCertified (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (budget : Nat) (e : Expr) : Except Diagnostic {formula // FormulaElaborates v owner e formula} := do
  let value ← certifiedAt doc v owner budget #v[] none e
  let boolean ← (booleanCertified value.val).mapError (failure doc e)
  return ⟨boolean.val, ⟨value.val, value.property, boolean.property⟩⟩

-- [impl->req~compiler-behavioral-elaboration~1]
def elaborate (doc : Document) (v : IR.BehavioralStructural.Validated k) (owner : Fin k)
    (budget : Nat) (e : Expr) : Except Diagnostic (Expression.Formula k 0) :=
  (elaborateCertified doc v owner budget e).map Subtype.val

-- [proof->req~compiler-behavioral-elaboration~1]
theorem elaborate_sound (h : elaborate doc v owner budget e = .ok formula) : FormulaElaborates v owner e formula := by
  obtain ⟨result, _, rfl⟩ := Traversal.map_success h
  exact result.property

end ClaferCompiler.Frontend.Behavioral.Expressions
