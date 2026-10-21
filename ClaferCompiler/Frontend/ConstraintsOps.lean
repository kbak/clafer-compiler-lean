module

public import ClaferCompiler.Frontend.ConstraintsCoercions

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr
variable {n m : Nat} {c : IR.Structural.Core n} {s : Support n m}
  {Γ : List (Local n)} {cursor : Cursor n m} {e l r domain body : Frontend.Expr}

def unary (op : Token) (span : SourceSpan) (input : Synth c s Γ cursor e) :
    Except String (Synth c s Γ cursor (.unary op e span)) := do
  if ho : op.text = "!" then
    let a ← expect input .boolean
    return ⟨.boolean, .located span (.not a.term), .unary (t := .boolean) (a := a.term.raw)
      (by simpa [ho] using a.derivation) (by rw [ho]; exact .not)⟩
  if ho : op.text = "-" then
    let a ← expect input .integer
    return ⟨.integer, .located span (.arithmetic .subtract (.integer 0) a.term),
      .unary (t := .integer) (a := a.term.raw) (by simpa [ho] using a.derivation) (by rw [ho]; exact .negative)⟩
  match ht : input.type with
  | .collection k =>
    let a : RawAt c s Γ cursor e (.collection k) := ⟨input.term, by rw [← ht]; exact input.derivation⟩
    if ho : op.text = "#" then
      return ⟨.integer, .located span (.cardinality k a.term), .unary (t := .collection k) (a := a.term.raw) (by simpa [ho] using a.derivation) (by rw [ho]; exact .count)⟩
    if ho : op.text = "some" then
      return ⟨.boolean, .located span (.less (.integer 0) (.cardinality k a.term)),
        .unary (t := .collection k) (a := a.term.raw) (by simpa [ho] using a.derivation) (by rw [ho]; exact .some)⟩
    if ho : op.text = "no" ∨ op.text = "not" then
      return ⟨.boolean, .located span (.equal .integer (.cardinality k a.term) (.integer 0)),
        .unary (t := .collection k) (a := a.term.raw) (by rcases ho with ho | ho <;> simpa [ho] using a.derivation) (.no ho)⟩
    if ho : op.text = "one" then
      return ⟨.boolean, .located span (.equal .integer (.cardinality k a.term) (.integer 1)),
        .unary (t := .collection k) (a := a.term.raw) (by simpa [ho] using a.derivation) (by rw [ho]; exact .one)⟩
    if ho : op.text = "lone" then
      return ⟨.boolean, .located span (.less (.cardinality k a.term) (.integer 2)),
        .unary (t := .collection k) (a := a.term.raw) (by simpa [ho] using a.derivation) (by rw [ho]; exact .lone)⟩
    throw "constraint.unsupported-operator"
  | _ => throw "constraint.expected-collection"

abbrev orTerm (a b : Term n m) := Term.not (.and (.not a) (.not b))
abbrev impliesTerm (a b : Term n m) := Term.not (.and a (.not b))

def binary (op : Token) (span : SourceSpan) (left : Synth c s Γ cursor l)
    (right : Synth c s Γ cursor r) : Except String (Synth c s Γ cursor (.binary op l r span)) := do
  if ["&&", "||", "xor", "=>", "<=>"].contains op.text then
    let a ← expect left .boolean
    let b ← expect right .boolean
    if ho : op.text = "&&" then
      return ⟨.boolean, .located span (.and a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .and)⟩
    if ho : op.text = "||" then
      return ⟨.boolean, .located span (orTerm a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .or)⟩
    if ho : op.text = "xor" then
      return ⟨.boolean, .located span (.and (orTerm a.term b.term) (.not (.and a.term b.term))),
        .binary a.derivation b.derivation (by rw [ho]; exact .xor)⟩
    if ho : op.text = "=>" then
      return ⟨.boolean, .located span (impliesTerm a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .implies)⟩
    if ho : op.text = "<=>" then
      return ⟨.boolean, .located span (.and (impliesTerm a.term b.term) (impliesTerm b.term a.term)),
        .binary a.derivation b.derivation (by rw [ho]; exact .iff)⟩
  if ["<", ">", "<=", ">=", "+", "-"].contains op.text then
    let a ← expect left .integer
    let b ← expect right .integer
    if ho : op.text = "<" then
      return ⟨.boolean, .located span (.less a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .less)⟩
    if ho : op.text = ">" then
      return ⟨.boolean, .located span (.less b.term a.term), .binary a.derivation b.derivation (by rw [ho]; exact .greater)⟩
    if ho : op.text = "<=" then
      return ⟨.boolean, .located span (.not (.less b.term a.term)), .binary a.derivation b.derivation (by rw [ho]; exact .le)⟩
    if ho : op.text = ">=" then
      return ⟨.boolean, .located span (.not (.less a.term b.term)), .binary a.derivation b.derivation (by rw [ho]; exact .ge)⟩
    if ho : op.text = "+" then
      return ⟨.integer, .located span (.arithmetic .add a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .add)⟩
    if ho : op.text = "-" then
      return ⟨.integer, .located span (.arithmetic .subtract a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .subtract)⟩
  let pair ← align left right (["=", "!="].contains op.text)
  let a := pair.left
  let b := pair.right
  if ho : op.text = "=" then
    if he : ValueType s pair.type then
      return ⟨.boolean, .located span (.equal pair.type a.term b.term), .binary a.derivation b.derivation (by rw [ho]; exact .equal he)⟩
    else throw "constraint.value-type"
  if ho : op.text = "!=" then
    if he : ValueType s pair.type then
      return ⟨.boolean, .located span (.not (.equal pair.type a.term b.term)), .binary a.derivation b.derivation (by rw [ho]; exact .unequal he)⟩
    else throw "constraint.value-type"
  match ht : pair.type with
  | .collection k =>
    have ha : Elaborates c s Γ cursor true l (.collection k) a.term.raw := by rw [← ht]; exact a.derivation
    have hb : Elaborates c s Γ cursor true r (.collection k) b.term.raw := by rw [← ht]; exact b.derivation
    if ho : op.text = "++" then
      return ⟨.collection k, .located span (.setOp .union k a.term b.term), .binary ha hb (by rw [ho]; exact .union)⟩
    if ho : op.text = "--" then
      return ⟨.collection k, .located span (.setOp .difference k a.term b.term), .binary ha hb (by rw [ho]; exact .difference)⟩
    if ho : op.text = "**" then
      return ⟨.collection k, .located span (.setOp .intersection k a.term b.term), .binary ha hb (by rw [ho]; exact .intersection)⟩
    if ho : op.text = "in" then
      return ⟨.boolean, .located span (.subset k a.term b.term), .binary ha hb (by rw [ho]; exact .subset)⟩
    if ho : op.text = "not in" then
      return ⟨.boolean, .located span (.not (.subset k a.term b.term)), .binary ha hb (by rw [ho]; exact .notSubset)⟩
    throw "constraint.unsupported-operator"
  | _ => throw "constraint.expected-collection"

def quantify (op binder : Token) (span : SourceSpan) (b : Local n)
    (hb : b.name = binder.text) (hf : ∀ old ∈ Γ, old.id ≠ b.id)
    (d : RawAt c s Γ cursor domain (.collection (.objects b.element)))
    (a : At c s (b :: Γ) none body .boolean) :
    Except String (Synth c s Γ cursor (.quantified op binder domain body span)) := do
  if ho : op.text = "all" then
    return ⟨.boolean, .located span (.all b d.term a.term),
      .quantified hb hf d.derivation a.derivation (by rw [ho]; exact .all)⟩
  if ho : op.text = "some" then
    return ⟨.boolean, .located span (.not (.all b d.term (.not a.term))),
      .quantified hb hf d.derivation a.derivation (by rw [ho]; exact .some)⟩
  if ho : op.text = "no" ∨ op.text = "not" then
    return ⟨.boolean, .located span (.all b d.term (.not a.term)), .quantified hb hf d.derivation a.derivation (.no ho)⟩
  throw "constraint.unsupported-quantifier"

end ClaferCompiler.Frontend.Constraints
