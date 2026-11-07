module

public import ClaferCompiler.Backend.Alloy.Behavioral.Expressions

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Partial

/-- Source definedness is a reified formula, separate from the target evaluator's
own arithmetic definedness. Truth keeps the raw one/lone barrier and both signs. -/
structure Translation where
  truth : Behavioral.Translation
  defined : TFormula

/-- A conservative constant-truth analysis over the existing target fold. A
false result says only that this analysis did not prove the formula true. -/
def trueAlgebra : Temporal.FormulaAlgebra Bool where
  truth := true
  falsity := false
  equal := fun _ _ => false
  subset := fun _ _ => false
  mult := fun _ _ => false
  compare := fun _ _ _ => false
  unary := fun op p => match op with
    | .neg | .before => false
    | _ => p
  binary := fun op p q => match op with
    | .conj => p && q
    | .disj => p || q
    | _ => q
  all := fun _ p => p
  exists_ := fun _ _ => false

def knownTrue (a : TFormula) : Bool := a.fold trueAlgebra false

/-- Total original domains need no repeated lifetime formula. Admission still
checks every source operand and arithmetic range before this simplification. -/
def totalAlways (parent domain : TFormula) : TFormula :=
  if knownTrue domain then .truth else Behavioral.always parent domain

-- [impl->req~compiler-behavioral-partial-lowering~1]
def atom (defined value : TFormula) : Translation := ⟨.atomic value, defined⟩
def truth : Translation := atom .truth .truth

def negation (a : Translation) : Translation := ⟨Behavioral.negation a.truth, a.defined⟩

def conjunction (a b : Translation) : Translation :=
  ⟨Behavioral.conjunction a.truth b.truth, .binary .conj a.defined b.defined⟩

def disjunction (a b : Translation) : Translation :=
  ⟨Behavioral.disjunction a.truth b.truth, .binary .conj a.defined b.defined⟩

def implication (a b : Translation) : Translation := disjunction (negation a) b
def equivalence (a b : Translation) : Translation :=
  ⟨Behavioral.equivalence a.truth b.truth, .binary .conj a.defined b.defined⟩
def exclusiveOr (a b : Translation) : Translation := negation (equivalence a b)

def conditional (c a b : Translation) : Translation :=
  ⟨(Behavioral.conjunction (Behavioral.implication c.truth a.truth)
      (Behavioral.implication (Behavioral.negation c.truth) b.truth)),
    .binary .conj c.defined (.binary .conj a.defined b.defined)⟩

def next (parent : TFormula) (a : Translation) : Translation :=
  ⟨a.truth.map (Behavioral.next parent), Behavioral.next parent a.defined⟩

def eventually (parent : TFormula) (a : Translation) : Translation :=
  ⟨⟨Behavioral.eventually parent a.truth.raw, Behavioral.eventually parent a.truth.positive,
      Behavioral.always parent a.truth.negative⟩,
    totalAlways parent a.defined⟩

def always (parent : TFormula) (a : Translation) : Translation :=
  ⟨⟨Behavioral.always parent a.truth.raw, Behavioral.always parent a.truth.positive,
      Behavioral.eventually parent a.truth.negative⟩,
    totalAlways parent a.defined⟩

def strongUntil (parent : TFormula) (a b : Translation) : Translation :=
  ⟨⟨Behavioral.strongUntil parent a.truth.raw b.truth.raw,
      Behavioral.strongUntil parent a.truth.positive b.truth.positive,
      Behavioral.weakUntil parent b.truth.negative
        (.binary .conj a.truth.negative b.truth.negative)⟩,
    totalAlways parent (.binary .conj a.defined b.defined)⟩

def weakUntil (parent : TFormula) (a b : Translation) : Translation :=
  ⟨⟨Behavioral.weakUntil parent a.truth.raw b.truth.raw,
      Behavioral.weakUntil parent a.truth.positive b.truth.positive,
      Behavioral.strongUntil parent b.truth.negative
        (.binary .conj a.truth.negative b.truth.negative)⟩,
    totalAlways parent (.binary .conj a.defined b.defined)⟩

def initially (present : TFormula) (a : Translation) : Translation :=
  ⟨a.truth.map (Behavioral.initially present), Behavioral.initially present a.defined⟩

def «finally» (present : TFormula) (a : Translation) : Translation :=
  ⟨a.truth.map (Behavioral.atEnd present), Behavioral.atEnd present a.defined⟩

def satisfaction (a : Translation) (positive : Bool) : TFormula :=
  .binary .conj a.defined (if positive then a.truth.positive else a.truth.negative)

/-- Called after attachment quantification: negate the complete property,
including its original strict domain. -/
def counterexample (property : TFormula) : TFormula := .unary .neg property

/-- Freeze domain membership once. All source signs share this capture, and
the original body's definedness is checked under the same captured collection. -/
def capture (aliases : List TRel) (domain : TRel) (domainDefined : TFormula)
    (body : TRel → Translation) : Translation :=
  ⟨Behavioral.freeze aliases domain (fun value => (body value).truth),
    .binary .conj domainDefined
      (Behavioral.freeze aliases domain (fun value => .atomic (body value).defined)).raw⟩

/-- `one` is compiled under one fresh singleton binder; `two` under the
uniqueness witness and that binder. The raw body supplies counting truth, while
every domain member must satisfy the original body's definedness. -/
def quantify (q : IR.Behavioral.Quantifier) (domain : TRel) (domainDefined : TFormula)
    (one two : Translation) : Translation :=
  let value : Behavioral.Translation := match q with
    | .all => ⟨.all domain one.truth.raw, .all domain one.truth.positive,
        .exists_ domain one.truth.negative⟩
    | .some => ⟨.exists_ domain one.truth.raw, .exists_ domain one.truth.positive,
        .all domain one.truth.negative⟩
    | .no => ⟨.all domain (.unary .neg one.truth.raw), .all domain one.truth.negative,
        .exists_ domain one.truth.positive⟩
    | .one | .lone =>
      let unique := Temporal.Formula.all (shift 1 domain)
        (.binary .implies two.truth.raw (.equal (.var 0) (.var 1)))
      .atomic (if q == .one then
        .exists_ domain (.binary .conj one.truth.raw unique)
        else .all domain (.binary .implies one.truth.raw unique))
  ⟨value, .binary .conj domainDefined (.all domain one.defined)⟩

end ClaferCompiler.Backend.Alloy.Behavioral.Partial
