module

public import tests.BehavioralStructuralNative
public import tests.AlloyTemporal
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Expressions

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullExpressions
open IR.Behavioral
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Temporal (Formula Integer Rel Module)

abbrev Source := Expression.Formula 7 1

def inputs : Expression.Ranges.Inputs 7 where
  width := 5
  context := ⟨1, ⟨0, 0⟩⟩
  root := ⟨1, ⟨0, 0⟩⟩
  extents := Vector.replicate 7 ⟨2, ⟨-2, 2⟩⟩
  steps := fun _ => ⟨2, ⟨-2, 2⟩⟩

def context : Expressions.Context 1 where
  lexical := ⟨.sig 0, fun _ => .sig 0,
    [.sig 0, .integer (-2), .integer (-1), .integer 0, .integer 1, .integer 2]⟩
  estimates := #v[⟨1, ⟨0, 0⟩⟩]

def number (i : Int) : Expression.Collection 7 n := .literal i

def equal (a b : Expression.Collection 7 n) : Expression.Formula 7 n :=
  .atom (.primitive (.equal a b))
def integerEqual (a b : Expression.Integer 7 n) : Expression.Formula 7 n :=
  .atom (.primitive (.integerEqual a b))

def pair : Expression.Collection 7 n := .union (number 1) (number 2)
def duplicate : Expression.Collection 7 n := .union (number 2) (number 2)
def emptyExtract : Expression.Integer 7 n := .extract (.set .empty)
def sumRepeated : Expression.Integer 7 n :=
  .fold .sum (.cons (number 2) (.cons (number 2) .nil)) (.extract (.set (.var 0)))
def productRepeated : Expression.Integer 7 n :=
  .fold .product (.cons (number 2) (.cons (number 2) .nil)) (.extract (.set (.var 0)))

def threeTuples : Expression.Formula 7 (1 + 2) :=
  .or (equal (.set (.var 1)) (number 1)) (equal (.set (.var 0)) (number 1))

inductive Query where | property | counterexample | domain

def Query.body (q : Query) (p : Backend.Alloy.Behavioral.Partial.Translation) : Formula :=
  match q with
  | .property => Backend.Alloy.Behavioral.Partial.satisfaction p true
  | .counterexample => Backend.Alloy.Behavioral.Partial.counterexample
      (Backend.Alloy.Behavioral.Partial.satisfaction p true)
  | .domain => p.defined

structure Case where
  name : String
  expected : Bool
  source : Source
  query : Query := .property
  enough : sizeOf source < 128
  padded : Bool := false
  integerThis : Bool := false

def sample (name : String) (expected : Bool) (source : Source)
    (query : Query := .property) (enough : sizeOf source < 128 := by decide) : Case :=
  ⟨name, expected, source, query, enough, false, false⟩

-- [utest->req~compiler-behavioral-partial-lowering~1]
/-- Expectations use the source set/occurrence and strict-domain contracts.
The selected/unselected and ordered-tuple mutations distinguish plausible
implementations that preserve ordinary Boolean examples but lose those contracts. -/
def sourceCases : List Case := [
  sample "full-expr-coerce-empty-zero" true (integerEqual (.coerce (.set .empty)) (.literal 0)),
  sample "full-expr-coerce-deduplicates" true (integerEqual (.coerce duplicate) (.literal 2)),
  sample "full-expr-coerce-duplicate-mutation" false (integerEqual (.coerce duplicate) (.literal 4)),
  sample "full-expr-sum-occurrences" true (integerEqual sumRepeated (.literal 4)),
  sample "full-expr-sum-union-mutation" false (integerEqual sumRepeated (.literal 2)),
  sample "full-expr-product-occurrences" true (integerEqual productRepeated (.literal 4)),
  sample "full-expr-empty-sum" true (integerEqual (.fold .sum .nil (.literal 2)) (.literal 0)),
  sample "full-expr-empty-product" true (integerEqual (.fold .product .nil (.literal 2)) (.literal 1)),
  sample "full-expr-extract-empty" false (integerEqual emptyExtract (.literal 0)) .domain,
  sample "full-expr-extract-many" false (integerEqual (.extract pair) (.literal 1)) .domain,
  sample "full-expr-extract-object" false (integerEqual (.extract (.set (.var 0))) (.literal 0)) .domain,
  sample "full-expr-coerce-object" false (integerEqual (.coerce (.set (.var 0))) (.literal 0)) .domain,
  sample "full-expr-extract-empty-counterexample" true (integerEqual emptyExtract (.literal 0)) .counterexample,
  sample "full-expr-negated-undefined" false (.not (integerEqual emptyExtract (.literal 0))),
  sample "full-expr-conditional-strict" false
    (integerEqual (.ite .truth (.literal 1) emptyExtract) (.literal 1)) .domain,
  sample "full-expr-conditional-undefined-counterexample" true
    (integerEqual (.ite .truth (.literal 1) emptyExtract) (.literal 1)) .counterexample,
  sample "full-expr-conditional-selected" true
    (integerEqual (.ite .truth (.literal 1) (.literal 2)) (.literal 1)),
  sample "full-expr-collection-selected" true
    (equal (.ite .truth (number 1) (number 2)) (number 1)),
  sample "full-expr-minimum-empty" true
    (equal (.extreme .minimum (.set .empty)) (.set .empty)),
  sample "full-expr-minimum" true (equal (.extreme .minimum pair) (number 1)),
  sample "full-expr-maximum" true (equal (.extreme .maximum pair) (number 2)),
  sample "full-expr-minimum-object" false
    (equal (.extreme .minimum (.set (.var 0))) (.set .empty)) .domain,
  sample "full-expr-count-deduplicates" true (integerEqual (.cardinality duplicate) (.literal 1)),
  sample "full-expr-integer-collection" true
    (equal (.integer (.binary .add (.literal 1) (.literal 1))) (number 2)),
  sample "full-expr-one-complete-tuple" false (.atom (.count .one 2 false pair threeTuples)),
  sample "full-expr-lone-complete-tuple" false (.atom (.count .lone 2 false pair threeTuples)),
  sample "full-expr-one-unique-tuple" true
    (.atom (.count .one 2 false pair (.and (equal (.set (.var 1)) (number 1))
      (equal (.set (.var 0)) (number 2))))),
  sample "full-expr-disjoint-singleton" false (.atom (.count .one 2 true (number 1) .truth)),
  sample "full-expr-disjoint-empty-lone" true (.atom (.count .lone 2 true (number 1) .truth)),
  sample "full-expr-ordered-swap-tuples" false (.atom (.count .one 2 true pair .truth)),
  sample "full-expr-zero-arity" true (.atom (.count .one 0 true (.set .empty) .truth)),
  sample "full-expr-quant-empty-domain" true
    (.quant .all (.set .empty) (integerEqual emptyExtract (.literal 0))),
  sample "full-expr-quant-strict-member" false
    (.quant .all (number 1) (.or .truth (integerEqual emptyExtract (.literal 0)))) .domain,
  sample "full-expr-frozen-selection" true
    (.letSet (.ite .truth (number 1) (number 2)) (equal (.set (.var 0)) (number 1))),
  sample "full-expr-unused-undefined-let" false (.letSet (.integer emptyExtract) .truth),
  sample "full-expr-unused-undefined-let-domain" false (.letSet (.integer emptyExtract) .truth) .domain,
  sample "full-expr-unused-undefined-let-counterexample" true
    (.letSet (.integer emptyExtract) .truth) .counterexample,
  { sample "full-expr-padded-alias-coercion" true
      (integerEqual (.coerce (number 2)) (.literal 2)) with padded := true },
  { sample "full-expr-padded-alias-one" true
      (.atom (.count .one 1 false (number 2) .truth)) with padded := true },
  { sample "full-expr-this-integer-live" true
      (equal (.set .this) (number 2)) with integerThis := true },
  { sample "full-expr-integer-initially" false
      (.initially (.not .truth)) with integerThis := true }
]

def cases : Except String (List (String × Bool × Module)) := sourceCases.mapM fun c => do
  let lexical := if c.padded then
      {context.lexical with aliases := context.lexical.aliases ++ [.integer 2, .integer 2]}
    else context.lexical
  let lexical := if c.integerThis then {lexical with this := .integer 2} else lexical
  let inputs := if c.integerThis then {inputs with context := ⟨1, ⟨2, 2⟩⟩} else inputs
  let compiled ← (Expressions.lower BehavioralStructural.validated inputs
    {context with lexical := lexical} c.source 128 c.enough).mapError (·.code)
  let base := AlloyTemporal.base (c.query.body compiled) [.mult .one (.sig 0)]
  let base := if c.integerThis then
      {base with
        schema := schema BehavioralStructural.validated
        command := {base.command with scopes := List.replicate 8 ⟨1, false⟩}}
    else base
  return (c.name, c.expected, {base with command := {base.command with bitwidth := 5}})

end ClaferCompiler.Tests.BehavioralFullExpressions
