module

public import ClaferCompiler.Driver.Diagnostic
public import ClaferCompiler.IR.Behavioral.Expression

@[expose] public section
namespace ClaferCompiler.Driver.BehavioralSyntax
open Lean IR.Behavioral

/-- A diagnostic/export representation, not a second admitted input schema. -/
structure Encoded where
  json : Json
  depth : Nat

def node (tag : String) (arguments : List Json := []) (children : List Encoded := []) : Encoded :=
  ⟨toJson (toJson tag :: arguments ++ children.map (·.json)),
   1 + (children.map (·.depth)).foldl max 0⟩

def navigation (m : IR.Structural.Core k) : Step k → Json
  | .parent => toJson ([toJson "parent"] : List Json)
  | .child d => toJson [toJson "child", toJson (m.get d).id]
  | .deref d => toJson [toJson "deref", toJson (m.get d).id]

def quantifier : Quantifier → String
  | .all => "all" | .some => "some" | .no => "no" | .one => "one" | .lone => "lone"

def binary : IR.BehavioralArithmetic.Binary → String
  | .add => "add" | .subtract => "subtract" | .multiply => "multiply"
  | .divide => "divide" | .remainder => "remainder"

def foldName : IR.BehavioralArithmetic.Fold → String
  | .sum => "sum" | .product => "product"

structure Pass (k : Nat) where
  set : {n : Nat} → SetExpr k n → Except Diagnostic Encoded
  collection : {n : Nat} → Expression.Collection k n → Except Diagnostic Encoded
  integer : {n : Nat} → Expression.Integer k n → Except Diagnostic Encoded
  collections : {n : Nat} → Expression.Collections k n → Except Diagnostic Encoded
  predicate : {n : Nat} → Expression.Predicate k n → Except Diagnostic Encoded
  atom : {n : Nat} → Expression.Atom k n → Except Diagnostic Encoded
  formula : {n : Nat} → Expression.Formula k n → Except Diagnostic Encoded

-- [impl->req~compiler-behavioral-integration~1]
/-- Reuse the complete seven-family traversal shape of the admitted range pass. -/
def step (m : IR.Structural.Core k) (next : Pass k) : Pass k where
  set := fun a => do
    match a with
    | .empty => return node "empty" [] []
    | .this => return node "this" [] []
    | .root => return node "root" [] []
    | .var i => return node "var" [toJson i.val] []
    | .extent d => return node "extent" [toJson (m.get d).id] []
    | .union a b => return node "union" [] [← next.set a, ← next.set b]
    | .inter a b => return node "inter" [] [← next.set a, ← next.set b]
    | .diff a b => return node "diff" [] [← next.set a, ← next.set b]
    | .step st a => return node "step" [navigation m st] [← next.set a]
    | .thisStep st => return node "thisStep" [navigation m st] []
  collection := fun a => do
    match a with
    | .set a => return node "set" [] [← next.set a]
    | .literal z => return node "literal" [toJson z] []
    | .integer a => return node "integer" [] [← next.integer a]
    | .extreme op a => return node "extreme" [toJson (match op with | .minimum => "minimum" | .maximum => "maximum")] [← next.collection a]
    | .union a b => return node "union" [] [← next.collection a, ← next.collection b]
    | .inter a b => return node "inter" [] [← next.collection a, ← next.collection b]
    | .diff a b => return node "diff" [] [← next.collection a, ← next.collection b]
    | .step st a => return node "step" [navigation m st] [← next.collection a]
    | .ofType d a => return node "ofType" [toJson (m.get d).id] [← next.collection a]
    | .ite c a b => return node "ite" [] [← next.formula c, ← next.collection a, ← next.collection b]
  integer := fun a => do
    match a with
    | .literal z => return node "literal" [toJson z] []
    | .coerce a => return node "coerce" [] [← next.collection a]
    | .extract a => return node "extract" [] [← next.collection a]
    | .cardinality a => return node "cardinality" [] [← next.collection a]
    | .binary op a b => return node "binary" [toJson (binary op)] [← next.integer a, ← next.integer b]
    | .negate a => return node "negate" [] [← next.integer a]
    | .fold op ds a => return node "fold" [toJson (foldName op)] [← next.collections ds, ← next.integer a]
    | .ite c a b => return node "ite" [] [← next.formula c, ← next.integer a, ← next.integer b]
  collections := fun a => do
    match a with
    | .nil => return node "nil" [] []
    | .cons a bs => return node "cons" [] [← next.collection a, ← next.collections bs]
  predicate := fun a => do
    match a with
    | .inhabited a => return node "inhabited" [] [← next.collection a]
    | .equal a b => return node "equal" [] [← next.collection a, ← next.collection b]
    | .subset a b => return node "subset" [] [← next.collection a, ← next.collection b]
    | .integerEqual a b => return node "integerEqual" [] [← next.integer a, ← next.integer b]
    | .less a b => return node "less" [] [← next.integer a, ← next.integer b]
  atom := fun a => do
    match a with
    | .primitive a => return node "primitive" [] [← next.predicate a]
    | .equalClosed left right => return node "equalClosed" [] [← next.set left, ← next.collection right]
    | .inContext domain body => return node "inContext" [] [← next.set domain, ← next.formula body]
    | .count q arity disjoint domain body => return node "count" [toJson (match q with | .one => "one" | .lone => "lone"), toJson arity, toJson disjoint] [← next.collection domain, ← next.formula body]
  formula := fun a => do
    match a with
    | .truth => return node "truth" [] []
    | .atom a => return node "atom" [] [← next.atom a]
    | .not a => return node "not" [] [← next.formula a]
    | .next a => return node "next" [] [← next.formula a]
    | .eventually a => return node "eventually" [] [← next.formula a]
    | .always a => return node "always" [] [← next.formula a]
    | .initially a => return node "initially" [] [← next.formula a]
    | .finally a => return node "finally" [] [← next.formula a]
    | .and a b => return node "and" [] [← next.formula a, ← next.formula b]
    | .or a b => return node "or" [] [← next.formula a, ← next.formula b]
    | .implies a b => return node "implies" [] [← next.formula a, ← next.formula b]
    | .iff a b => return node "iff" [] [← next.formula a, ← next.formula b]
    | .xor a b => return node "xor" [] [← next.formula a, ← next.formula b]
    | .strongUntil a b => return node "strongUntil" [] [← next.formula a, ← next.formula b]
    | .weakUntil a b => return node "weakUntil" [] [← next.formula a, ← next.formula b]
    | .ite c a b => return node "ite" [] [← next.formula c, ← next.formula a, ← next.formula b]
    | .quant q d a => return node "quant" [toJson (quantifier q)] [← next.collection d, ← next.formula a]
    | .letSet d a => return node "letSet" [] [← next.collection d, ← next.formula a]

def exhausted : Diagnostic := {
  code := "behavioral.syntax-budget", phase := "encoding", category := .unsupported
  message := "source expansion exceeds the syntax traversal allocation" }

def encode (m : IR.Structural.Core k) : Nat → Pass k :=
  Nat.rec ⟨fun _ => .error exhausted, fun _ => .error exhausted,
    fun _ => .error exhausted, fun _ => .error exhausted, fun _ => .error exhausted,
    fun _ => .error exhausted, fun _ => .error exhausted⟩ (fun _ previous => step m previous)

end ClaferCompiler.Driver.BehavioralSyntax
