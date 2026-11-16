module

public import ClaferCompiler.Driver.BehavioralSource

@[expose] public section
namespace ClaferCompiler.Driver.ExplicitSyntax
open Lean Decode IR.Behavioral
open Behavioral (arg tag arity declarationIndex)

/-- Full resolved syntax is decoded independently of source elaboration. Every
ID and lexical slot is checked; traversal exhaustion is an error. -/
structure Pass (k : Nat) where
  set : {n : Nat} → Node → Except Diagnostic (SetExpr k n)
  collection : {n : Nat} → Node → Except Diagnostic (Expression.Collection k n)
  integer : {n : Nat} → Node → Except Diagnostic (Expression.Integer k n)
  collections : {n : Nat} → Node → Except Diagnostic (Expression.Collections k n)
  predicate : {n : Nat} → Node → Except Diagnostic (Expression.Predicate k n)
  atom : {n : Nat} → Node → Except Diagnostic (Expression.Atom k n)
  formula : {n : Nat} → Node → Except Diagnostic (Expression.Formula k n)

def choose (n : Node) (rows : List (String × α)) : Except Diagnostic α := do
  let key ← string n
  match rows.find? (fun row => row.1 == key) with
  | some row => return row.2
  | none => throw (bad n "unknown constructor")

-- [impl->req~compiler-rich-core-explicit~1]
def step (m : IR.Structural.Core k) (fuel : Nat) (next : Pass k) : Pass k where
  set := fun n => (Behavioral.setAt m fuel n).map (·.value)
  collection := fun {_depth} n => do
    match ← tag n with
    | "set" =>
      arity n 2
      let a1 ← next.set (← arg n 1)
      return .set a1
    | "literal" =>
      arity n 2
      let a1 ← Source.integer (← arg n 1)
      return .literal a1
    | "integer" =>
      arity n 2
      let a1 ← next.integer (← arg n 1)
      return .integer a1
    | "extreme" =>
      arity n 3
      let a1 ← choose (← arg n 1) [("minimum", .minimum), ("maximum", .maximum)]
      let a2 ← next.collection (← arg n 2)
      return .extreme a1 a2
    | "union" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .union a1 a2
    | "inter" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .inter a1 a2
    | "diff" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .diff a1 a2
    | "step" =>
      arity n 3
      let a1 ← Behavioral.step m (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .step a1 a2
    | "ofType" =>
      arity n 3
      let a1 ← declarationIndex m (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .ofType a1 a2
    | "ite" =>
      arity n 4
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      let a3 ← next.collection (← arg n 3)
      return .ite a1 a2 a3
    | _ => throw (bad n "unknown collection constructor")
  integer := fun {depth} n => do
    match ← tag n with
    | "literal" =>
      arity n 2
      let a1 ← Source.integer (← arg n 1)
      return .literal a1
    | "coerce" =>
      arity n 2
      let a1 ← next.collection (← arg n 1)
      return .coerce a1
    | "extract" =>
      arity n 2
      let a1 ← next.collection (← arg n 1)
      return .extract a1
    | "cardinality" =>
      arity n 2
      let a1 ← next.collection (← arg n 1)
      return .cardinality a1
    | "binary" =>
      arity n 4
      let a1 ← choose (← arg n 1) [("add", .add), ("subtract", .subtract), ("multiply", .multiply), ("divide", .divide), ("remainder", .remainder)]
      let a2 ← next.integer (← arg n 2)
      let a3 ← next.integer (← arg n 3)
      return .binary a1 a2 a3
    | "negate" =>
      arity n 2
      let a1 ← next.integer (← arg n 1)
      return .negate a1
    | "fold" =>
      arity n 4
      let a1 ← choose (← arg n 1) [("sum", .sum), ("product", .product)]
      let a2 ← next.collections (← arg n 2)
      let a3 ← next.integer (n := depth + 1) (← arg n 3)
      return .fold a1 a2 a3
    | "ite" =>
      arity n 4
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.integer (← arg n 2)
      let a3 ← next.integer (← arg n 3)
      return .ite a1 a2 a3
    | _ => throw (bad n "unknown integer constructor")
  collections := fun {_depth} n => do
    match ← tag n with
    | "nil" =>
      arity n 1
      return .nil
    | "cons" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collections (← arg n 2)
      return .cons a1 a2
    | _ => throw (bad n "unknown collections constructor")
  predicate := fun {_depth} n => do
    match ← tag n with
    | "inhabited" =>
      arity n 2
      let a1 ← next.collection (← arg n 1)
      return .inhabited a1
    | "equal" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .equal a1 a2
    | "subset" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.collection (← arg n 2)
      return .subset a1 a2
    | "integerEqual" =>
      arity n 3
      let a1 ← next.integer (← arg n 1)
      let a2 ← next.integer (← arg n 2)
      return .integerEqual a1 a2
    | "less" =>
      arity n 3
      let a1 ← next.integer (← arg n 1)
      let a2 ← next.integer (← arg n 2)
      return .less a1 a2
    | _ => throw (bad n "unknown predicate constructor")
  atom := fun {depth} n => do
    match ← tag n with
    | "primitive" =>
      arity n 2
      let a1 ← next.predicate (← arg n 1)
      return .primitive a1
    | "equalClosed" =>
      arity n 3
      let a1 ← next.set (← arg n 1)
      let a2 ← next.collection (n := 0) (← arg n 2)
      return .equalClosed a1 a2
    | "inContext" =>
      arity n 3
      let a1 ← next.set (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .inContext a1 a2
    | "count" =>
      arity n 6
      let a1 ← choose (← arg n 1) [("one", .one), ("lone", .lone)]
      let arityValue ← natural (← arg n 2)
      let a3 ← boolean (← arg n 3)
      let a4 ← next.collection (← arg n 4)
      let a5 ← next.formula (n := depth + arityValue) (← arg n 5)
      return .count a1 arityValue a3 a4 a5
    | _ => throw (bad n "unknown atom constructor")
  formula := fun {depth} n => do
    match ← tag n with
    | "truth" =>
      arity n 1
      return .truth
    | "atom" =>
      arity n 2
      let a1 ← next.atom (← arg n 1)
      return .atom a1
    | "not" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .not a1
    | "next" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .next a1
    | "eventually" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .eventually a1
    | "always" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .always a1
    | "previous" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .previous a1
    | "weakPrevious" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .weakPrevious a1
    | "once" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .once a1
    | "historically" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .historically a1
    | "initially" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .initially a1
    | "finally" =>
      arity n 2
      let a1 ← next.formula (← arg n 1)
      return .finally a1
    | "and" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .and a1 a2
    | "or" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .or a1 a2
    | "implies" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .implies a1 a2
    | "iff" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .iff a1 a2
    | "xor" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .xor a1 a2
    | "strongUntil" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .strongUntil a1 a2
    | "weakUntil" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .weakUntil a1 a2
    | "since" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .since a1 a2
    | "triggered" =>
      arity n 3
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      return .triggered a1 a2
    | "ite" =>
      arity n 4
      let a1 ← next.formula (← arg n 1)
      let a2 ← next.formula (← arg n 2)
      let a3 ← next.formula (← arg n 3)
      return .ite a1 a2 a3
    | "quant" =>
      arity n 4
      let a1 ← choose (← arg n 1) [("all", .all), ("some", .some), ("no", .no), ("one", .one), ("lone", .lone)]
      let a2 ← next.collection (← arg n 2)
      let a3 ← next.formula (n := depth + 1) (← arg n 3)
      return .quant a1 a2 a3
    | "letSet" =>
      arity n 3
      let a1 ← next.collection (← arg n 1)
      let a2 ← next.formula (n := depth + 1) (← arg n 2)
      return .letSet a1 a2
    | _ => throw (bad n "unknown formula constructor")

def exhausted (n : Node) : Diagnostic := bad n "explicit syntax traversal exhausted"

def decode (m : IR.Structural.Core k) : Nat → Pass k :=
  Nat.rec ⟨fun n => .error (exhausted n), fun n => .error (exhausted n),
    fun n => .error (exhausted n), fun n => .error (exhausted n),
    fun n => .error (exhausted n), fun n => .error (exhausted n),
    fun n => .error (exhausted n)⟩ (fun fuel next => step m (fuel + 1) next)

end ClaferCompiler.Driver.ExplicitSyntax
