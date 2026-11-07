module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Integers

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full
namespace Expressions
open IR.Behavioral

abbrev Result (α : Type) := Except IR.Structural.Diagnostic α

structure Context (n : Nat) where
  lexical : Behavioral.Context n
  estimates : Expression.Ranges.Context n

def Context.push (c : Context n) (r : Temporal.Rel) (estimate : Expression.Ranges.CollectionEstimate) : Context (n + 1) :=
  ⟨c.lexical.push r, Expression.Ranges.push c.estimates estimate⟩
def Context.shift (c : Context n) (amount : Nat) : Context n :=
  ⟨c.lexical.shift amount, c.estimates⟩

def Context.extend (c : Context n) (xs : Vector Temporal.Rel arity)
    (estimate : Expression.Ranges.CollectionEstimate) : Context (n + arity) :=
  ⟨⟨c.lexical.this, fun i => if h : i.val < arity then xs[i.val]
      else c.lexical.lookup ⟨i.val - arity, by omega⟩,
    c.lexical.aliases⟩, Expression.Ranges.extend c.estimates arity estimate⟩

def all (ps : List Temporal.Formula) : Temporal.Formula := ps.foldr (.binary .conj) .truth

def valueMapM (a : Value α) (f : α → Result (Value β)) : Result (Value β) := do
  let choices ← a.cases.mapM fun (g, x) => do
    let b ← f x
    return b.cases.map fun (h, y) => (Temporal.Formula.binary .conj g h, y)
  return ⟨choices.flatten⟩

def partialMapM (a : Value α) (f : α → Result Partial.Translation) : Result Partial.Translation := do
  let choices ← a.cases.mapM fun (g, x) => do
    let b ← f x
    return (g, b)
  let use := fun get => (Value.mk choices).use get
  return ⟨⟨use (fun p => p.truth.raw), use (fun p => p.truth.positive),
      use (fun p => p.truth.negative)⟩, use (fun p => p.defined)⟩

/-- Complete ordered tuples, with lexical index zero holding the last binder.
Domain aliases have already been deduplicated by identity membership guards. -/
def tuples (domain : List Temporal.Rel) (disjoint : Bool) :
    (arity : Nat) → List (Vector Temporal.Rel arity) :=
  Nat.rec [#v[]] fun arity previous => previous.flatMap fun xs =>
    (domain.filter fun x => !disjoint || !xs.toList.contains x).map fun x =>
      Vector.ofFn (Fin.cases x (fun i => xs[i]))

/-- Count the original raw truth of complete tuples. No nested one/lone
quantifier is introduced; all body domains remain separate strict obligations. -/
def countTruth (q : Grouped.Count) (ps : List Temporal.Formula) : Temporal.Formula :=
  let counts := ps.foldl (fun (zeroCount, oneCount) p =>
    (Temporal.Formula.binary .conj zeroCount (.unary .neg p),
     Temporal.Formula.binary .disj (.binary .conj oneCount (.unary .neg p))
       (.binary .conj zeroCount p))) (Temporal.Formula.truth, Temporal.Formula.falsity)
  match q with | .one => counts.2 | .lone => .binary .disj counts.1 counts.2

def collectionEstimate (b : Expression.Ranges.Inputs k) (fuel : Nat) (c : Context n) (a : Expression.Collection k n) :
    Result Expression.Ranges.CollectionEstimate := do
  return (← (Expression.Ranges.analyzeAt b fuel).collection a c.estimates).val

def integerEstimate (b : Expression.Ranges.Inputs k) (fuel : Nat) (c : Context n) (a : Expression.Integer k n) :
    Result IR.Expr.Interval := do
  return (← (Expression.Ranges.analyzeAt b fuel).integer a c.estimates).val

structure Pass (k : Nat) where
  set : {n : Nat} → Context n → SetExpr k n → Result Temporal.Rel
  collection : {n : Nat} → Context n → Expression.Collection k n → Result (Value Temporal.Rel)
  integer : {n : Nat} → Context n → Expression.Integer k n → Result (Value Temporal.Integer)
  collections : {n : Nat} → Context n → Expression.Collections k n → Result (Value (List Temporal.Rel))
  predicate : {n : Nat} → Context n → Expression.Predicate k n → Result Partial.Translation
  atom : {n : Nat} → Context n → Expression.Atom k n → Result Partial.Translation
  formula : {n : Nat} → Context n → Expression.Formula k n → Result Partial.Translation

def present (v : IR.BehavioralStructural.Validated k) (c : Context n) : Temporal.Formula :=
  .mult .some (.inter c.lexical.this (Full.observedLive v))
def parentPresent (v : IR.BehavioralStructural.Validated k) (c : Context n) : Temporal.Formula :=
  .binary .disj (.subset c.lexical.this (Full.root v))
    (.mult .some (.join c.lexical.this (Full.step v .parent)))

def finiteStep (v : IR.BehavioralStructural.Validated k) (s : Step k) : Result Temporal.Rel :=
  match s with
  | .child d => if Full.integerDeclaration v d then
      .error { category := .unsupported, code := "behavioral.infinite-primitive-extent" }
    else .ok (Full.step v s)
  | _ => .ok (Full.step v s)

-- [impl->req~compiler-behavioral-partial-lowering~1]
def lowerStep (v : IR.BehavioralStructural.Validated k) (b : Expression.Ranges.Inputs k) (fuel : Nat) (next : Pass k) : Pass k where
  set := fun c a => do
    match a with
    | .empty => return .empty .unary
    | .this => return .inter c.lexical.this (Full.observedLive v)
    | .root => return Full.root v
    | .var i => return c.lexical.lookup i
    | .extent d =>
      if Full.integerDeclaration v d then
        throw { category := .unsupported, code := "behavioral.infinite-primitive-extent" }
      return Full.head v d
    | .union a d => return .union (← next.set c a) (← next.set c d)
    | .inter a d => return .inter (← next.set c a) (← next.set c d)
    | .diff a d => return .diff (← next.set c a) (← next.set c d)
    | .step s a => return .join (← next.set c a) (← finiteStep v s)
    | .thisStep s => return .join c.lexical.this (← finiteStep v s)
  collection := fun c a => do
    match a with
    | .set a => return .pure (← next.set c a)
    | .literal i => return .pure (.integer i)
    | .integer a => return integerCollection (← integerEstimate b fuel c a) (← next.integer c a)
    | .extreme op a => return collectionExtreme op (← collectionEstimate b fuel c a).values (← next.collection c a)
    | .union a d => return collectionUnion (← next.collection c a) (← next.collection c d)
    | .inter a d => return collectionInter (← next.collection c a) (← next.collection c d)
    | .diff a d => return collectionDiff (← next.collection c a) (← next.collection c d)
    | .step s a =>
      let relation ← finiteStep v s
      return (← next.collection c a).map fun value => .join value relation
    | .ofType d a => return (← next.collection c a).map fun value => .inter value (Full.pool v d)
    | .ite cond a d => return .conditional (← next.formula c cond) (← next.collection c a) (← next.collection c d)
  integer := fun c a => do
    match a with
    | .literal i => return .pure (.literal i)
    | .coerce a =>
      let estimate ← collectionEstimate b fuel c a
      let value ← next.collection c a
      return value.bind fun relation =>
        (Value.selections c.lexical.aliases relation estimate.budget).bind fun heads =>
          let guard := Temporal.Formula.binary .conj (.subset relation .ints)
            (.equal relation (Full.union heads))
          Value.guard guard (integerFold .sum (heads.map fun alias =>
            Value.pure (Temporal.Integer.scalar estimate.values.lower estimate.values.upper alias)))
    | .extract a => return integerExtract (← collectionEstimate b fuel c a).values (← next.collection c a)
    | .cardinality a => return integerCardinality c.lexical.aliases (← collectionEstimate b fuel c a).budget (← next.collection c a)
    | .binary op a d => return integerBinary op (← next.integer c a) (← next.integer c d)
    | .negate a => return integerNegate (← next.integer c a)
    | .fold op ds a =>
      let estimates ← (Expression.Ranges.analyzeAt b fuel).collections ds c.estimates
      let domains ← next.collections c ds
      valueMapM domains fun relations => do
        let choices := (relations.zip estimates.val).foldl (fun choices (relation, estimate) =>
          let selected := (Value.selections c.lexical.aliases relation estimate.budget).bind fun heads =>
            ⟨[(.equal relation (Full.union heads), heads)]⟩
          (choices.pair selected).map fun (before, now) => before ++ now) (Value.pure [])
        valueMapM choices fun occurrences => do
          let values ← occurrences.mapM fun alias =>
            next.integer (c.push alias (Expression.Ranges.singleton (Expression.Ranges.family estimates.val))) a
          return integerFold op values
    | .ite cond a d => return .conditional (← next.formula c cond) (← next.integer c a) (← next.integer c d)
  collections := fun c a => do
    match a with
    | .nil => return .pure []
    | .cons a ds => return ((← next.collection c a).pair (← next.collections c ds)).map fun (head, tail) => head :: tail
  predicate := fun c a => do
    match a with
    | .inhabited a => return (← next.collection c a).predicate (.mult .some)
    | .equal a d => return ((← next.collection c a).pair (← next.collection c d)).predicate fun (a, d) => .equal a d
    | .subset a d => return ((← next.collection c a).pair (← next.collection c d)).predicate fun (a, d) => .subset a d
    | .integerEqual a d => return ((← next.integer c a).pair (← next.integer c d)).predicate fun (a, d) => .compare .eq a d
    | .less a d => return ((← next.integer c a).pair (← next.integer c d)).predicate fun (a, d) => .compare .lt a d
  atom := fun c a => do
    match a with
    | .primitive a => next.predicate c a
    | .count q arity disjoint d a =>
      let estimate ← collectionEstimate b fuel c d
      let domain ← next.collection c d
      partialMapM domain fun relation => do
        let choices := (Value.selections c.lexical.aliases relation estimate.budget).bind fun heads =>
          ⟨[(.equal relation (Full.union heads), heads)]⟩
        partialMapM choices fun heads => do
          let bodies ← (tuples heads disjoint arity).mapM fun tuple => next.formula (c.extend tuple estimate) a
          return Partial.atom (all (bodies.map (·.defined))) (countTruth q (bodies.map (·.truth.raw)))
  formula := fun c a => do
    match a with
    | .truth => return Partial.truth
    | .atom a => next.atom c a
    | .not a => return Partial.negation (← next.formula c a)
    | .and a d => return Partial.conjunction (← next.formula c a) (← next.formula c d)
    | .or a d => return Partial.disjunction (← next.formula c a) (← next.formula c d)
    | .implies a d => return Partial.implication (← next.formula c a) (← next.formula c d)
    | .iff a d => return Partial.equivalence (← next.formula c a) (← next.formula c d)
    | .xor a d => return Partial.exclusiveOr (← next.formula c a) (← next.formula c d)
    | .ite cond a d => return Partial.conditional (← next.formula c cond) (← next.formula c a) (← next.formula c d)
    | .next a => return Partial.next (parentPresent v c) (← next.formula c a)
    | .eventually a => return Partial.eventually (parentPresent v c) (← next.formula c a)
    | .always a => return Partial.always (parentPresent v c) (← next.formula c a)
    | .strongUntil a d => return Partial.strongUntil (parentPresent v c) (← next.formula c a) (← next.formula c d)
    | .weakUntil a d => return Partial.weakUntil (parentPresent v c) (← next.formula c a) (← next.formula c d)
    | .initially a => return Partial.initially (present v c) (← next.formula c a)
    | .finally a => return Partial.finally (present v c) (← next.formula c a)
    | .quant q d a =>
      let estimate ← collectionEstimate b fuel c d
      let domain ← next.collection c d
      partialMapM domain fun relation => do
        let one ← next.formula ((c.shift 1).push (.var 0) (Expression.Ranges.singleton estimate)) a
        let two ← next.formula ((c.shift 2).push (.var 0) (Expression.Ranges.singleton estimate)) a
        return Partial.quantify q relation .truth one two
    | .letSet d a =>
      let estimate ← collectionEstimate b fuel c d
      let domain ← next.collection c d
      partialMapM domain fun relation =>
        partialMapM (Value.capture c.lexical.aliases relation estimate.budget) fun frozen =>
          next.formula (c.push frozen estimate) a

/-- Traversal exhaustion remains an explicit unsupported diagnostic. Public
compilation supplies an erased proof that the executable traversal budget
exceeds the syntax size; no accepted constructor is silently cut off. -/
def lowerAt (v : IR.BehavioralStructural.Validated k) (b : Expression.Ranges.Inputs k) (fuel : Nat) : Nat → Pass k :=
  Nat.rec ⟨fun _ _ => .error Expression.Ranges.budgetError, fun _ _ => .error Expression.Ranges.budgetError,
    fun _ _ => .error Expression.Ranges.budgetError, fun _ _ => .error Expression.Ranges.budgetError,
    fun _ _ => .error Expression.Ranges.budgetError, fun _ _ => .error Expression.Ranges.budgetError,
    fun _ _ => .error Expression.Ranges.budgetError⟩ (fun _ next => lowerStep v b fuel next)

-- [impl->req~compiler-behavioral-partial-lowering~1]
def lower (v : IR.BehavioralStructural.Validated k) (b : Expression.Ranges.Inputs k) (c : Context n)
    (a : Expression.Formula k n) (fuel : Nat) (_enough : sizeOf a < fuel) : Result Partial.Translation := do
  let _ ← Expression.Ranges.analyze b fuel a c.estimates
  (lowerAt v b fuel fuel).formula c a

end Expressions
end ClaferCompiler.Backend.Alloy.Behavioral.Full
