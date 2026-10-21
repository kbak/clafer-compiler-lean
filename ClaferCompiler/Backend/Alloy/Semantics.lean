module

public import ClaferCompiler.Backend.Alloy.Bounds

@[expose] public section

namespace ClaferCompiler.Backend.Alloy

/-! Finite set-of-tuples interpretation of the static target fragment.
Natural numbers are opaque atom identities, unrelated to bounded Alloy integers.
[impl->req~compiler-alloy-core~1]
[impl->req~compiler-bounds~1] -/

abbrev Tuple := List Nat
abbrev Relation := List Tuple

structure Instance where
  signatures : List (List Nat)
  fields : List Relation := []
  /-- Per-signature owner/value rows for declared scalar fields. -/
  values : List (List (Nat × Int)) := []

def relationSubset (a b : Relation) : Bool := a.all b.contains

/-- Evaluation is total on raw syntax; only `evaluate` admits a public candidate.
Canonical set operations discard duplicate tuples introduced by joins/unions. -/
def Rel.eval (i : Instance) (env : List Nat) (rel : Rel) : Relation :=
  rel.fold {
    empty := fun _ => []
    sig := fun s => (i.signatures[s]?.getD []).map fun x => [x]
    field := fun f => i.fields[f]?.getD []
    var := fun v => (env[v]?).toList.map fun x => [x]
    union := fun a b => (a ++ b).eraseDups
    inter := fun a b => a.filter b.contains
    diff := fun a b => a.filter fun t => !b.contains t
    product := fun a b => (a.flatMap fun x => b.map (x ++ ·)).eraseDups
    join := fun a b => (a.flatMap fun x =>
      (b.filter fun y => x.getLast? == y.head?).map fun y => x.dropLast ++ y.drop 1).eraseDups
    transpose := fun a => (a.map List.reverse).eraseDups
    diagonal := fun a => (a.filterMap fun t => match t with
      | [x] => some [x, x] | _ => none).eraseDups
  } []

/-- A bounded conditional value observation. The lower endpoint is an internal
fallback, guarded separately by source definedness; it is not source extraction.
The matching target text uses a conditional and a singleton scalar field image. -/
def Instance.scalarValue (i : Instance) (env : List Nat) (owner : Nat)
    (lo hi : Int) (r : Rel) : Int :=
  match (r.eval i env).eraseDups with
  | [[atom]] =>
    match ((i.values[owner]?.getD []).filter (fun row => row.1 == atom)).map Prod.snd |>.eraseDups with
    | [value] => if lo ≤ value && value ≤ hi then value else lo
    | _ => lo
  | _ => lo

/-- Declared `one Int` fields have exactly one representable value per owner.
No scalar field is introduced for ordinary M1 signatures. -/
def Instance.scalarFields (width : Nat) (s : Schema) (i : Instance) : Bool :=
  s.signatures.zipIdx.all fun (decl, owner) =>
    !decl.scalar ||
      let rows := i.values[owner]?.getD []
      let objects := i.signatures[owner]?.getD []
      rows.all (fun row => objects.contains row.1 && fitsInt width row.2) &&
      (rows.map Prod.fst).Pairwise (· ≠ ·) &&
      objects.all (fun atom => rows.any (fun row => row.1 == atom))

/-! [impl->req~compiler-target-arithmetic~1] -/
def Integer.eval (width : Nat) (i : Instance) (env : List Nat) (n : Integer) : Option Int :=
  n.fold {
    literal := boundedInt width
    count := fun r => boundedInt width (Int.ofNat (r.eval i env).eraseDups.length)
    scalar := fun owner lo hi r => boundedInt width (i.scalarValue env owner lo hi r)
    add := fun a b => do boundedInt width ((← a) + (← b))
    subtract := fun a b => do boundedInt width ((← a) - (← b))
  } none

def Multiplicity.holds : Multiplicity → Nat → Bool
  | .set, _ => true
  | .lone, n => n ≤ 1
  | .one, n => n == 1
  | .some, n => 0 < n

def Comparison.holds : Comparison → Int → Int → Bool
  | .eq, a, b => a == b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b

/-- Undefined integer observations propagate strictly through Boolean operators.
Only actual domain members evaluate a quantifier body. -/
def Formula.eval (width : Nat) (i : Instance) (env : List Nat) (formula : Formula) : Option Bool :=
  formula.fold {
    truth := fun _ => some true, falsity := fun _ => some false
    equal := fun a b e => some (relationSubset (a.eval i e) (b.eval i e) &&
      relationSubset (b.eval i e) (a.eval i e))
    subset := fun a b e => some (relationSubset (a.eval i e) (b.eval i e))
    mult := fun m r e => some (m.holds (r.eval i e).eraseDups.length)
    compare := fun op a b e => do
      let x ← a.eval width i e
      let y ← b.eval width i e
      pure (op.holds x y)
    neg := fun p e => do pure (!(← p e))
    conj := fun p q e => do
      let x ← p e
      let y ← q e
      pure (x && y)
    disj := fun p q e => do
      let x ← p e
      let y ← q e
      pure (x || y)
    implies := fun p q e => do
      let x ← p e
      let y ← q e
      pure (!x || y)
    all := fun domain body e => do
      let values ← (domain.eval i e).mapM fun tuple => body (tuple.headD 0 :: e)
      pure (values.all id)
    exists_ := fun domain body e => do
      let values ← (domain.eval i e).mapM fun tuple => body (tuple.headD 0 :: e)
      pure (values.any id)
  } (fun _ => none) env

/-- Malformed tables are distinct from a well-formed candidate violating facts.
There is no atom pool payload: unused allocation slots have no denotation. -/
def Instance.wellFormed (s : Schema) (i : Instance) : Bool :=
  i.signatures.length == s.signatures.length && i.fields.length == s.fields.length &&
  i.signatures.all (fun xs => xs.eraseDups.length == xs.length) &&
  i.fields.all (fun ts => ts.eraseDups.length == ts.length && ts.all (fun t => t.length == 2))

def Instance.declarations (s : Schema) (i : Instance) : Bool :=
  (s.signatures.zipIdx.all fun (decl, id) => Id.run do
    let extent := i.signatures[id]?.getD []
    let children := (s.signatures.zipIdx.filter fun (child, _) => child.parent == some id).map Prod.snd
    let included := decl.parent.all fun parent => extent.all (i.signatures[parent]?.getD []).contains
    let covered := !decl.isAbstract || children.isEmpty ||
      extent.all (fun atom => children.any fun child => (i.signatures[child]?.getD []).contains atom)
    let disjoint := s.signatures.zipIdx.all fun (other, j) =>
      id == j || decl.parent != other.parent ||
      extent.all (fun atom => !(i.signatures[j]?.getD []).contains atom)
    return included && covered && disjoint && decl.multiplicity.holds extent.length) &&
  (s.fields.zipIdx.all fun (field, id) =>
    let tuples := i.fields[id]?.getD []
    let owner := i.signatures[field.owner]?.getD []
    let target := i.signatures[field.target]?.getD []
    (tuples.all fun tuple => match tuple with
      | [a, b] => owner.contains a && target.contains b
      | _ => false) &&
    owner.all (fun atom => field.multiplicity.holds
      (tuples.filter fun tuple => tuple.head? == some atom).length))

def Instance.inScope (scopes : List Scope) (i : Instance) : Bool :=
  (scopes.zip i.signatures).all fun (scope, atoms) =>
    if scope.exact then atoms.length == scope.size else atoms.length ≤ scope.size

/-- Conjoin the facts and the run body (or negated check body), with strict
definedness. No source predicate, compilation result or encoder occurs here. -/
def Module.eval (m : Module) (i : Instance) : Option Bool := do
  let facts ← m.facts.mapM (fun f => f.eval m.command.bitwidth i [])
  let body ← m.command.body.eval m.command.bitwidth i []
  pure (facts.all id && body == (m.command.kind == .run) &&
    i.scalarFields m.command.bitwidth m.schema)

/-- Independent target satisfaction, including command polarity and declarations.
For `check`, true means a counterexample, not validity of the assertion. -/
def Satisfies (m : Module) (i : Instance) : Prop :=
  m.wellTyped = true ∧ m.safeBounds = true ∧ i.wellFormed m.schema = true ∧
  i.declarations m.schema = true ∧ i.inScope m.command.scopes = true ∧
  m.eval i = some true

inductive EvaluationError where
  | malformedInstance | unrepresentableInteger
  deriving DecidableEq, BEq

def evaluate (m : CheckedModule) (i : Instance) : Except EvaluationError Bool :=
  if !i.wellFormed m.raw.schema then .error .malformedInstance
  else if !i.declarations m.raw.schema || !i.inScope m.raw.command.scopes then .ok false
  else match m.raw.eval i with
    | none => .error .unrepresentableInteger
    | some value => .ok value

theorem evaluate_iff_satisfies (m : CheckedModule) (i : Instance) :
    evaluate m i = .ok true ↔ Satisfies m.raw i := by
  unfold evaluate Satisfies
  rw [m.typed, m.bounded]
  cases hw : i.wellFormed m.raw.schema <;>
    cases hd : i.declarations m.raw.schema <;>
    cases hs : i.inScope m.raw.command.scopes <;> simp_all
  cases he : m.raw.eval i <;> simp_all

theorem eval_neg_truth (w : Nat) (i : Instance) (env : List Nat) :
    (Formula.neg .truth).eval w i env = some false := rfl

theorem eval_all_empty (w : Nat) (i : Instance) (env : List Nat) :
    (Formula.all (.empty .unary) .falsity).eval w i env = some true := rfl

theorem eval_exists_empty (w : Nat) (i : Instance) (env : List Nat) :
    (Formula.exists_ (.empty .unary) .truth).eval w i env = some false := rfl

end ClaferCompiler.Backend.Alloy
