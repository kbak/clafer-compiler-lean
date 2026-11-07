module

public import ClaferCompiler.Backend.Alloy.Temporal.Syntax
public import ClaferCompiler.Backend.Alloy.Semantics

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Temporal

-- [impl->req~compiler-alloy-temporal-target~1]
inductive Atom where
  | object (id : Nat) | integer (value : Int)
  deriving DecidableEq, BEq

abbrev Relation := List (List Atom)
abbrev Environment := List Atom

/-- Object tables reuse the static relational representation. Integer atoms are
separate and cannot alias object IDs. There are no String literals or seq terms. -/
abbrev State := Alloy.Instance

structure Trace where
  /-- Finite shared allocation pool. Spare entries have no relational denotation. -/
  inventory : List Nat
  state : Nat → State

def integerAtoms (width : Nat) : List Atom :=
  (List.range (2 ^ width)).map fun n => .integer (minInt width + Int.ofNat n)

def State.universe (s : Schema) (width : Nat) (i : State) : List Atom :=
  ((s.declarations.signatures.zipIdx.filter fun (sig, _) => sig.parent.isNone).flatMap
    fun (_, id) => (i.signatures[id]?.getD []).map Atom.object).eraseDups ++ integerAtoms width

abbrev RelMeaning := Environment → Nat → Relation
abbrev FormulaMeaning := Environment → Nat → Prop

/-- Priming changes time, never the captured lexical environment. -/
def relationAlgebra (s : Schema) (width : Nat) (τ : Trace) : RelAlgebra RelMeaning where
  empty := fun _ _ _ => []
  sig := fun n _ t => (τ.state t |>.signatures[n]?.getD []).map fun x => [.object x]
  field := fun n _ t => (τ.state t |>.fields[n]?.getD []).map (List.map Atom.object)
  var := fun n env _ => (env[n]?).toList.map fun x => [x]
  univ := fun _ t => ((τ.state t).universe s width).map fun x => [x]
  iden := fun _ t => ((τ.state t).universe s width).map fun x => [x, x]
  ints := fun _ _ => (integerAtoms width).map fun x => [x]
  union := fun a b env t => (a env t ++ b env t).eraseDups
  inter := fun a b env t => (a env t).filter (b env t).contains
  diff := fun a b env t => (a env t).filter fun x => !(b env t).contains x
  product := fun a b env t => ((a env t).flatMap fun x => (b env t).map (x ++ ·)).eraseDups
  join := fun a b env t => ((a env t).flatMap fun x =>
    ((b env t).filter fun y => x.getLast? == y.head?).map fun y => x.dropLast ++ y.drop 1).eraseDups
  transpose := fun a env t => ((a env t).map List.reverse).eraseDups
  prime := fun a env t => a env (t + 1)

def Rel.eval (s : Schema) (width : Nat) (τ : Trace) (env : Environment) (t : Nat) (r : Rel) : Relation :=
  r.fold (relationAlgebra s width τ) (fun _ _ => []) env t

def Integer.eval (s : Schema) (width : Nat) (τ : Trace) (env : Environment) (t : Nat) (n : Integer) : Option Int :=
  n.fold {
    literal := boundedInt width
    count := fun r => boundedInt width (Int.ofNat (r.eval s width τ env t).eraseDups.length)
    add := fun a b => do boundedInt width ((← a) + (← b))
    subtract := fun a b => do boundedInt width ((← a) - (← b)) } none

/-- Ordinary classical temporal truth over natural time. The fold carries
closures, so neither captured environments nor time are reset by evaluation. -/
def formulaAlgebra (s : Schema) (width : Nat) (τ : Trace) : FormulaAlgebra FormulaMeaning where
  truth := fun _ _ => True
  falsity := fun _ _ => False
  equal := fun a b env t => ∀ row, row ∈ a.eval s width τ env t ↔ row ∈ b.eval s width τ env t
  subset := fun a b env t => ∀ row, row ∈ a.eval s width τ env t → row ∈ b.eval s width τ env t
  mult := fun m r env t => m.holds (r.eval s width τ env t).eraseDups.length = true
  compare := fun op a b env t => ∃ x y, a.eval s width τ env t = some x ∧
    b.eval s width τ env t = some y ∧ op.holds x y = true
  unary := fun op p env t => match op with
    | .neg => ¬ p env t
    | .after => p env (t + 1)
    | .always => ∀ j, t ≤ j → p env j
    | .eventually => ∃ j, t ≤ j ∧ p env j
    | .before => ∃ j, t = j + 1 ∧ p env j
    | .once => ∃ j, j ≤ t ∧ p env j
    | .historically => ∀ j, j ≤ t → p env j
  binary := fun op p q env t => match op with
    | .conj => p env t ∧ q env t
    | .disj => p env t ∨ q env t
    | .implies => p env t → q env t
    | .until => ∃ j, t ≤ j ∧ q env j ∧ ∀ k, t ≤ k → k < j → p env k
    | .releases => ∀ j, t ≤ j → (∀ k, t ≤ k → k < j → ¬ p env k) → q env j
    | .since => ∃ j, j ≤ t ∧ q env j ∧ ∀ k, j < k → k ≤ t → p env k
    | .triggered => ∀ j, j ≤ t → (∀ k, j < k → k ≤ t → ¬ p env k) → q env j
  all := fun r p env t => ∀ x, [x] ∈ r.eval s width τ env t → p (x :: env) t
  exists_ := fun r p env t => ∃ x, [x] ∈ r.eval s width τ env t ∧ p (x :: env) t

def Formula.Holds (s : Schema) (width : Nat) (τ : Trace) (env : Environment) (t : Nat) (p : Formula) : Prop :=
  p.fold (formulaAlgebra s width τ) (fun _ _ => False) env t

/-- Strict observation definedness is separate from truth: negating an overflowing
atom cannot make a model satisfy the command. Every arithmetic branch is checked. -/
def definedAlgebra (s : Schema) (width : Nat) (τ : Trace) : FormulaAlgebra FormulaMeaning where
  truth := fun _ _ => True
  falsity := fun _ _ => True
  equal := fun _ _ _ _ => True
  subset := fun _ _ _ _ => True
  mult := fun _ _ _ _ => True
  compare := fun _ a b env t => (a.eval s width τ env t).isSome = true ∧
    (b.eval s width τ env t).isSome = true
  unary := fun op p env t => match op with
    | .neg => p env t
    | .after => p env (t + 1)
    | .before => ∀ j, t = j + 1 → p env j
    | .once | .historically => ∀ j, j ≤ t → p env j
    | .always | .eventually => ∀ j, t ≤ j → p env j
  binary := fun op p q env t => match op with
    | .conj | .disj | .implies => p env t ∧ q env t
    | .until | .releases => ∀ j, t ≤ j → p env j ∧ q env j
    | .since | .triggered => ∀ j, j ≤ t → p env j ∧ q env j
  all := fun r p env t => ∀ x, [x] ∈ r.eval s width τ env t → p (x :: env) t
  exists_ := fun r p env t => ∀ x, [x] ∈ r.eval s width τ env t → p (x :: env) t

def Formula.Defined (s : Schema) (width : Nat) (τ : Trace) (env : Environment) (t : Nat) (p : Formula) : Prop :=
  p.fold (definedAlgebra s width τ) (fun _ _ => False) env t

/-- Inventory is shared; declarations hold in every state. Type disjointness is
trace-wide, so an object cannot migrate between sibling types on reappearance. -/
def Trace.Declarations (s : Schema) (τ : Trace) : Prop :=
  τ.inventory.Pairwise (· ≠ ·) ∧
  (∀ t, (τ.state t).wellFormed s.declarations = true ∧
    (τ.state t).declarations s.declarations = true ∧
    ∀ xs ∈ (τ.state t).signatures, ∀ x ∈ xs, x ∈ τ.inventory) ∧
  (∀ (i : Nat), s.mutableSignatures[i]? = some false → ∀ t x,
    x ∈ ((τ.state t).signatures[i]?.getD []) ↔ x ∈ ((τ.state 0).signatures[i]?.getD [])) ∧
  (∀ (i : Nat), s.mutableFields[i]? = some false → ∀ t row,
    row ∈ ((τ.state t).fields[i]?.getD []) ↔ row ∈ ((τ.state 0).fields[i]?.getD [])) ∧
  (∀ (i j : Nat) (a b : Alloy.Signature), s.declarations.signatures[i]? = some a →
    s.declarations.signatures[j]? = some b → i ≠ j → a.parent = b.parent →
    ∀ t u x, x ∈ ((τ.state t).signatures[i]?.getD []) →
      x ∉ ((τ.state u).signatures[j]?.getD []))

/-- Per-signature scopes bound the union over all times, never frame population.
Exact scopes are admitted only on static signatures. Spare pool entries are ignored. -/
def Trace.InScope (scopes : List Scope) (τ : Trace) : Prop :=
  ∀ (i : Nat) (scope : Scope), scopes[i]? = some scope → ∃ used : List Nat,
    used.Pairwise (· ≠ ·) ∧
    (∀ x, x ∈ used ↔ ∃ t, x ∈ ((τ.state t).signatures[i]?.getD [])) ∧
    (if scope.exact then used.length = scope.size else used.length ≤ scope.size)

-- [impl->req~compiler-alloy-temporal-target~1]
def Satisfies (m : Module) (τ : Trace) : Prop :=
  m.wellTyped = true ∧ m.safeBounds = true ∧ τ.Declarations m.schema ∧
  τ.InScope m.command.scopes ∧
  (∀ f ∈ m.facts, f.Defined m.schema m.command.bitwidth τ [] 0 ∧
    f.Holds m.schema m.command.bitwidth τ [] 0) ∧
  m.command.body.Defined m.schema m.command.bitwidth τ [] 0 ∧
  (match m.command.kind with
   | .run => m.command.body.Holds m.schema m.command.bitwidth τ [] 0
   | .check => ¬ m.command.body.Holds m.schema m.command.bitwidth τ [] 0)

/-- Lasso frames are valuations, not temporal truth caches. -/
structure Lasso where
  inventory : List Nat
  frames : List State
  loop : Nat
  nonempty : 0 < frames.length
  loopValid : loop < frames.length

inductive LassoError where
  | emptyTrace | invalidLoop | malformedFrame | invalidInventory
  deriving DecidableEq, BEq

/-- Shape admission does not assume declaration/fact truth. A well-formed
candidate may still violate scopes, immutability or any target formula. -/
def checkLasso (s : Schema) (inventory : List Nat) (frames : List State) (loop : Nat) :
    Except LassoError Lasso :=
  if hn : 0 < frames.length then
    if hl : loop < frames.length then
      if !(frames.all fun frame => frame.wellFormed s.declarations) then
        .error .malformedFrame
      else if !(inventory.Pairwise (· ≠ ·)) || !(frames.all fun frame =>
          frame.signatures.all fun xs => xs.all inventory.contains) then
        .error .invalidInventory
      else .ok ⟨inventory, frames, loop, hn, hl⟩
    else .error .invalidLoop
  else .error .emptyTrace

def Lasso.index (l : Lasso) (t : Nat) : Nat :=
  if t < l.frames.length then t else
    l.loop + (t - l.frames.length) % (l.frames.length - l.loop)

def Lasso.unfold (l : Lasso) : Trace :=
  ⟨l.inventory, fun t => l.frames[l.index t]?.getD ⟨[], [], []⟩⟩

def Lasso.Fits (l : Lasso) (c : Command) : Prop :=
  c.minSteps ≤ l.frames.length ∧ l.frames.length ≤ c.maxSteps

def Lasso.Satisfies (m : Module) (l : Lasso) : Prop :=
  l.Fits m.command ∧ Temporal.Satisfies m l.unfold

-- [proof->req~compiler-alloy-temporal-target~1]
theorem Lasso.index_lt (l : Lasso) (t : Nat) : l.index t < l.frames.length := by
  unfold Lasso.index
  split
  · assumption
  · have h := Nat.mod_lt (t - l.frames.length) (show 0 < l.frames.length - l.loop by
      have := l.loopValid; omega)
    have := l.loopValid
    omega

theorem Lasso.index_initial (l : Lasso) : l.index 0 = 0 := by
  simp [Lasso.index, l.nonempty]

theorem Lasso.index_loop (l : Lasso) : l.index l.frames.length = l.loop := by
  simp [Lasso.index]

theorem Lasso.index_periodic (l : Lasso) (t : Nat) (h : l.frames.length ≤ t) :
    l.index (t + (l.frames.length - l.loop)) = l.index t := by
  have ht : ¬ t < l.frames.length := by omega
  have hs : ¬ t + (l.frames.length - l.loop) < l.frames.length := by omega
  simp only [Lasso.index, ite_eq_right ht, ite_eq_right hs]
  rw [show t + (l.frames.length - l.loop) - l.frames.length =
    (t - l.frames.length) + (l.frames.length - l.loop) by omega]
  simp

theorem prime_eval (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat) (r : Rel) :
    (Rel.prime r).eval s w τ e t = r.eval s w τ e (t + 1) := by
  simp only [Rel.eval, Rel.fold, Rel.prime, List.foldl_append, List.foldl_cons, List.foldl_nil]
  cases h : r.code.foldl (relationAlgebra s w τ).step (some []) with
  | none => rfl
  | some xs =>
    cases xs with
    | nil => rfl
    | cons x xs => cases xs <;> rfl

theorem prime_capture (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t i : Nat) :
    (Rel.prime (.var i)).eval s w τ e t = (Rel.var i).eval s w τ e t := rfl

/-- Immutability is extensional; tuple/list ordering has no semantic significance. -/
theorem static_signature_prime (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t i : Nat)
    (hd : τ.Declarations s) (hs : s.mutableSignatures[i]? = some false) :
    (Formula.equal (.sig i) (.prime (.sig i))).Holds s w τ e t := by
  intro row
  have same := hd.2.2.1 i hs
  change row ∈ (((τ.state t).signatures[i]?.getD []).map fun x => [Atom.object x]) ↔
    row ∈ (((τ.state (t + 1)).signatures[i]?.getD []).map fun x => [Atom.object x])
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨x, (same (t + 1) x).mpr ((same t x).mp hx), rfl⟩
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨x, (same t x).mpr ((same (t + 1) x).mp hx), rfl⟩

-- [proof->req~compiler-alloy-temporal-target~1]
theorem before_initial (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p : Formula) (hp : p.Built) :
    ¬ (Formula.unary .before p).Holds s w τ e 0 := by
  unfold Formula.Holds
  rw [Formula.fold_unary _ _ _ _ hp]
  simp [formulaAlgebra]

theorem before_succ (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p : Formula) (hp : p.Built) (t : Nat) :
    (Formula.unary .before p).Holds s w τ e (t + 1) ↔ p.Holds s w τ e t := by
  unfold Formula.Holds
  rw [Formula.fold_unary _ _ _ _ hp]
  simp [formulaAlgebra]

theorem birth_initial (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p : Formula) (hp : p.Built) :
    p.birth.Holds s w τ e 0 ↔ p.Holds s w τ e 0 := by
  unfold Formula.birth Formula.Holds
  rw [Formula.fold_binary _ _ _ _ _ hp (.unary .neg (.unary .before hp)),
    Formula.fold_unary _ _ _ _ (.unary .before hp), Formula.fold_unary _ _ _ _ hp]
  simp [formulaAlgebra]

theorem birth_succ (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p : Formula) (hp : p.Built) (t : Nat) :
    p.birth.Holds s w τ e (t + 1) ↔
      p.Holds s w τ e (t + 1) ∧ ¬ p.Holds s w τ e t := by
  unfold Formula.birth Formula.Holds
  rw [Formula.fold_binary _ _ _ _ _ hp (.unary .neg (.unary .before hp)),
    Formula.fold_unary _ _ _ _ (.unary .before hp), Formula.fold_unary _ _ _ _ hp]
  simp [formulaAlgebra]

theorem weakUntil_meaning (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (p q : Formula) (hp : p.Built) (hq : q.Built) (t : Nat) :
    (p.weakUntil q).Holds s w τ e t ↔
      (Formula.binary .until p q).Holds s w τ e t ∨
      (Formula.unary .always p).Holds s w τ e t := by
  simp only [Formula.weakUntil, Formula.Holds,
    Formula.fold_binary _ _ _ _ _ (.binary .until hp hq) (.unary .always hp)]
  rfl

end ClaferCompiler.Backend.Alloy.Temporal
