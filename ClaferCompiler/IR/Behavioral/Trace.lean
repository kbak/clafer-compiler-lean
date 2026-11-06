module

public import ClaferCompiler.IR.Behavioral.Admission

@[expose] public section
namespace ClaferCompiler.IR.Behavioral

-- [impl->req~compiler-behavioral-ir~1]
/-- One inventory for every frame; reference heads are ordinary distinct entries. -/
structure Identities (k o : Nat) where
  ids : Vector Nat o
  root : Fin o
  directType : Vector (Fin k) o
  parent : Vector (Option (Fin o)) o
  deriving DecidableEq, Repr

structure Frame (k o : Nat) where
  live : Vector Bool o
  references : List (Fin k × Fin o × Fin o)
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-ir~1]
/-- A nonempty lasso with explicit loop and no per-frame identity remapping. -/
structure Lasso (k o steps : Nat) where
  identities : Identities k o
  frames : Vector (Frame k o) steps
  loop : Fin steps
  deriving DecidableEq, Repr

def Lasso.index (l : Lasso k o steps) (t : Nat) : Fin steps :=
  if h : t < steps then ⟨t, h⟩
  else ⟨l.loop.val + (t - steps) % (steps - l.loop.val), by
    have := Nat.mod_lt (t - steps) (by have := l.loop.isLt; omega : 0 < steps - l.loop.val)
    have := l.loop.isLt
    omega⟩

def Lasso.at (l : Lasso k o steps) (t : Nat) : Frame k o := l.frames[l.index t]

/-- Independent identity, time and observation capacities; no integer profile here. -/
structure ObservationBounds where
  identities : Nat
  minSteps : Nat
  maxSteps : Nat
  referencesPerFrame : Nat
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-ir~1]
def fits (b : ObservationBounds) (l : Lasso k o steps) : Prop :=
  o ≤ b.identities ∧ 0 < b.minSteps ∧ b.minSteps ≤ steps ∧ steps ≤ b.maxSteps ∧
  ∀ i : Fin steps, l.frames[i].references.length ≤ b.referencesPerFrame

instance (b : ObservationBounds) (l : Lasso k o steps) : Decidable (fits b l) := by
  unfold fits
  infer_instance

def nextType (m : Structural.Core k) (d : Fin k) : Fin k := (m.get d).super.getD d
def walkType (m : Structural.Core k) (n : Nat) (d : Fin k) : Fin k :=
  Nat.repeat (nextType m) n d

/-- The finite carrier bounds the first visit, even before rank admission. -/
def ancestor (m : Structural.Core k) (d e : Fin k) : Bool :=
  decide (∃ j : Fin k, walkType m j.val d = e)

def identityChecks (m : Structural.Core k) (ids : Identities k o) : Prop :=
  (∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y) ∧
  ids.directType[ids.root] = m.root ∧
  (∀ x : Fin o, ids.directType[x] = m.root → x = ids.root) ∧
  (∀ x : Fin o, (m.get ids.directType[x]).isAbstract = false) ∧
  ids.parent[ids.root] = none ∧
  (∀ x : Fin o, x ≠ ids.root → ∃ p, ids.parent[x] = some p) ∧
  ∀ x p : Fin o, ids.parent[x] = some p →
    ∃ c : Fin k, (m.get ids.directType[x]).parent = some c ∧
      ancestor m ids.directType[p] c = true

instance (m : Structural.Core k) (ids : Identities k o) : Decidable (identityChecks m ids) := by
  unfold identityChecks
  infer_instance

/-- Representation checks only. Structural multiplicities/groups are source obligations. -/
def frameChecks (ids : Identities k o) (f : Frame k o) : Prop :=
  f.live[ids.root] = true ∧
  (∀ x p : Fin o, f.live[x] = true → ids.parent[x] = some p → f.live[p] = true) ∧
  f.references.Nodup ∧
  ∀ r ∈ f.references, f.live[r.2.1] = true ∧ f.live[r.2.2] = true

instance (ids : Identities k o) (f : Frame k o) : Decidable (frameChecks ids f) := by
  unfold frameChecks
  infer_instance

def traceChecks (m : Structural.Core k) (l : Lasso k o steps) : Prop :=
  identityChecks m l.identities ∧ ∀ i : Fin steps, frameChecks l.identities l.frames[i]

instance (m : Structural.Core k) (l : Lasso k o steps) : Decidable (traceChecks m l) := by
  unfold traceChecks
  infer_instance

structure CheckedTrace (m : Structural.Core k) (b : ObservationBounds) (o steps : Nat) where
  lasso : Lasso k o steps
  checked : traceChecks m lasso
  bounded : fits b lasso

-- [impl->req~compiler-behavioral-ir~1]
def admitTrace (m : Structural.Core k) (b : ObservationBounds) (l : Lasso k o steps) :
    Except Structural.Diagnostic (CheckedTrace m b o steps) :=
  if hc : traceChecks m l then
    if hb : fits b l then .ok ⟨l, hc, hb⟩
    else .error ⟨.unsupported, "behavioral.observation-bounds", "/bounds", none⟩
  else .error ⟨.malformed, "behavioral.trace", "/trace", none⟩

abbrev ObjectSet (o : Nat) := Fin o → Bool

structure Environment (o n : Nat) where
  this : Fin o
  lookup : Fin n → ObjectSet o

def Environment.closed (x : Fin o) : Environment o 0 := ⟨x, Fin.elim0⟩
def Environment.push (ρ : Environment o n) (s : ObjectSet o) : Environment o (n + 1) :=
  ⟨ρ.this, Fin.cases s ρ.lookup⟩

def head (m : Structural.Core k) (ids : Identities k o) (f : Frame k o) (d : Fin k)
    (x : Fin o) : Bool := f.live[x] && ancestor m ids.directType[x] d

def relation (m : Structural.Core k) (ids : Identities k o) (f : Frame k o) :
    Step k → Fin o → Fin o → Bool
  | .parent, x, p => ids.parent[x] == some p && f.live[p]
  | .child d, p, x => f.live[p] && f.live[x] && ids.parent[x] == some p &&
      ancestor m ids.directType[x] d && (m.get d).parent != none
  | .deref d, x, y => f.live[x] && f.live[y] && f.references.contains (d, x, y)

def image (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (s : Step k) (a : ObjectSet o) : ObjectSet o :=
  fun y => decide (∃ x : Fin o, a x = true ∧ relation m ids f s x y = true)

-- [impl->req~compiler-behavioral-interpretation~1]
/-- Evaluate finite observations now; captured sets themselves are not live-filtered. -/
def SetExpr.evalStep (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (ρ : Environment o n) (fuel : Nat)
    (next : (a : SetExpr k n) → sizeOf a < fuel → ObjectSet o)
    (a : SetExpr k n) : sizeOf a < fuel + 1 → ObjectSet o :=
  match a with
      | .empty => fun _ _ => false
      | .this => fun _ x => x == ρ.this && f.live[x]
      | .root => fun _ x => x == ids.root
      | .var v => fun _ => ρ.lookup v
      | .extent d => fun _ => head m ids f d
      | .union a b => fun h x => next a (by simp_all; omega) x || next b (by simp_all; omega) x
      | .inter a b => fun h x => next a (by simp_all; omega) x && next b (by simp_all; omega) x
      | .diff a b => fun h x => next a (by simp_all; omega) x && !(next b (by simp_all; omega) x)
      | .step s a => fun h => image m ids f s (next a (by simp_all; omega))
      | .thisStep s => fun _ => image m ids f s (fun x => x == ρ.this)

def SetExpr.evalAt (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (ρ : Environment o n) : (fuel : Nat) → (a : SetExpr k n) → sizeOf a < fuel → ObjectSet o :=
  Nat.rec (motive := fun fuel => (a : SetExpr k n) → sizeOf a < fuel → ObjectSet o)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (SetExpr.evalStep m ids f ρ)

theorem SetExpr.evalAt_succ (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (ρ : Environment o n) (fuel : Nat) (a : SetExpr k n) (h : sizeOf a < fuel + 1) :
    evalAt m ids f ρ (fuel + 1) a h = evalStep m ids f ρ fuel (evalAt m ids f ρ fuel) a h := rfl

def SetExpr.eval (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (ρ : Environment o n) (a : SetExpr k n) (fuel : Nat) (enough : sizeOf a < fuel) : ObjectSet o :=
  a.evalAt m ids f ρ fuel enough


def Atom.eval (m : Structural.Core k) (ids : Identities k o) (f : Frame k o)
    (ρ : Environment o n) (a : Atom k n) (fuel : Nat) (enough : sizeOf a < fuel) : Bool :=
  match a with
  | .inhabited a => decide (∃ x, a.eval m ids f ρ fuel (by simp_all; omega) x = true)
  | .equal a b => decide (∀ x, a.eval m ids f ρ fuel (by simp_all; omega) x =
      b.eval m ids f ρ fuel (by simp_all; omega) x)
  | .subset a b => decide (∀ x, a.eval m ids f ρ fuel (by simp_all; omega) x = true →
      b.eval m ids f ρ fuel (by simp_all; omega) x = true)

end ClaferCompiler.IR.Behavioral
