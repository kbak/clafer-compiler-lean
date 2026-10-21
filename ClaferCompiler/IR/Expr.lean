module

public import ClaferCompiler.IR.Structural

@[expose] public section
namespace ClaferCompiler.IR.Expr

inductive MapKind where
  | head | parent | dereference | target | inclusion
  deriving DecidableEq, Repr

structure MapRef (n : Nat) where
  owner : Nat
  kind : MapKind
  source : Fin n
  target : Fin n
  name : String := ""
  deriving DecidableEq, Repr

/-- Positions retain support occurrences, including repeated declaration/map IDs. -/
structure Support (n m : Nat) where
  classes : Vector Nat n
  maps : Vector (MapRef n) m
  context : Fin n
  integer : Vector Bool n
  deriving DecidableEq, Repr

inductive Collection (n : Nat) where
  | objects (element : Fin n)
  | relation (source target : Fin n)
  deriving DecidableEq, Repr

inductive Ty (n : Nat) where
  | boolean | integer | collection (shape : Collection n)
  deriving DecidableEq, Repr

structure Local (n : Nat) where
  id : Nat
  name : String
  element : Fin n
  deriving DecidableEq, Repr

inductive SetOp where
  | union | difference | intersection
  deriving DecidableEq, Repr
inductive Arithmetic where
  | add | subtract
  deriving DecidableEq, Repr

/-- Explicit paths; equal IDs are permitted across distinct support positions. -/
inductive Path (n m : Nat) where
  | same
  | inclusion (edge : Fin m)
  | trans (middle : Fin n) (first second : Path n m)

noncomputable def Path.Valid (s : Support n m) (x y : Fin n) : Path n m → Prop
  | .same => s.classes[x] = s.classes[y]
  | .inclusion e => s.maps[e].kind = .inclusion ∧ s.maps[e].source = x ∧ s.maps[e].target = y
  | .trans z p q => p.Valid s x z ∧ q.Valid s z y

termination_by structural p => p

noncomputable def Path.depth : Path n m → Nat
  | .same | .inclusion _ => 1
  | .trans _ p q => 1 + p.depth + q.depth

def widenAt (s : Support n m) : (fuel : Nat) → (p : Path n m) →
    p.depth < fuel → (x y : Fin n) → Decidable (p.Valid s x y) :=
  Nat.rec (motive := fun fuel => (p : Path n m) → p.depth < fuel →
    (x y : Fin n) → Decidable (p.Valid s x y))
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun _ next p h x y => by
      cases p with
      | same => unfold Path.Valid; infer_instance
      | inclusion => unfold Path.Valid; infer_instance
      | trans z p q =>
        haveI := next p (by simp_all only [Path.depth]; omega) x z
        haveI := next q (by simp_all only [Path.depth]; omega) z y
        unfold Path.Valid; infer_instance)

noncomputable instance widenDec (s : Support n m) (x y : Fin n) (p : Path n m) : Decidable (p.Valid s x y) :=
  widenAt s (p.depth + 1) p (Nat.lt_succ_self _) x y

/-- Raw annotated syntax. `Term` adds a cached traversal budget;
`Checked` certifies sorts and lexical scope;
annotations do not assert typing until checked. Spans retain original UTF-8 bytes. -/
inductive Syntax (n m : Nat) where
  | boolean (value : Bool)
  | integer (value : Int)
  | this
  | extent (vertex : Fin n)
  | var (position : Nat)
  | map (edge : Fin m)
  | and (left right : Syntax n m)
  | not (body : Syntax n m)
  | equal (type : Ty n) (left right : Syntax n m)
  | less (left right : Syntax n m)
  | arithmetic (op : Arithmetic) (left right : Syntax n m)
  | integerOf (vertex : Fin n) (body : Syntax n m)
  | cardinality (shape : Collection n) (body : Syntax n m)
  | setOp (op : SetOp) (shape : Collection n) (left right : Syntax n m)
  | subset (shape : Collection n) (left right : Syntax n m)
  | image (source target : Fin n) (objects relation : Syntax n m)
  | join (source middle target : Fin n) (left right : Syntax n m)
  | widenObjects (source target : Fin n) (path : Path n m) (body : Syntax n m)
  | widenRelation (source target source' target' : Fin n)
      (left right : Path n m) (body : Syntax n m)
  | all (binder : Local n) (domain body : Syntax n m)
  | located (span : Structural.SourceSpan) (body : Syntax n m)

noncomputable def Syntax.depth : Syntax n m → Nat
  | .and a b | .equal _ a b | .less a b | .arithmetic _ a b | .setOp _ _ a b
  | .subset _ a b | .image _ _ a b | .join _ _ _ a b | .all _ a b => 1 + a.depth + b.depth
  | .not a | .integerOf _ a | .cardinality _ a | .located _ a => 1 + a.depth
  | .widenObjects _ _ p a => 1 + p.depth + a.depth
  | .widenRelation _ _ _ _ p q a => 1 + p.depth + q.depth + a.depth
  | _ => 1

/-- Type and lexical checks are independent of bounds, truth and definedness. -/
noncomputable def Syntax.Typed (s : Support n m) (Γ : List (Local n)) (t : Ty n) : Syntax n m → Prop
  | .boolean _ => t = .boolean
  | .integer _ => t = .integer
  | .this => t = .collection (.objects s.context)
  | .extent x => t = .collection (.objects x)
  | .var i => match Γ[i]? with | none => False | some b => t = .collection (.objects b.element)
  | .map e => t = .collection (.relation s.maps[e].source s.maps[e].target)
  | .and a b => t = .boolean ∧ a.Typed s Γ .boolean ∧ b.Typed s Γ .boolean
  | .not a => t = .boolean ∧ a.Typed s Γ .boolean
  | .equal k a b => t = .boolean ∧ a.Typed s Γ k ∧ b.Typed s Γ k
  | .less a b => t = .boolean ∧ a.Typed s Γ .integer ∧ b.Typed s Γ .integer
  | .arithmetic _ a b => t = .integer ∧ a.Typed s Γ .integer ∧ b.Typed s Γ .integer
  | .integerOf x a => t = .integer ∧ s.integer[x] = true ∧ a.Typed s Γ (.collection (.objects x))
  | .cardinality k a => t = .integer ∧ a.Typed s Γ (.collection k)
  | .setOp _ k a b => t = .collection k ∧ a.Typed s Γ (.collection k) ∧ b.Typed s Γ (.collection k)
  | .subset k a b => t = .boolean ∧ a.Typed s Γ (.collection k) ∧ b.Typed s Γ (.collection k)
  | .image x y a b => t = .collection (.objects y) ∧
      a.Typed s Γ (.collection (.objects x)) ∧ b.Typed s Γ (.collection (.relation x y))
  | .join x y z a b => t = .collection (.relation x z) ∧
      a.Typed s Γ (.collection (.relation x y)) ∧ b.Typed s Γ (.collection (.relation y z))
  | .widenObjects x y p a => t = .collection (.objects y) ∧
      p.Valid s x y ∧ a.Typed s Γ (.collection (.objects x))
  | .widenRelation x y x' y' p q a => t = .collection (.relation x' y') ∧
      p.Valid s x x' ∧ q.Valid s y y' ∧ a.Typed s Γ (.collection (.relation x y))
  | .all b d a => t = .boolean ∧ (∀ old ∈ Γ, old.id ≠ b.id) ∧
      d.Typed s Γ (.collection (.objects b.element)) ∧ a.Typed s (b :: Γ) .boolean
  | .located p a => p.startByte ≤ p.endByte ∧ a.Typed s Γ t

termination_by structural e => e

/-- Standard-library natural recursion avoids generated project recursion helpers.
The fuel proof is structural size, not a user supplied limit or a skipped check. -/
def typedAt (s : Support n m) : (fuel : Nat) → (e : Syntax n m) → e.depth < fuel →
    (Γ : List (Local n)) → (t : Ty n) → Decidable (e.Typed s Γ t) :=
  Nat.rec (motive := fun fuel => (e : Syntax n m) → e.depth < fuel →
    (Γ : List (Local n)) → (t : Ty n) → Decidable (e.Typed s Γ t))
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun fuel next e h Γ t => by
      cases e with
      | boolean b =>
        unfold Syntax.Typed; infer_instance
      | integer i =>
        unfold Syntax.Typed; infer_instance
      | this =>
        unfold Syntax.Typed; infer_instance
      | extent x =>
        unfold Syntax.Typed; infer_instance
      | var i =>
        unfold Syntax.Typed; cases Γ[i]? <;> infer_instance
      | map e =>
        unfold Syntax.Typed; infer_instance
      | and a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ .boolean
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ .boolean
        unfold Syntax.Typed; infer_instance
      | not a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ .boolean
        unfold Syntax.Typed; infer_instance
      | equal k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ k
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ k
        unfold Syntax.Typed; infer_instance
      | less a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ .integer
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ .integer
        unfold Syntax.Typed; infer_instance
      | arithmetic op a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ .integer
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ .integer
        unfold Syntax.Typed; infer_instance
      | integerOf x a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection (.objects x))
        unfold Syntax.Typed; infer_instance
      | cardinality k a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection k)
        unfold Syntax.Typed; infer_instance
      | setOp op k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection k)
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ (.collection k)
        unfold Syntax.Typed; infer_instance
      | subset k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection k)
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ (.collection k)
        unfold Syntax.Typed; infer_instance
      | image x y a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection (.objects x))
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ (.collection (.relation x y))
        unfold Syntax.Typed; infer_instance
      | join x y z a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection (.relation x y))
        haveI := next b (by simp_all only [Syntax.depth]; omega) Γ (.collection (.relation y z))
        unfold Syntax.Typed; infer_instance
      | widenObjects x y p a =>
        haveI := widenAt s fuel p (by simp_all only [Syntax.depth]; omega) x y
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection (.objects x))
        unfold Syntax.Typed; infer_instance
      | widenRelation x y u v p q a =>
        haveI := widenAt s fuel p (by simp_all only [Syntax.depth]; omega) x u
        haveI := widenAt s fuel q (by simp_all only [Syntax.depth]; omega) y v
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ (.collection (.relation x y))
        unfold Syntax.Typed; infer_instance
      | all b d a =>
        haveI := next d (by simp_all only [Syntax.depth]; omega) Γ (.collection (.objects b.element))
        haveI := next a (by simp_all only [Syntax.depth]; omega) (b :: Γ) .boolean
        unfold Syntax.Typed; infer_instance
      | located p a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega) Γ t
        unfold Syntax.Typed; infer_instance)

noncomputable instance typedDec (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Syntax n m) :
    Decidable (e.Typed s Γ t) := typedAt s (e.depth + 1) e (Nat.lt_succ_self _) Γ t

/-- Exact occurrence inventories, with operand order and repeated maps retained. -/
noncomputable def Syntax.extents : Syntax n m → List (Fin n)
  | .extent x => [x]
  | .and a b | .equal _ a b | .less a b | .arithmetic _ a b | .setOp _ _ a b
  | .subset _ a b | .image _ _ a b | .join _ _ _ a b | .all _ a b => a.extents ++ b.extents
  | .not a | .integerOf _ a | .cardinality _ a | .widenObjects _ _ _ a
  | .widenRelation _ _ _ _ _ _ a | .located _ a => a.extents
  | _ => []

termination_by structural e => e

noncomputable def Syntax.maps : Syntax n m → List (Fin m)
  | .map e => [e]
  | .and a b | .equal _ a b | .less a b | .arithmetic _ a b | .setOp _ _ a b
  | .subset _ a b | .image _ _ a b | .join _ _ _ a b | .all _ a b => a.maps ++ b.maps
  | .not a | .integerOf _ a | .cardinality _ a | .widenObjects _ _ _ a
  | .widenRelation _ _ _ _ _ _ a | .located _ a => a.maps
  | _ => []

termination_by structural e => e

def Syntax.Observed (s : Support n m) (e : Syntax n m) : Prop :=
  ∀ x ∈ e.extents, s.integer[x] = false

def observedAt (s : Support n m) : (fuel : Nat) → (e : Syntax n m) →
    e.depth < fuel → Decidable (e.Observed s) :=
  Nat.rec (motive := fun fuel => (e : Syntax n m) → e.depth < fuel → Decidable (e.Observed s))
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun _ next e h => by
      cases e with
      | boolean b => exact isTrue (by simp [Syntax.Observed, Syntax.extents])
      | integer i => exact isTrue (by simp [Syntax.Observed, Syntax.extents])
      | this => exact isTrue (by simp [Syntax.Observed, Syntax.extents])
      | var i => exact isTrue (by simp [Syntax.Observed, Syntax.extents])
      | map f => exact isTrue (by simp [Syntax.Observed, Syntax.extents])
      | extent x =>
        exact decidable_of_iff (s.integer[x] = false) (by simp [Syntax.Observed, Syntax.extents])
      | not a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | integerOf x a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | cardinality k a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | widenObjects x y p a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | widenRelation x y x1 y1 p q a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | located p a =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s) (by simp [Syntax.Observed, Syntax.extents])
      | and a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | equal k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | less a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | arithmetic op a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | setOp op k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | subset k a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | image x y a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | join x y z a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and])
      | all x a b =>
        haveI := next a (by simp_all only [Syntax.depth]; omega)
        haveI := next b (by simp_all only [Syntax.depth]; omega)
        exact decidable_of_iff (a.Observed s ∧ b.Observed s) (by simp [Syntax.Observed, Syntax.extents, or_imp, forall_and]))

noncomputable instance (s : Support n m) (e : Syntax n m) : Decidable (e.Observed s) :=
  observedAt s (e.depth + 1) e (Nat.lt_succ_self _)

/-- Cached structural budgets make native traversals use only standard-library
recursion. The proof rules out exhaustion; the caller cannot truncate a check. -/
structure Widen (n m : Nat) where
  path : Path n m
  budget : Nat
  bound : path.depth < budget

namespace Widen
abbrev same : Widen n m := ⟨.same, 2, by simp [Path.depth]⟩
abbrev inclusion (e : Fin m) : Widen n m := ⟨.inclusion e, 2, by simp [Path.depth]⟩
abbrev trans (z : Fin n) (p q : Widen n m) : Widen n m :=
  ⟨.trans z p.path q.path, 1 + p.budget + q.budget, by
    simp only [Path.depth]; have := p.bound; have := q.bound; omega⟩
end Widen

structure Term (n m : Nat) where
  raw : Syntax n m
  budget : Nat
  bound : raw.depth < budget

namespace Term
abbrev boolean (b : Bool) : Term n m :=
  ⟨.boolean b, 2, by simp [Syntax.depth]⟩

abbrev integer (i : Int) : Term n m :=
  ⟨.integer i, 2, by simp [Syntax.depth]⟩

abbrev this  : Term n m :=
  ⟨.this, 2, by simp [Syntax.depth]⟩

abbrev extent (x : Fin n) : Term n m :=
  ⟨.extent x, 2, by simp [Syntax.depth]⟩

abbrev var (i : Nat) : Term n m :=
  ⟨.var i, 2, by simp [Syntax.depth]⟩

abbrev map (e : Fin m) : Term n m :=
  ⟨.map e, 2, by simp [Syntax.depth]⟩

abbrev and (a b : Term n m) : Term n m :=
  ⟨.and a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev not (a : Term n m) : Term n m :=
  ⟨.not a.raw, 1 + a.budget, by
    simp only [Syntax.depth]; have := a.bound; omega⟩

abbrev equal (t : Ty n) (a b : Term n m) : Term n m :=
  ⟨.equal t a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev less (a b : Term n m) : Term n m :=
  ⟨.less a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev arithmetic (op : Arithmetic) (a b : Term n m) : Term n m :=
  ⟨.arithmetic op a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev integerOf (x : Fin n) (a : Term n m) : Term n m :=
  ⟨.integerOf x a.raw, 1 + a.budget, by
    simp only [Syntax.depth]; have := a.bound; omega⟩

abbrev cardinality (k : Collection n) (a : Term n m) : Term n m :=
  ⟨.cardinality k a.raw, 1 + a.budget, by
    simp only [Syntax.depth]; have := a.bound; omega⟩

abbrev setOp (op : SetOp) (k : Collection n) (a b : Term n m) : Term n m :=
  ⟨.setOp op k a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev subset (k : Collection n) (a b : Term n m) : Term n m :=
  ⟨.subset k a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev image (x y : Fin n) (a b : Term n m) : Term n m :=
  ⟨.image x y a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev join (x y z : Fin n) (a b : Term n m) : Term n m :=
  ⟨.join x y z a.raw b.raw, 1 + a.budget + b.budget, by
    simp only [Syntax.depth]; have := a.bound; have := b.bound; omega⟩

abbrev widenObjects (x y : Fin n) (p : Widen n m) (a : Term n m) : Term n m :=
  ⟨.widenObjects x y p.path a.raw, 1 + p.budget + a.budget, by
    simp only [Syntax.depth]; have := p.bound; have := a.bound; omega⟩

abbrev widenRelation (x y x1 y1 : Fin n) (p q : Widen n m) (a : Term n m) : Term n m :=
  ⟨.widenRelation x y x1 y1 p.path q.path a.raw, 1 + p.budget + q.budget + a.budget, by
    simp only [Syntax.depth]; have := p.bound; have := q.bound; have := a.bound; omega⟩

abbrev all (b : Local n) (d a : Term n m) : Term n m :=
  ⟨.all b d.raw a.raw, 1 + d.budget + a.budget, by
    simp only [Syntax.depth]; have := d.bound; have := a.bound; omega⟩

abbrev located (p : Structural.SourceSpan) (a : Term n m) : Term n m :=
  ⟨.located p a.raw, 1 + a.budget, by
    simp only [Syntax.depth]; have := a.bound; omega⟩

abbrev Typed (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Term n m) : Prop :=
  e.raw.Typed s Γ t
abbrev Observed (s : Support n m) (e : Term n m) : Prop := e.raw.Observed s
noncomputable abbrev extents (e : Term n m) := e.raw.extents
noncomputable abbrev maps (e : Term n m) := e.raw.maps

instance (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Term n m) : Decidable (e.Typed s Γ t) :=
  typedAt s e.budget e.raw e.bound Γ t
instance (s : Support n m) (e : Term n m) : Decidable (e.Observed s) :=
  observedAt s e.budget e.raw e.bound

/-- Every finite syntax has a certificate. Runtime callers use the straight-line
builders above; no metadata or integer magnitude contributes to their budget. -/
noncomputable def certify (e : Syntax n m) : Term n m :=
  ⟨e, e.depth + 1, Nat.lt_succ_self _⟩
end Term

structure Checked (s : Support n m) (Γ : List (Local n)) (t : Ty n) where
  term : Term n m
  typed : term.Typed s Γ t
  observed : term.Observed s

/-!
[impl->req~compiler-expressions~1]
-/
def check (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Term n m) :
    Except Structural.Diagnostic (Checked s Γ t) :=
  if ht : e.Typed s Γ t then
    if ho : e.Observed s then .ok ⟨e, ht, ho⟩
    else .error { category := .unsupported, code := "expr.infinite-primitive-extent" }
  else .error { category := .malformed, code := "expr.type-scope-or-span" }

end ClaferCompiler.IR.Expr
