module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
variable {U : Type}

-- [proof->req~compiler-behavioral-correctness~1]
/-- Primitive row observations, discharged by the concrete trace representation.
This contains no formula truth, set-expression or atom agreement premise. -/
structure PrimitiveAgreement (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat) : Prop where
  injective : Function.Injective f
  root : ∀ e t, Relations.Unary f {σ.identities.root} ((root v).eval (schema v) w τ e t)
  live : ∀ e t, Relations.Unary f (σ.live t) ((live v).eval (schema v) w τ e t)
  head : ∀ d e t, Relations.Unary f ((σ.raw (SemanticsBridge.Structural.interpret v.core) t).head d)
    ((head v d).eval (schema v) w τ e t)
  step : ∀ st e t, Relations.Binary f ((SemanticsBridge.Behavioral.step st).relation
    (SemanticsBridge.Structural.interpret v.core) σ t) ((step v st).eval (schema v) w τ e t)

/-- A frozen relation denotes the same source set at every time. -/
def Frozen (v : IR.Structural.Layout k) (w : Nat) (τ : Trace) (f : U → Nat)
    (e : Environment) (r : Rel) (S : Set U) : Prop :=
  r.Term ∧ ∀ t, Relations.Unary f S (r.eval (schema v) w τ e t)

structure ContextRep (v : IR.Structural.Layout k) (w : Nat) (τ : Trace) (f : U → Nat)
    (c : Context n) (ρ : Clafer.Behavioral.Environment U n) (e : Environment) : Prop where
  this : Frozen v w τ f e c.this {ρ.this}
  lookup : ∀ i, Frozen v w τ f e (c.lookup i) (ρ.lookup i)
  aliases : ∀ r ∈ c.aliases, ∃ x, Frozen v w τ f e r {x}
  covers : ∀ x, ∃ r ∈ c.aliases, Frozen v w τ f e r {x}

 theorem root_term (v : IR.Structural.Layout k) : (root v).Term := .sig _
theorem live_term (v : IR.Structural.Layout k) : (live v).Term := .join (.sig _) (.field _)
theorem head_term (v : IR.Structural.Layout k) (d : Fin k) : (head v d).Term :=
  .inter (.sig _) (live_term v)
theorem step_term (v : IR.Structural.Layout k) (st : IR.Behavioral.Step k) : (step v st).Term := by
  cases st with
  | parent => exact .inter (.field _) (.product (.sig _) (live_term v))
  | child d =>
    simp only [step]
    unfold contains
    split
    · exact .empty _
    · exact .inter (.transpose (.field _)) (.product (live_term v) (head_term v d))
  | deref d => exact .inter (.field _) (.product (live_term v) (live_term v))

 theorem setAt_term (v : IR.Structural.Layout k) (c : Context n)
    (hc : c.this.Term) (hl : ∀ i, (c.lookup i).Term)
    (fuel : Nat) (a : IR.Behavioral.SetExpr k n) (h : sizeOf a < fuel) :
    (setAt v c fuel a h).Term := by
  induction fuel generalizing a with
  | zero => omega
  | succ fuel ih =>
    cases a <;> simp only [setAt, setStep]
    · exact .empty _
    · exact .inter hc (live_term v)
    · exact root_term v
    · exact hl _
    · exact head_term v _
    · exact .union (ih _ _) (ih _ _)
    · exact .inter (ih _ _) (ih _ _)
    · exact .diff (ih _ _) (ih _ _)
    · exact .join (ih _ _) (step_term v _)
    · exact .join hc (step_term v _)

-- [proof->req~compiler-behavioral-correctness~1]
theorem setAt_meaning (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat)
    (hp : PrimitiveAgreement v w σ τ f) (c : Context n) (ρ : Clafer.Behavioral.Environment U n)
    (e : Environment) (hc : ContextRep v w τ f c ρ e) (t fuel : Nat)
    (a : IR.Behavioral.SetExpr k n) (h : sizeOf a < fuel) :
    Relations.Unary f ((SemanticsBridge.Behavioral.setExpr a).eval (SemanticsBridge.Structural.interpret v.core) σ ρ t)
      ((setAt v c fuel a h).eval (schema v) w τ e t) := by
  induction fuel generalizing a with
  | zero => omega
  | succ fuel ih =>
    have hs (b : IR.Behavioral.SetExpr k n) (hb : sizeOf b < fuel) :=
      setAt_term v c hc.this.1 (fun i => (hc.lookup i).1) fuel b hb
    cases a <;> simp only [setAt, setStep, SemanticsBridge.Behavioral.setExpr, Clafer.Behavioral.SetExpr.eval]
    · exact Relations.unary_empty
    · exact Relations.unary_inter hp.injective hc.this.1 (live_term v) (hc.this.2 t) (hp.live e t)
    · exact hp.root e t
    · exact (hc.lookup _).2 t
    · exact hp.head _ e t
    · exact Relations.unary_union (hs _ _) (hs _ _) (ih _ _) (ih _ _)
    · exact Relations.unary_inter hp.injective (hs _ _) (hs _ _) (ih _ _) (ih _ _)
    · exact Relations.unary_diff hp.injective (hs _ _) (hs _ _) (ih _ _) (ih _ _)
    · exact Relations.unary_image hp.injective (hs _ _) (step_term v _) (ih _ _) (hp.step _ e t)
    · exact Relations.unary_image hp.injective hc.this.1 (step_term v _) (hc.this.2 t) (hp.step _ e t)

theorem atom_built (v : IR.Structural.Layout k) (c : Context n)
    (a : IR.Behavioral.Atom k n) (fuel : Nat) (h : sizeOf a < fuel) :
    (atom v c a fuel h).Built := by
  cases a with
  | inhabited a => exact .mult _ _
  | equal a b => exact .equal _ _
  | subset a b => exact .subset _ _

theorem atom_meaning (v : IR.Structural.Layout k) (w : Nat)
    (σ : Clafer.Behavioral.Trace (Fin k) U) (τ : Trace) (f : U → Nat)
    (hp : PrimitiveAgreement v w σ τ f) (c : Context n) (ρ : Clafer.Behavioral.Environment U n)
    (e : Environment) (hc : ContextRep v w τ f c ρ e) (t fuel : Nat)
    (a : IR.Behavioral.Atom k n) (h : sizeOf a < fuel) :
    (atom v c a fuel h).Holds (schema v) w τ e t ↔
      (SemanticsBridge.Behavioral.atom a).eval (SemanticsBridge.Structural.interpret v.core) σ ρ t := by
  have hs (b : IR.Behavioral.SetExpr k n) (hb : sizeOf b < fuel) :=
    setAt_meaning v w σ τ f hp c ρ e hc t fuel b hb
  cases a with
  | inhabited a => exact Relations.unary_some (hs _ _)
  | equal a b => exact Relations.unary_equal hp.injective (hs _ _) (hs _ _)
  | subset a b => exact Relations.unary_subset hp.injective (hs _ _) (hs _ _)

 theorem ContextRep.push (hc : ContextRep v w τ f c ρ e) (hr : Frozen v w τ f e r S) :
    ContextRep v w τ f (c.push r) (ρ.push S) e := by
  refine ⟨hc.this, ?_, hc.aliases, hc.covers⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hr
  · exact hc.lookup j

theorem Frozen.shift (hr : Frozen v w τ f e r S) (pre : Environment) :
    Frozen v w τ f (pre ++ e) (shift pre.length r) S := by
  refine ⟨shift_term hr.1 _, ?_⟩
  intro t
  rw [shift_eval hr.1]
  exact hr.2 t

theorem ContextRep.shift (hc : ContextRep v w τ f c ρ e) (pre : Environment) :
    ContextRep v w τ f (c.shift pre.length) ρ (pre ++ e) := by
  refine ⟨hc.this.shift pre, fun i => (hc.lookup i).shift pre, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨x, hx⟩ := hc.aliases a ha
    exact ⟨x, hx.shift pre⟩
  · intro x
    obtain ⟨a, ha, hx⟩ := hc.covers x
    exact ⟨Backend.Alloy.Behavioral.shift pre.length a, List.mem_map.mpr ⟨a, ha, rfl⟩, hx.shift pre⟩

end ClaferCompiler.Correctness.Behavioral
