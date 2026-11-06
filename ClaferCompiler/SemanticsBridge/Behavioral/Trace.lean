module

public import ClaferCompiler.IR.Behavioral.Trace
public import ClaferCompiler.SemanticsBridge.Behavioral.Syntax

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral
open IR.Behavioral

-- [impl->req~compiler-behavioral-interpretation~1]
def identities (ids : Identities k o) : Clafer.Behavioral.Identities (Fin k) (Fin o) :=
  ⟨ids.root, fun x => ids.directType[x], fun x => ids.parent[x]⟩

def trace (l : Lasso k o steps) : Clafer.Behavioral.Trace (Fin k) (Fin o) where
  identities := identities l.identities
  live t := {x | (l.at t).live[x] = true}
  deref t d x y := (d, x, y) ∈ (l.at t).references

def environment (ρ : Environment o n) : Clafer.Behavioral.Environment (Fin o) n :=
  ⟨ρ.this, fun v => {x | ρ.lookup v x = true}⟩

-- [impl->req~compiler-behavioral-interpretation~1]
/-- One global correspondence. No validity or formula satisfaction premise.
The first slice observes the whole finite nonprimitive pool. -/
structure ObservesTrace (l : Lasso k o steps)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (e : Fin o ≃ U) : Prop where
  root : e l.identities.root = τ.identities.root
  directType : ∀ x, τ.identities.directType (e x) = l.identities.directType[x]
  parent : ∀ x, τ.identities.parent (e x) = (l.identities.parent[x]).map e
  live : ∀ t x, e x ∈ τ.live t ↔ (l.at t).live[x] = true
  deref : ∀ t d x y, τ.deref t d (e x) (e y) ↔ (d, x, y) ∈ (l.at t).references

def FitsTrace (b : ObservationBounds) (l : Lasso k o steps)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (e : Fin o ≃ U) : Prop :=
  ObservesTrace l τ e ∧ fits b l

-- [proof->req~compiler-behavioral-interpretation~1]
theorem observes_self (l : Lasso k o steps) : ObservesTrace l (trace l) (Equiv.refl _) := by
  constructor <;> intros <;> simp [trace, identities]

theorem walkType_eq (m : IR.Structural.Core k) (j : Nat) (d : Fin k) :
    walkType m j d = (Structural.interpret m).next^[j] d := by
  induction j generalizing d with
  | zero => rfl
  | succ j ih =>
    simp only [walkType, Nat.repeat, Function.iterate_succ_apply']
    exact congrArg (nextType m) (ih d)

theorem ancestor_agrees (m : IR.Structural.Core k) (d e : Fin k) :
    ancestor m d e = true ↔ (Structural.interpret m).Ancestor d e := by
  simp only [ancestor, decide_eq_true_eq, walkType_eq,
    Clafer.Semantics.EffectiveCore.ancestor_iff_bounded]

-- [proof->req~compiler-behavioral-ir~1]
theorem identityChecks_valid (m : IR.Structural.Core k) (ids : Identities k o)
    (h : identityChecks m ids) : (identities ids).Valid (Structural.interpret m) := by
  refine ⟨h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  · exact h.2.2.2.1
  · intro x p hp
    obtain ⟨c, hc, ha⟩ := h.2.2.2.2.2.2 x p hp
    exact ⟨c, hc, (ancestor_agrees m _ _).mp ha⟩

theorem checked_root_live (v : CheckedTrace m b o steps) (t : Nat) :
    (trace v.lasso).identities.root ∈ (trace v.lasso).live t :=
  (v.checked.2 (v.lasso.index t)).1

theorem checked_parent_live (v : CheckedTrace m b o steps) (t : Nat) (x p : Fin o)
    (hx : x ∈ (trace v.lasso).live t)
    (hp : (trace v.lasso).identities.parent x = some p) :
    p ∈ (trace v.lasso).live t :=
  (v.checked.2 (v.lasso.index t)).2.1 x p hx hp

/-- Remaining structural clauses are explicit, rather than hidden in trace admission. -/
theorem checked_valid (v : CheckedTrace m b o steps)
    (states : ∀ t, (trace v.lasso).StateValid (Structural.interpret m) t) :
    (trace v.lasso).Valid (Structural.interpret m) :=
  ⟨identityChecks_valid m _ v.checked.1, checked_root_live v, checked_parent_live v, states⟩

theorem checked_fits (v : CheckedTrace m b o steps) :
    FitsTrace b v.lasso (trace v.lasso) (Equiv.refl _) := ⟨observes_self _, v.bounded⟩

-- [proof->req~compiler-behavioral-interpretation~1]
/-- Includes absence/reappearance and replacement; no adjacency assumption. -/
theorem fixed_parent (l : Lasso k o steps) {i j : Nat} {p q x : Fin o}
    (hi : (trace l).ParentAt i p x) (hj : (trace l).ParentAt j q x) : p = q :=
  (trace l).parent_stable hi hj

theorem relation_agrees (m : IR.Structural.Core k) (l : Lasso k o steps)
    (t : Nat) (s : Step k) (x y : Fin o) :
    relation m l.identities (l.at t) s x y = true ↔
    (step s).relation (Structural.interpret m) (trace l) t x y := by
  cases s <;> simp [relation, step, Clafer.Behavioral.Step.relation,
    Clafer.Behavioral.Trace.raw, Clafer.Behavioral.Trace.ParentAt,
    trace, identities, ancestor_agrees, Structural.interpret, and_assoc]

-- [proof->req~compiler-behavioral-interpretation~1]
/-- Concrete adapter proof; it does not assume generic observation agreement. -/
theorem setExprAt_agrees (m : IR.Structural.Core k) (l : Lasso k o steps)
    (t : Nat) (ρ : Environment o n) (a : SetExpr k n) (x : Fin o)
    (fuel : Nat) (enough : sizeOf a < fuel) :
    a.evalAt m l.identities (l.at t) ρ fuel enough x = true ↔
    x ∈ (setExpr a).eval (Structural.interpret m) (trace l) (environment ρ) t := by
  induction fuel generalizing a x with
  | zero => omega
  | succ fuel ih =>
    cases a <;> simp_all [SetExpr.evalAt_succ, SetExpr.evalStep, setExpr, Clafer.Behavioral.SetExpr.eval,
      Bool.eq_false_iff, environment, head, trace, identities, Clafer.Behavioral.Trace.raw,
      ancestor_agrees, image, Clafer.Behavioral.Step.image, relation_agrees]

theorem setExpr_agrees (m : IR.Structural.Core k) (l : Lasso k o steps)
    (t : Nat) (ρ : Environment o n) (a : SetExpr k n) (x : Fin o)
    (fuel : Nat) (enough : sizeOf a < fuel) :
    a.eval m l.identities (l.at t) ρ fuel enough x = true ↔
    x ∈ (setExpr a).eval (Structural.interpret m) (trace l) (environment ρ) t :=
  setExprAt_agrees m l t ρ a x fuel enough

theorem atom_agrees (m : IR.Structural.Core k) (l : Lasso k o steps)
    (t : Nat) (ρ : Environment o n) (a : Atom k n) (fuel : Nat) (enough : sizeOf a < fuel) :
    a.eval m l.identities (l.at t) ρ fuel enough = true ↔
    (atom a).eval (Structural.interpret m) (trace l) (environment ρ) t := by
  cases a with
  | inhabited a => simp [Atom.eval, atom, Clafer.Behavioral.SetAtom.eval, Set.Nonempty, setExpr_agrees]
  | subset a b => simp [Atom.eval, atom, Clafer.Behavioral.SetAtom.eval, Set.subset_def, setExpr_agrees]
  | equal a b =>
    have ha : sizeOf a < fuel := by simp_all; omega
    have hb : sizeOf b < fuel := by simp_all; omega
    simp only [Atom.eval, decide_eq_true_eq, atom, Clafer.Behavioral.SetAtom.eval, Set.ext_iff]
    exact forall_congr' fun x => by
      rw [← setExpr_agrees m l t ρ a x fuel ha, ← setExpr_agrees m l t ρ b x fuel hb]
      cases a.eval m l.identities (l.at t) ρ fuel ha x <;>
        cases b.eval m l.identities (l.at t) ρ fuel hb x <;> decide

theorem environment_push (ρ : Environment o n) (s : ObjectSet o) :
    environment (ρ.push s) = (environment ρ).push {x | s x = true} := by
  unfold environment Environment.push Clafer.Behavioral.Environment.push
  congr 1
  funext v
  refine Fin.cases ?_ (fun _ => ?_) v <;> rfl

end ClaferCompiler.SemanticsBridge.Behavioral
