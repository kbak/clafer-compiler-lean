module

public import ClaferCompiler.Correctness.Behavioral.Full.RangesValues
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsSets

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Ranges
open IR.Behavioral
open Expression.Ranges
open SemanticsBridge.Behavioral (setExpr step)

/-- Uniform structural budgets at every state. Only finite, admitted primitive
observations have bounds; the full mathematical integer extent is excluded. -/
structure InputsBound (v : IR.BehavioralStructural.Validated k)
    (b : Inputs k) (σ : Clafer.Behavioral.Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) : Prop where
  root : CollectionBound R b.root {σ.identities.root}
  extents : ∀ d, b.extentAllowed[d] = true → ∀ t,
    CollectionBound R b.extents[d] ((σ.raw (Sets.model v) t).head d)
  steps : ∀ st, b.stepAllowed st = true → ∀ t S,
    CollectionBound R (b.steps st) ((step st).image (Sets.model v) σ t S)

structure EnvironmentBound (b : Inputs k) (Γ : Context n)
    (R : Clafer.Constraints.IntegerRealization U) (ρ : Clafer.Behavioral.Environment U n) : Prop where
  this : CollectionBound R b.context {ρ.this}
  lookup : ∀ i, CollectionBound R Γ[i] (ρ.lookup i)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem set_bound (hb : InputsBound v b σ R) (hρ : EnvironmentBound b Γ R ρ)
    (h : SetBound b Γ a r) (t : Nat) :
    CollectionBound R r ((setExpr a).eval (Sets.model v) σ ρ t) := by
  induction h with
  | empty => exact CollectionBound.empty
  | this => exact hρ.this.subset (fun _ hx => hx.1)
  | root => exact hb.root
  | var => exact hρ.lookup _
  | extent allowed _ => exact hb.extents _ allowed t
  | union _ _ iha ihb => exact iha.union ihb
  | inter _ _ iha ihb => exact iha.inter ihb
  | diff _ _ iha _ => exact iha.diff
  | step _ allowed _ _ => exact hb.steps _ allowed t _
  | thisStep allowed _ => exact hb.steps _ allowed t _

end ClaferCompiler.Correctness.Behavioral.Full.Ranges
