module

public import ClaferCompiler.IR.Behavioral.Admission
public import ClaferCompiler.SemanticsBridge.Structural
public import Clafer.Behavioral.Lowering

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral
open IR.Behavioral
namespace Source
abbrev Step := Clafer.Behavioral.Step
abbrev SetExpr := Clafer.Behavioral.SetExpr
abbrev SetAtom := Clafer.Behavioral.SetAtom
abbrev Formula := Clafer.Behavioral.Formula
end Source

def step : Step k → Source.Step (Fin k)
  | .parent => .parent
  | .child d => .child d
  | .deref d => .deref d

-- [impl->req~compiler-behavioral-interpretation~1]
noncomputable def setExpr : SetExpr k n → Source.SetExpr (Fin k) n
  | .empty => .empty | .this => .this | .root => .root
  | .var v => .var v | .extent d => .extent d
  | .union a b => .union (setExpr a) (setExpr b)
  | .inter a b => .inter (setExpr a) (setExpr b)
  | .diff a b => .diff (setExpr a) (setExpr b)
  | .step s a => .step (step s) (setExpr a)
  | .thisStep s => .thisStep (step s)

def atom : Atom k n → Source.SetAtom (Fin k) n
  | .inhabited a => .inhabited (setExpr a)
  | .equal a b => .equal (setExpr a) (setExpr b)
  | .subset a b => .subset (setExpr a) (setExpr b)

def quantifier : Quantifier → Clafer.Behavioral.Quantifier
  | .all => .all | .some => .some | .no => .no | .one => .one | .lone => .lone

-- [impl->req~compiler-behavioral-interpretation~1]
noncomputable def formula : Formula k n → Source.Formula (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) n
  | .truth => .truth | .atom a => .atom (atom a)
  | .not a => .not (formula a)
  | .and a b => .and (formula a) (formula b)
  | .or a b => .or (formula a) (formula b)
  | .implies a b => .implies (formula a) (formula b)
  | .iff a b => .iff (formula a) (formula b)
  | .xor a b => .xor (formula a) (formula b)
  | .ite c a b => .ite (formula c) (formula a) (formula b)
  | .next a => .next (formula a)
  | .eventually a => .eventually (formula a)
  | .always a => .always (formula a)
  | .strongUntil a b => .strongUntil (formula a) (formula b)
  | .weakUntil a b => .weakUntil (formula a) (formula b)
  | .initially a => .initially (formula a)
  | .finally a => .finally (formula a)
  | .quant q d a => .quant (quantifier q) (setExpr d) (formula a)
  | .letSet d a => .letSet (setExpr d) (formula a)

-- [proof->req~compiler-behavioral-interpretation~1]
/-- Exact constructor translation, for every tree, binder depth and source sign. -/
theorem normalizeAt_interpret (a : Formula k n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) :
    formula (Formula.normalizeAt fuel a enough s) = (formula a).normalize s := by
  induction a generalizing fuel s with
  | quant q d a ih =>
    cases fuel with
    | zero => omega
    | succ fuel => cases q <;> cases s <;>
      simp [Formula.normalizeAt_succ, Formula.normalizeStep, FormulaF.normalizeStep, formula, quantifier, Clafer.Behavioral.Formula.normalize, ih]
  | _ => cases fuel with
    | zero => omega
    | succ fuel => cases s <;>
      simp_all [Formula.normalizeAt_succ, Formula.normalizeStep, FormulaF.normalizeStep, formula, Clafer.Behavioral.Formula.normalize]

theorem normalize_interpret (a : Formula k n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) :
    formula (a.normalize s fuel enough) = (formula a).normalize s :=
  normalizeAt_interpret a s fuel enough

theorem normalize_normal (a : Formula k n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) : (formula (a.normalize s fuel enough)).Normal := by
  rw [normalize_interpret]
  exact Clafer.Behavioral.Formula.normalize_normal _ _

theorem normalize_agrees (m : Clafer.Semantics.EffectiveCore k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (a : Formula k n) (s : Bool)
    (ρ : Clafer.Behavioral.Environment U n) (t fuel : Nat) (enough : sizeOf a < fuel) :
    (formula (a.normalize s fuel enough)).raw τ (.sets m τ) ρ t ↔
      (formula a).denote τ (.sets m τ) s ρ t := by
  rw [normalize_interpret]
  exact Clafer.Behavioral.Formula.normalize_agrees _ _ _ _ _ _

theorem normalize_lower_agrees (m : Clafer.Semantics.EffectiveCore k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (a : Formula k n) (s : Bool)
    (ρ : Clafer.Behavioral.Environment U n) (t fuel : Nat) (enough : sizeOf a < fuel) :
    (formula (a.normalize s fuel enough)).lower.eval τ (.sets m τ) ρ t ↔
      (formula a).denote τ (.sets m τ) s ρ t := by
  rw [normalize_interpret]
  exact Clafer.Behavioral.Formula.normalize_lower_agrees _ _ _ _ _ _

-- [proof->req~compiler-behavioral-ir~1]
theorem admitted_domain (v : Admitted k) :
    (Structural.interpret v.document.core).WellFormed ∧
    (Structural.interpret v.document.core).Supported :=
  Structural.validated_domain v.structural

theorem admit_preserves (d : Document k) (v : Admitted k)
    (h : admitBehavioral d = .ok v) : v.document = d := by
  unfold admitBehavioral at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rfl

theorem admit_success_iff (d : Document k) :
    (∃ v, admitBehavioral d = .ok v) ↔
    d.version = "clafer-behavioral-ir/1" ∧ d.profile = "behavioral-core/1" ∧
    IR.Structural.coreChecks d.core d.certificate ∧
    IR.Structural.supportChecks d.core d.certificate ∧ metadataChecks d ∧ supportedBodies d := by
  unfold admitBehavioral
  split_ifs <;> simp_all

end ClaferCompiler.SemanticsBridge.Behavioral
