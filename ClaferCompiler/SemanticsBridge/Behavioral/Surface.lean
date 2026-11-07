module

public import ClaferCompiler.IR.Behavioral.Surface
public import ClaferCompiler.SemanticsBridge.Behavioral.Syntax
public import Clafer.Behavioral.Patterns
public import Clafer.Behavioral.Transitions
public import Clafer.Behavioral.Modifiers

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Surface
open IR.Behavioral
open IR.Behavioral.Surface
namespace S
abbrev Patterns := Clafer.Behavioral.Patterns.Pattern
abbrev Scope := Clafer.Behavioral.Patterns.Scope
end S

namespace Patterns

def pattern : Patterns.Pattern (Formula k n) →
    S.Patterns (Source.Formula (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) n)
  | .never p => .never (formula p) | .sometime p => .sometime (formula p)
  | .lonce p => .lonce (formula p) | .always p => .always (formula p)
  | .precede s p => .precede (formula s) (formula p)
  | .follow s p => .follow (formula s) (formula p)

def scope : Patterns.Scope (Formula k n) →
    S.Scope (Source.Formula (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) n)
  | .suffix => .suffix | .before r => .before (formula r) | .after q => .after (formula q)
  | .between q r => .between (formula q) (formula r)
  | .afterUntil q r => .afterUntil (formula q) (formula r)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Every cell has exact syntax agreement, including the two accepted corrections. -/
theorem expand_interpret (p : Patterns.Pattern (Formula k n)) (s : Patterns.Scope (Formula k n)) :
    formula (Patterns.expand p s) = Clafer.Behavioral.Patterns.expand (pattern p) (scope s) := by
  cases p <;> cases s <;> rfl

theorem expand_agrees (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.Observation (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) U)
    (p : Patterns.Pattern (Formula k n)) (s : Patterns.Scope (Formula k n)) (ρ) (sign) (t) :
    (formula (Patterns.expand p s)).denote τ O sign ρ t ↔
      Clafer.Behavioral.Patterns.meaning (τ.ParentPresent ρ.this)
        ((pattern p).map (fun a sign => a.denote τ O sign ρ))
        ((scope s).map (fun a sign => a.denote τ O sign ρ)) sign t := by
  rw [expand_interpret]
  exact Clafer.Behavioral.Patterns.expand_agrees τ O _ _ ρ sign t

/-- Normalization remains executable; source truth is the independent interval rule. -/
theorem normalized_agrees (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.Observation (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) U)
    (p : Patterns.Pattern (Formula k n)) (s : Patterns.Scope (Formula k n)) (ρ) (sign) (t fuel)
    (enough : sizeOf (Patterns.expand p s) < fuel) :
    (formula (Formula.normalize (Patterns.expand p s) sign fuel enough)).raw τ O ρ t ↔
      Clafer.Behavioral.Patterns.meaning (τ.ParentPresent ρ.this)
        ((pattern p).map (fun a sign => a.denote τ O sign ρ))
        ((scope s).map (fun a sign => a.denote τ O sign ρ)) sign t := by
  rw [normalize_interpret, Clafer.Behavioral.Formula.normalize_agrees]
  exact expand_agrees τ O p s ρ sign t
end Patterns

namespace Transitions

def arrow : Transitions.Arrow → Clafer.Behavioral.Transitions.Arrow
  | .immediate => .immediate | .eventual => .eventual

def chain (c : Transitions.Chain k n) :
    Clafer.Behavioral.Transitions.Chain (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) n :=
  c.links.foldr (fun l rest => .link (formula l.source) (l.guard.map formula) (arrow l.arrow) rest)
    (.stop (formula c.target))

theorem precondition_interpret (l : Transitions.Link k n) :
    formula (Transitions.precondition l) =
      Clafer.Behavioral.Transitions.precondition (formula l.source) (l.guard.map formula) := by
  cases l with
  | mk source guard arrow => cases guard <;> rfl

theorem step_interpret (context : Formula k n) (l : Transitions.Link k n) (target : Formula k n) :
    formula (Transitions.step context l target) =
      Clafer.Behavioral.Transitions.step (formula context) (formula l.source) (formula target) (arrow l.arrow) := by
  cases l with
  | mk source guard arrow => cases arrow <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem sequence_interpret (context : Formula k n) (c : Transitions.Chain k n) :
    formula (Transitions.sequence context c) = (chain c).sequence (formula context) := by
  rcases c with ⟨links, target⟩
  induction links with
  | nil => simp [Transitions.sequence, chain]
  | cons link rest ih =>
    simp only [Transitions.sequence, chain, List.foldr_cons,
      Clafer.Behavioral.Transitions.Chain.sequence_link, formula]
    rw [precondition_interpret, step_interpret]
    exact congrArg (fun x => Clafer.Behavioral.Formula.and
      (Clafer.Behavioral.Transitions.precondition (formula link.source) (link.guard.map formula))
      (Clafer.Behavioral.Transitions.step (formula context) (formula link.source) x (arrow link.arrow))) ih

theorem expand_interpret (context : Formula k n) (c : Transitions.Chain k n) :
    formula (Transitions.expand context c) = (chain c).expand (formula context) := by
  rcases c with ⟨links, target⟩
  cases links with
  | nil => rfl
  | cons link rest =>
    change Clafer.Behavioral.Formula.implies (formula (Transitions.precondition link))
      (formula (Transitions.step context link (Transitions.sequence context ⟨rest, target⟩))) = _
    rw [precondition_interpret, step_interpret, sequence_interpret]
    rfl

theorem expand_agrees (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.Observation (Source.SetAtom (Fin k)) (Source.SetExpr (Fin k)) U)
    (context : Formula k n) (c : Transitions.Chain k n) (ρ) (sign) (t) :
    (formula (Transitions.expand context c)).denote τ O sign ρ t ↔
      (chain c).meaning τ O (formula context) ρ sign t := by
  rw [expand_interpret]
  exact Clafer.Behavioral.Transitions.Chain.expand_agrees τ O _ _ ρ sign t

theorem declaration_interpret (guard : Option (Formula k n)) (a : Transitions.Arrow)
    (rest : Transitions.Chain k n) :
    formula (Transitions.declaration guard a rest) =
      Clafer.Behavioral.Transitions.declaration (guard.map formula) (arrow a) (chain rest) := by
  rw [Transitions.declaration, expand_interpret]
  rfl
end Transitions

namespace Modifiers

def modifier : Modifiers.Modifier → Clafer.Behavioral.Modifiers.Modifier
  | .initial => .initial | .final => .final | .finalref => .finalref | .finaltarget => .finaltarget

def view : Modifiers.View k → Clafer.Behavioral.Modifiers.View (Fin k)
  | .heads d => .heads d | .reference d => .reference d | .targets d => .targets d

def placement : Modifiers.Placement k → Clafer.Behavioral.Modifiers.Placement (Fin k)
  | .all => .all | .parents d => .parents d | .heads d => .heads d

theorem view_interpret (v : Modifiers.View k) :
    setExpr (v.expression : SetExpr k n) = (view v).expression := by cases v <;> rfl

theorem stability_interpret (v : Modifiers.View k) :
    formula (Modifiers.stabilityExpansion v) = Clafer.Behavioral.Modifiers.stabilityExpansion (view v) := by
  cases v <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem expand_interpret (d : Fin k) (m : Modifiers.Modifier) :
    (Modifiers.expand d m).map (fun item => (placement item.1, formula item.2)) =
      Clafer.Behavioral.Modifiers.expand d (modifier m) := by
  cases m <;> rfl

/-- Existing inherited-reference meaning supplies the full modifier conclusion.
No equality across a lifetime gap or recursive descendant finality is added. -/
theorem expand_agrees (m : Clafer.Behavioral.Structural.Core k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (valid : Clafer.Behavioral.Structural.Valid m τ)
    (d : Fin k) (mod : Modifiers.Modifier) :
    (∀ item ∈ Modifiers.expand d mod, (formula item.2).Attached τ
      (.sets m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ))
      ((placement item.1).contexts m τ)) ↔
      Clafer.Behavioral.Modifiers.meaning m τ d (modifier mod) := by
  have h := Clafer.Behavioral.Modifiers.expand_agrees m τ valid d (modifier mod)
  rw [← expand_interpret] at h
  simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using h
end Modifiers
end ClaferCompiler.SemanticsBridge.Behavioral.Surface
