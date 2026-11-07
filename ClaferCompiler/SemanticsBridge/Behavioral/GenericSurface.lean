module

public import ClaferCompiler.SemanticsBridge.Behavioral.Formula
public import ClaferCompiler.SemanticsBridge.Behavioral.Surface

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.GenericSurface
open IR.Behavioral IR.Behavioral.Surface
variable {A D A' D' : Nat → Type}
variable (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)

namespace Patterns

def pattern : Patterns.Pattern (FormulaF A D n) →
    Clafer.Behavioral.Patterns.Pattern (Clafer.Behavioral.Formula A' D' n)
  | .never p => .never (Generic.interpret am dm p) | .sometime p => .sometime (Generic.interpret am dm p)
  | .lonce p => .lonce (Generic.interpret am dm p) | .always p => .always (Generic.interpret am dm p)
  | .precede s p => .precede (Generic.interpret am dm s) (Generic.interpret am dm p)
  | .follow s p => .follow (Generic.interpret am dm s) (Generic.interpret am dm p)

def scope : Patterns.Scope (FormulaF A D n) →
    Clafer.Behavioral.Patterns.Scope (Clafer.Behavioral.Formula A' D' n)
  | .suffix => .suffix | .before r => .before (Generic.interpret am dm r) | .after q => .after (Generic.interpret am dm q)
  | .between q r => .between (Generic.interpret am dm q) (Generic.interpret am dm r)
  | .afterUntil q r => .afterUntil (Generic.interpret am dm q) (Generic.interpret am dm r)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Every cell has exact syntax agreement, including the two accepted corrections. -/
theorem expand_interpret (p : Patterns.Pattern (FormulaF A D n)) (s : Patterns.Scope (FormulaF A D n)) :
    Generic.interpret am dm (Patterns.expand p s) = Clafer.Behavioral.Patterns.expand (pattern am dm p) (scope am dm s) := by
  cases p <;> cases s <;> rfl

theorem expand_agrees (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.Observation A' D' U)
    (p : Patterns.Pattern (FormulaF A D n)) (s : Patterns.Scope (FormulaF A D n)) (ρ) (sign) (t) :
    (Generic.interpret am dm (Patterns.expand p s)).denote τ O sign ρ t ↔
      Clafer.Behavioral.Patterns.meaning (τ.ParentPresent ρ.this)
        ((pattern am dm p).map (fun a sign => a.denote τ O sign ρ))
        ((scope am dm s).map (fun a sign => a.denote τ O sign ρ)) sign t := by
  rw [expand_interpret]
  exact Clafer.Behavioral.Patterns.expand_agrees τ O _ _ ρ sign t

end Patterns

namespace Transitions

def arrow : Transitions.Arrow → Clafer.Behavioral.Transitions.Arrow
  | .immediate => .immediate | .eventual => .eventual

def chain (c : Transitions.ChainF A D n) :
    Clafer.Behavioral.Transitions.Chain A' D' n :=
  c.links.foldr (fun l rest => .link (Generic.interpret am dm l.source) (l.guard.map (Generic.interpret am dm)) (arrow l.arrow) rest)
    (.stop (Generic.interpret am dm c.target))

theorem precondition_interpret (l : Transitions.LinkF A D n) :
    Generic.interpret am dm (Transitions.precondition l) =
      Clafer.Behavioral.Transitions.precondition (Generic.interpret am dm l.source) (l.guard.map (Generic.interpret am dm)) := by
  cases l with
  | mk source guard arrow => cases guard <;> rfl

theorem step_interpret (context : FormulaF A D n) (l : Transitions.LinkF A D n) (target : FormulaF A D n) :
    Generic.interpret am dm (Transitions.step context l target) =
      Clafer.Behavioral.Transitions.step (Generic.interpret am dm context) (Generic.interpret am dm l.source) (Generic.interpret am dm target) (arrow l.arrow) := by
  cases l with
  | mk source guard arrow => cases arrow <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem sequence_interpret (context : FormulaF A D n) (c : Transitions.ChainF A D n) :
    Generic.interpret am dm (Transitions.sequence context c) = (chain am dm c).sequence (Generic.interpret am dm context) := by
  rcases c with ⟨links, target⟩
  induction links with
  | nil => simp [Transitions.sequence, chain]
  | cons link rest ih =>
    simp only [Transitions.sequence, chain, List.foldr_cons,
      Clafer.Behavioral.Transitions.Chain.sequence_link, Generic.interpret]
    rw [precondition_interpret, step_interpret]
    exact congrArg (fun x => Clafer.Behavioral.Formula.and
      (Clafer.Behavioral.Transitions.precondition (Generic.interpret am dm link.source) (link.guard.map (Generic.interpret am dm)))
      (Clafer.Behavioral.Transitions.step (Generic.interpret am dm context) (Generic.interpret am dm link.source) x (arrow link.arrow))) ih

theorem expand_interpret (context : FormulaF A D n) (c : Transitions.ChainF A D n) :
    Generic.interpret am dm (Transitions.expand context c) = (chain am dm c).expand (Generic.interpret am dm context) := by
  rcases c with ⟨links, target⟩
  cases links with
  | nil => rfl
  | cons link rest =>
    change Clafer.Behavioral.Formula.implies (Generic.interpret am dm (Transitions.precondition link))
      (Generic.interpret am dm (Transitions.step context link (Transitions.sequence context ⟨rest, target⟩))) = _
    rw [precondition_interpret, step_interpret, sequence_interpret]
    rfl

theorem expand_agrees (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.Observation A' D' U)
    (context : FormulaF A D n) (c : Transitions.ChainF A D n) (ρ) (sign) (t) :
    (Generic.interpret am dm (Transitions.expand context c)).denote τ O sign ρ t ↔
      (chain am dm c).meaning τ O (Generic.interpret am dm context) ρ sign t := by
  rw [expand_interpret]
  exact Clafer.Behavioral.Transitions.Chain.expand_agrees τ O _ _ ρ sign t

end Transitions

end ClaferCompiler.SemanticsBridge.Behavioral.GenericSurface
