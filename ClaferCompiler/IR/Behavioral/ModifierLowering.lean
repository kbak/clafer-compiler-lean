module

public import ClaferCompiler.IR.Behavioral.Expression
public import ClaferCompiler.IR.Behavioral.Properties

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.ModifierLowering

/-- Modifier expansion uses the same accepted surface shapes and placements. -/
def modifierInitial (d : Fin k) : Expression.Formula k 0 :=
  .initially (.atom (.primitive (.inhabited (.set (.thisStep (.child d))))))

def modifierView (d : Fin k) : Surface.Modifiers.View k → SetExpr k n
  | .heads _ => .thisStep (.child d)
  | .reference _ => .thisStep (.deref d)
  | .targets _ => .step (.deref d) (.thisStep (.child d))

def modifierStable (view : SetExpr k 0) (later : SetExpr k 1) : Expression.Formula k 0 :=
  .letSet (.set view) (.next (.implies (.atom (.primitive (.inhabited (.set .this))))
    (.atom (.primitive (.equal (.set (.var 0)) (.set later))))))

def modifierExpansions (d : Fin k) : Surface.Modifiers.Modifier →
    List (Surface.Modifiers.Placement k × Expression.Formula k 0)
  | .initial => [(.parents d, modifierInitial d)]
  | .final => [(.all, modifierStable (modifierView d (.heads d)) (modifierView d (.heads d))),
      (.heads d, modifierStable (modifierView d (.reference d)) (modifierView d (.reference d)))]
  | .finalref => [(.heads d, modifierStable (modifierView d (.reference d)) (modifierView d (.reference d)))]
  | .finaltarget => [(.all, modifierStable (modifierView d (.targets d)) (modifierView d (.targets d)))]


abbrev Constraint (k : Nat) := Properties.Constraint k (Expression.Atom k) (Expression.Collection k)
abbrev Request (k : Nat) := Properties.Request k (Expression.Atom k) (Expression.Collection k)

-- [impl->req~compiler-rich-core-explicit~1]
/-- One shared expansion for backend compilation and explicit core export. -/
def obligations (v : BehavioralStructural.Validated k)
    (table : Vector (List Surface.Modifiers.Modifier) k) :
    List (Surface.Modifiers.Placement k × Expression.Formula k 0) :=
  (List.finRange k).flatMap fun d =>
    (Modifiers.effective v table d).flatMap (modifierExpansions d)

/-- Finite attachment owners. Integer owners have empty stable modifier views;
that boundary is discharged by the preservation proof, not assumed by decoding. -/
def owners (v : BehavioralStructural.Validated k) : Surface.Modifiers.Placement k → List (Fin k)
  | .all => (List.finRange k).filter fun d => (v.core.structural.get d).origin != .integer
  | .heads d => [d]
  | .parents d => (v.core.structural.get d).parent.toList

-- [impl->req~compiler-rich-core-explicit~1]
def constraints (v : BehavioralStructural.Validated k)
    (table : Vector (List Surface.Modifiers.Modifier) k) : List (Constraint k) :=
  (obligations v table).flatMap fun item => (owners v item.1).map fun owner =>
    ⟨owner, item.2, (v.core.structural.get owner).source.getD ⟨"", 0, 0⟩⟩

-- [impl->req~compiler-rich-core-explicit~1]
/-- Materialize every effective obligation before erasing declarations. The
ordinary constraints interpret independently of provenance or rich source. -/
def lower (r : Request k) : Request k :=
  ⟨{ r.model with
      modifiers := Vector.replicate k []
      constraints := r.model.constraints ++ constraints r.model.structural r.model.modifiers }, r.command⟩

-- [proof->req~compiler-rich-core-explicit~1]
theorem lower_modifiers (r : Request k) : (lower r).model.modifiers = Vector.replicate k [] := rfl


-- [proof->req~compiler-rich-core-explicit~1]
theorem lower_idempotent (r : Request k) : lower (lower r) = lower r := by
  simp [lower, constraints, obligations, Modifiers.effective]

end ClaferCompiler.IR.Behavioral.ModifierLowering
