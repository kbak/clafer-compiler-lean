module

public import ClaferCompiler.IR.Behavioral.Properties
public import ClaferCompiler.SemanticsBridge.Behavioral.Formula
public import ClaferCompiler.SemanticsBridge.Behavioral.Modifiers
public import Clafer.Behavioral.Properties

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Properties
open IR.Behavioral.Properties
variable {A D A' D' : Nat → Type}
variable (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)

def constraint {U : Type u} (m : IR.BehavioralStructural.Core k) (c : Constraint k A D) :
    Clafer.Behavioral.Properties.Constraint (Fin k) A' D' U :=
  if c.owner = m.structural.root then
    .root (Generic.interpret am dm c.body)
  else .nested (BehavioralStructural.interpret m) c.owner (Generic.interpret am dm c.body)

def constraints {U : Type u} (m : IR.BehavioralStructural.Core k) (cs : List (Constraint k A D)) :
    Set (Clafer.Behavioral.Properties.Constraint (Fin k) A' D' U) :=
  {c | c ∈ cs.map (constraint am dm m)}

-- [impl->req~compiler-behavioral-elaboration~1]
def model {U : Type u} (m : Model k A D)
    (O : Clafer.Behavioral.Trace (Fin k) U → Clafer.Behavioral.PartialObservation A' D' U) :=
  Clafer.Behavioral.Properties.Model.behavioral (BehavioralStructural.interpret m.structural.core)
    (Modifiers.declared m.modifiers) O (constraints am dm m.structural.core m.constraints)

/-- Universal assertions and existential scenario requests use distinct upstream
judgments. Counterexample search negates the entire interpreted property. -/
def request {U : Type u} (r : Request k A D)
    (O : Clafer.Behavioral.Trace (Fin k) U → Clafer.Behavioral.PartialObservation A' D' U) : Prop :=
  match r.command with
  | .check i => (model am dm r.model O).Asserts
      (constraint am dm r.model.structural.core r.model.assertions[i])
  | .run additional => (model am dm r.model O).Possible
      (constraints am dm r.model.structural.core additional)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem scenario_interpret {U : Type u} (m : Model k A D) (cs : List (Constraint k A D))
    (O : Clafer.Behavioral.Trace (Fin k) U → Clafer.Behavioral.PartialObservation A' D' U) :
    model am dm (m.withScenario cs) O =
      (model am dm m O).withScenario (constraints am dm m.structural.core cs) := by
  unfold model Model.withScenario Clafer.Behavioral.Properties.Model.withScenario
    Clafer.Behavioral.Properties.Model.behavioral
  congr 1
  ext c
  simp only [constraints, Set.mem_ofPred_eq, List.map_append, List.mem_append, Set.mem_union]

theorem scenario_possible {U : Type u} (m : Model k A D) (cs : List (Constraint k A D))
    (O : Clafer.Behavioral.Trace (Fin k) U → Clafer.Behavioral.PartialObservation A' D' U) :
    (model am dm m O).Possible (constraints am dm m.structural.core cs) ↔
      ∃ τ, (model am dm (m.withScenario cs) O).Satisfies τ := by
  rw [scenario_interpret]
  exact Clafer.Behavioral.Properties.Model.possible_iff _ _

theorem assertion_failure {U : Type u} (m : Model k A D) (a : Constraint k A D)
    (O : Clafer.Behavioral.Trace (Fin k) U → Clafer.Behavioral.PartialObservation A' D' U) :
    (∃ τ, (model am dm m O).Counterexample (constraint am dm m.structural.core a) τ) ↔
      ¬ (model am dm m O).Asserts (constraint am dm m.structural.core a) :=
  Clafer.Behavioral.Properties.Model.counterexample_iff _ _

end ClaferCompiler.SemanticsBridge.Behavioral.Properties
