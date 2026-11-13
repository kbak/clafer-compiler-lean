module

public import ClaferCompiler.SemanticsBridge.Behavioral.InitializerBounds
public import ClaferCompiler.SemanticsBridge.Behavioral.InitializerClassification
public import ClaferCompiler.Frontend.Behavioral.Elaborate
public import Clafer.Behavioral.InitializerCompatibility
public import Clafer.Behavioral.InitializerFinality

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Initializers
open IR.Behavioral
open Clafer.Behavioral (Trace Environment)
namespace Accepted
abbrev Transport := Clafer.Behavioral.Initializers.Transport.Frame
end Accepted

def productionClock : Option Frontend.Behavioral.Initializers.Clock → Clafer.Behavioral.Initializers.Clock
  | none => .everyLive
  | some .instanceBirth => .instanceBirth
  | some .parentBirth => .parentBirth
  | some .globalZero => .globalZero

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The executable classification and its provenance certificate construct the
accepted production obligation, with the actual resolved RHS retained. -/
theorem classifies_production {source : Frontend.Behavioral.Document}
    (b : Frontend.Behavioral.BoundDeclarations source)
    (p : Frontend.Behavioral.BoundHeaderProperty b.resolved.candidate.core)
    (header : Frontend.Behavioral.Header) (op : Frontend.Token)
    (a : Expression.Collection b.resolved.count 0)
    (provenance : Frontend.Behavioral.Initializers.Provenance b p.declaration header)
    (classification : Frontend.Behavioral.InitializerClassification b p header op a c) :
    Clafer.Behavioral.Initializers.Structure.elaborate
      (BehavioralStructural.interpret b.resolved.admitted.core) p.declaration
      (if op.text = "=" then .constant else .initial)
      ((header.structural.cardinality.map Frontend.Resolution.cardBounds).map Structural.bounds)
      (Frontend.Behavioral.Initializers.scalarAt b.resolved.candidate.core (source.source.utf8ByteSize + 1) a) a =
        .ok ⟨p.declaration, if (b.resolved.candidate.core.get p.declaration).parent.isSome then .parent else .root,
          productionClock c, a⟩ := by
  rw [Clafer.Behavioral.Initializers.Structure.elaborate, ← metadata_agrees b p.declaration header provenance]
  rcases classification with ⟨op, rfl⟩ | ⟨op, c, classified, rfl⟩
  · simp [op, Clafer.Behavioral.Initializers.elaborate, metadata,
      Frontend.Behavioral.Initializers.metadata, productionClock]
  · have agree := classify_agrees (Frontend.Behavioral.Initializers.metadata b p.declaration header)
      (Frontend.Behavioral.Initializers.scalarAt b.resolved.candidate.core (source.source.utf8ByteSize + 1) a)
    rw [classified] at agree
    rw [ite_eq_right (by rw [op]; decide)]
    simp only [Clafer.Behavioral.Initializers.elaborate, ← agree]
    cases c <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The RHS adapter is the independent resolved collection interpretation,
including conditions, inherited references, captures and partial arithmetic. -/
def rhs (m : Clafer.Behavioral.Structural.Core k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : Expression.Collection k n) :
    Clafer.Behavioral.Initializers.Transport.Value U (Set U) n :=
  Expression.collection m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R a

-- [proof->req~compiler-behavioral-elaboration~1]
theorem rhs_transport (m : Clafer.Behavioral.Structural.Core k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : Expression.Collection k n)
    (ρ : Environment U n) (child : U) (t : Nat) :
    Clafer.Behavioral.Initializers.Transport.moved (rhs m τ R a)
      (Clafer.Behavioral.Initializers.Transport.move ρ child) t = rhs m τ R a ρ t :=
  Clafer.Behavioral.Initializers.Transport.observation_preserved _ _ _ _

theorem rhs_binder_transport (m : Clafer.Behavioral.Structural.Core k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (a : Expression.Collection k (n + 1))
    (ρ : Environment U n) (child : U) (S : Set U) (t : Nat) :
    Clafer.Behavioral.Initializers.Transport.moved (rhs m τ R a)
      ((Clafer.Behavioral.Initializers.Transport.move ρ child).push S) t =
        rhs m τ R a (ρ.push S) t :=
  Clafer.Behavioral.Initializers.Transport.binder_preserved _ _ _ _ _

theorem condition_agrees (τ : Trace (Fin k) U) (a : Expression.Meaning U n) :
    Expression.condition τ a =
      Clafer.Behavioral.Initializers.Transport.condition τ Expression.observation a := rfl

theorem conditional_agrees (condition : Option Bool) (yes no : Option α) :
    IR.BehavioralArithmetic.conditional condition yes no =
      Clafer.Behavioral.Initializers.Transport.choose condition yes no := by
  cases condition <;> cases yes <;> cases no <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The generated atom changes attachment only for its entire body. Its
definedness requires every selected context, independently of raw truth. -/
theorem context_observation (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (domain : SetExpr k n) (body : Expression.Meaning U n) (ρ : Environment U n) (t : Nat) :
    (Clafer.Behavioral.Formula.atom (Expression.contextObservation m τ domain body)).Satisfies
      τ Expression.observation true ρ t ↔
        ∀ x ∈ (setExpr domain).eval m τ ρ t,
          body.Defined τ Expression.observation {ρ with this := x} t ∧
          body.raw τ Expression.observation.canonical {ρ with this := x} t := by
  classical
  rw [Clafer.Behavioral.Initializers.atom_satisfies]
  change (∃ p, Expression.contextObservation m τ domain body ρ t = some p ∧ p) ↔ _
  unfold Expression.contextObservation
  dsimp only
  split
  · rename_i defined
    constructor
    · rintro ⟨p, eq, truth⟩
      have eq := Option.some.inj eq
      subst p
      exact fun x hx => ⟨defined x hx, truth x hx⟩
    · intro h
      exact ⟨_, rfl, fun x hx => (h x hx).2⟩
  · rename_i undefined
    simp only [reduceCtorEq, false_and, exists_false, false_iff]
    exact fun h => undefined (fun x hx => (h x hx).1)

theorem empty_context (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (body : Expression.Meaning U n) (ρ : Environment U n) (t : Nat) :
    Expression.contextObservation m τ .empty body ρ t = some True := by
  classical
  simp [Expression.contextObservation, setExpr, Clafer.Behavioral.SetExpr.eval]

-- [proof->req~compiler-behavioral-elaboration~1]
/-- For a live owned head the original context is recovered from fixed actual
ownership. This is the domain used by the generated context atom at birth. -/
theorem parent_context (m : Clafer.Behavioral.Structural.Core k) (τ : Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid m τ) (ρ : Environment U n) (t : Nat)
    (parent : τ.identities.parent ρ.this = some p) (live : ρ.this ∈ τ.live t) :
    Clafer.Behavioral.Structural.eval m τ (.thisStep .parent) ρ t = {p} := by
  ext x
  rw [Clafer.Behavioral.Structural.direct_parent]
  simp only [parent, Option.some.injEq, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1.symm
  · rintro rfl
    exact ⟨rfl, valid.parent_live t _ _ live parent⟩

end ClaferCompiler.SemanticsBridge.Behavioral.Initializers
