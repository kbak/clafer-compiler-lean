module

public import ClaferCompiler.IR.Behavioral.Primitive
public import ClaferCompiler.SemanticsBridge.Behavioral.Formula
public import ClaferCompiler.SemanticsBridge.BehavioralArithmetic
public import Clafer.Behavioral.Initializers

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Primitive
open IR.Behavioral.Primitive

def extreme : Extreme → Clafer.Behavioral.Aggregate.Extreme
  | .minimum => .minimum
  | .maximum => .maximum

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Checked mutual datatype recursors avoid generated unsafe equation helpers.
All three interpretations use the same constructor algebra. -/
def collection : Collection k n → Clafer.Behavioral.CollectionExpr (Fin k) n :=
  Collection.rec
    (motive_1 := fun n _ => Clafer.Behavioral.CollectionExpr (Fin k) n)
    (motive_2 := fun n _ => Clafer.Behavioral.IntegerExpr (Fin k) n)
    (motive_3 := fun n _ => Clafer.Behavioral.CollectionList (Fin k) n)
    (fun {_} a => .set (setExpr a))
    (fun {_} i => .literal i)
    (fun {_} _ a => .integer a)
    (fun {_} op _ a => .extreme (extreme op) a)
    (fun {_} _ _ a b => .union a b)
    (fun {_} _ _ a b => .inter a b)
    (fun {_} _ _ a b => .diff a b)
    (fun {_} i => .literal i)
    (fun {_} _ a => .coerce a)
    (fun {_} _ a => .extract a)
    (fun {_} _ a => .cardinality a)
    (fun {_} op _ _ a b => .binary (BehavioralArithmetic.binary op) a b)
    (fun {_} _ a => .negate a)
    (fun {_} op _ _ domains body => .fold (BehavioralArithmetic.fold op) domains body)
    (fun {_} => .nil)
    (fun {_} _ _ a rest => .cons a rest)

def integer : Integer k n → Clafer.Behavioral.IntegerExpr (Fin k) n :=
  Integer.rec
    (motive_1 := fun n _ => Clafer.Behavioral.CollectionExpr (Fin k) n)
    (motive_2 := fun n _ => Clafer.Behavioral.IntegerExpr (Fin k) n)
    (motive_3 := fun n _ => Clafer.Behavioral.CollectionList (Fin k) n)
    (fun {_} a => .set (setExpr a))
    (fun {_} i => .literal i)
    (fun {_} _ a => .integer a)
    (fun {_} op _ a => .extreme (extreme op) a)
    (fun {_} _ _ a b => .union a b)
    (fun {_} _ _ a b => .inter a b)
    (fun {_} _ _ a b => .diff a b)
    (fun {_} i => .literal i)
    (fun {_} _ a => .coerce a)
    (fun {_} _ a => .extract a)
    (fun {_} _ a => .cardinality a)
    (fun {_} op _ _ a b => .binary (BehavioralArithmetic.binary op) a b)
    (fun {_} _ a => .negate a)
    (fun {_} op _ _ domains body => .fold (BehavioralArithmetic.fold op) domains body)
    (fun {_} => .nil)
    (fun {_} _ _ a rest => .cons a rest)

def collections : Collections k n → Clafer.Behavioral.CollectionList (Fin k) n :=
  Collections.rec
    (motive_1 := fun n _ => Clafer.Behavioral.CollectionExpr (Fin k) n)
    (motive_2 := fun n _ => Clafer.Behavioral.IntegerExpr (Fin k) n)
    (motive_3 := fun n _ => Clafer.Behavioral.CollectionList (Fin k) n)
    (fun {_} a => .set (setExpr a))
    (fun {_} i => .literal i)
    (fun {_} _ a => .integer a)
    (fun {_} op _ a => .extreme (extreme op) a)
    (fun {_} _ _ a b => .union a b)
    (fun {_} _ _ a b => .inter a b)
    (fun {_} _ _ a b => .diff a b)
    (fun {_} i => .literal i)
    (fun {_} _ a => .coerce a)
    (fun {_} _ a => .extract a)
    (fun {_} _ a => .cardinality a)
    (fun {_} op _ _ a b => .binary (BehavioralArithmetic.binary op) a b)
    (fun {_} _ a => .negate a)
    (fun {_} op _ _ domains body => .fold (BehavioralArithmetic.fold op) domains body)
    (fun {_} => .nil)
    (fun {_} _ _ a rest => .cons a rest)

def atom : Atom k n → Clafer.Behavioral.PrimitiveExpression.Atom (Fin k) n
  | .inhabited a => .inhabited (collection a)
  | .equal a b => .equal (collection a) (collection b)
  | .subset a b => .subset (collection a) (collection b)
  | .integerEqual a b => .integerEqual (integer a) (integer b)
  | .less a b => .less (integer a) (integer b)

def formula (a : Formula k n) := Generic.interpret (fun {_} => atom) (fun {_} => collection) a

-- [proof->req~compiler-behavioral-elaboration~1]
theorem initializer_interpret (heads left value : Collection k n) :
    formula (constantInitializer heads left value) =
      Clafer.Behavioral.Initializers.constant (collection heads) (collection left) (collection value) := rfl

/-- The accepted upstream equation applies at every live enclosing state.
Defined operands are an explicit premise, never inferred from absence of heads. -/
theorem initializer_truth {U : Type u} (m : Clafer.Behavioral.Structural.Core k)
    (τ : Clafer.Behavioral.Trace (Fin k) U) (R : Clafer.Constraints.IntegerRealization U)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) (heads left value : Collection k n)
    (H L V : Set U)
    (hh : Clafer.Behavioral.PrimitiveExpression.collection m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) R ρ t (collection heads) = some H)
    (hl : Clafer.Behavioral.PrimitiveExpression.collection m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) R ρ t (collection left) = some L)
    (hv : Clafer.Behavioral.PrimitiveExpression.collection m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) R ρ t (collection value) = some V) :
    (formula (constantInitializer heads left value)).Satisfies τ (.primitives m τ R) true ρ t ↔
      (H.Nonempty → L = V) := by
  rw [initializer_interpret]
  exact Clafer.Behavioral.Initializers.constant_truth m τ R ρ t _ _ _ H L V hh hl hv

-- [proof->req~compiler-behavioral-elaboration~1]
theorem normalized_truth (a : Normalized k n) :
    formula a.truth = (formula a.original).normalize a.positive := by
  rw [a.correspondence]
  exact Generic.normalize_interpret _ _ _ _ _ _

/-- The retained original tree supplies the strict partial domain for all
branches and quantified members. Undefinedness cannot be erased by rewriting. -/
theorem normalized_satisfaction (a : Normalized k n)
    (τ : Clafer.Behavioral.Trace C U)
    (O : Clafer.Behavioral.PartialObservation
      (Clafer.Behavioral.PrimitiveExpression.Atom (Fin k)) (Clafer.Behavioral.CollectionExpr (Fin k)) U)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (formula a.original).Satisfies τ O a.positive ρ t ↔
      (formula a.original).Defined τ O ρ t ∧ (formula a.truth).raw τ O.canonical ρ t := by
  rw [a.correspondence]
  exact Generic.satisfies_iff_normalized _ _ _ _ _ _ _ _ _ _

end ClaferCompiler.SemanticsBridge.Behavioral.Primitive
