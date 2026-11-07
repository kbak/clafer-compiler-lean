module

public import ClaferCompiler.Frontend.Behavioral.ValueCore

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Names
open IR.Behavioral Values

/-- A navigation edge selects current structural relations; the first step from
`this` uses its fixed context identity. Field lookup precedes reference traversal. -/
inductive Navigate (v : IR.BehavioralStructural.Validated k) :
    Fin k → Expression.Collection k n → String → Ty k → Expression.Collection k n → Prop where
  | parent : Navigate v d a "parent" (parentType v d) (navigateCollection .parent a)
  | dereference (reference : IR.BehavioralSupport.referenceView v d = some r) :
      Navigate v d a "dref" (classType v r.target) (navigateCollection (.deref d) a)
  | field (ordinary : name ≠ "parent" ∧ name ≠ "dref")
      (field : Constraints.Field v.core.structural d name depth p y) :
      Navigate v d a name (classType v y) (navigateCollection (.child y) a)
  | reference (ordinary : name ≠ "parent" ∧ name ≠ "dref")
      (absent : ¬ Constraints.HasField v.core.structural d name)
      (reference : IR.BehavioralSupport.referenceView v d = some r)
      (tail : Navigate v r.target (navigateCollection (.deref d) a) name type term) :
      Navigate v d a name type term

def referenceAt (v : IR.BehavioralStructural.Validated k) (start : Fin k) (depth : Nat) : Option (Fin k) :=
  depth.repeat (fun d => d.bind fun d => (IR.BehavioralSupport.referenceView v d).map (·.target)) (some start)

def Reachable (v : IR.BehavioralStructural.Validated k) (start : Fin k) (name : String) : Prop :=
  ∃ depth : Fin (k + 1), match referenceAt v start depth.val with
    | none => False
    | some d => Constraints.HasField v.core.structural d name

instance (v : IR.BehavioralStructural.Validated k) (start : Fin k) (name : String) :
    Decidable (Reachable v start name) := by
  unfold Reachable
  letI : DecidablePred (fun depth : Fin (k + 1) => match referenceAt v start depth.val with
    | none => False | some d => Constraints.HasField v.core.structural d name) :=
    fun _ => by dsimp only; split <;> infer_instance
  infer_instance

def Applicable (v : IR.BehavioralStructural.Validated k) (d : Fin k) (name : String) : Prop :=
  if name = "parent" then True
  else if name = "dref" then (IR.BehavioralSupport.referenceView v d).isSome = true
  else Reachable v d name

instance (v : IR.BehavioralStructural.Validated k) (d : Fin k) (name : String) :
    Decidable (Applicable v d name) := by unfold Applicable; infer_instance

/-- A heterogeneous path visits every applicable class, retaining no result for
classes which cannot supply the requested navigation. -/
inductive Pieces (v : IR.BehavioralStructural.Validated k) (a : Expression.Collection k n) (name : String) :
    List (Fin k) → List (Ty k × Expression.Collection k n) → Prop where
  | nil : Pieces v a name [] []
  | skip (absent : ¬ Applicable v d name) (rest : Pieces v a name ds out) : Pieces v a name (d :: ds) out
  | cons (present : Applicable v d name) (head : Navigate v d (.ofType d a) name type term)
      (rest : Pieces v a name ds out) : Pieces v a name (d :: ds) ((type, term) :: out)

inductive ScopePath (v : IR.BehavioralStructural.Validated k) (owner : Fin k) :
    Nat → Fin k → SetExpr k n → Prop where
  | here : ScopePath v owner 0 owner .this
  | parent (path : ScopePath v owner depth d a) (parent : (v.core.structural.get d).parent = some p) :
      ScopePath v owner (depth + 1) p (navigateSet .parent a)

def NoLocal (Γ : Context k n) (name : String) : Prop :=
  ∀ i : Fin n, (Γ[i].map (fun entry => entry.1.text)) ≠ some name
instance (Γ : Context k n) (name : String) : Decidable (NoLocal Γ name) := by
  unfold NoLocal; infer_instance

def HasTarget (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (name : String) : Prop :=
  match IR.BehavioralSupport.referenceView v owner with
  | none => False
  | some r => Reachable v r.target name
instance (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (name : String) :
    Decidable (HasTarget v owner name) := by
  unfold HasTarget; split <;> infer_instance

/-- Source lookup rules record shadowing, the original lexical scope chain,
head-field priority and the unique global fallback. -/
-- [impl->req~compiler-behavioral-elaboration~1]
inductive Name (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (Γ : Context k n) :
    Option (Value k n) → String → Value k n → Prop where
  | empty : Name v owner Γ none "noclafer" (.collection .empty (.set .empty))
  | emptyRelative : Name v owner Γ (some (.collection type a)) "noclafer"
      (.collection .empty (.inter a (.set .empty)))
  | this : Name v owner Γ none "this" (.collection (.objects owner) (.set .this))
  | local (lookup : Binders.Lookup Γ name) :
      Name v owner Γ none name (.collection lookup.type (.set (.var lookup.index)))
  | special (spelling : name = "parent" ∨ name = "dref") (path : Navigate v owner (.set .this) name type term) :
      Name v owner Γ none name (.collection type term)
  | contextual (localAbsent : NoLocal Γ name) (ordinary : name ≠ "this" ∧ name ≠ "parent" ∧ name ≠ "dref")
      (scope : ScopePath v owner depth d a) (notRoot : d ≠ v.core.structural.root)
      (nearest : Constraints.NoContext v.core.structural owner name depth)
      (hasField : Constraints.HasField v.core.structural d name)
      (path : Navigate v d (.set a) name type term) : Name v owner Γ none name (.collection type term)
  | target (localAbsent : NoLocal Γ name) (ordinary : name ≠ "this" ∧ name ≠ "parent" ∧ name ≠ "dref")
      (contextAbsent : Constraints.NoContext v.core.structural owner name (k + 1))
      (reference : IR.BehavioralSupport.referenceView v owner = some r) (reachable : Reachable v r.target name)
      (path : Navigate v r.target (.set (navigateSet (.deref owner) .this)) name type term) :
      Name v owner Γ none name (.collection type term)
  | global (localAbsent : NoLocal Γ name) (ordinary : name ≠ "this" ∧ name ≠ "parent" ∧ name ≠ "dref")
      (contextAbsent : Constraints.NoContext v.core.structural owner name (k + 1))
      (targetAbsent : ¬ HasTarget v owner name) (unique : Constraints.Global v.core.structural name d) :
      Name v owner Γ none name (.collection (classType v d) (.set (.extent d)))
  | relative (path : Navigate v d a name type term) :
      Name v owner Γ (some (.collection (.objects d) a)) name (.collection type term)
  | mixed (pieces : Pieces v a name ds out) (nonempty : out ≠ []) :
      Name v owner Γ (some (.collection (.mixed ds) a)) name
        (.collection (classUnion v (out.flatMap (classes v ·.1)))
          (out.foldl (fun acc p => .union acc p.2) (.set .empty)))
  | emptyParent : Name v owner Γ (some (.collection .empty a)) "parent"
      (.collection .empty (navigateCollection .parent a))
  | emptyDereference : Name v owner Γ (some (.collection .empty a)) "dref" (.collection .empty a)
  | emptyField (spelling : (v.core.structural.get d).name = name) (user : (v.core.structural.get d).origin = .user) :
      Name v owner Γ (some (.collection .empty a)) name (.collection .empty (navigateCollection (.child d) a))

end ClaferCompiler.Frontend.Behavioral.Names
