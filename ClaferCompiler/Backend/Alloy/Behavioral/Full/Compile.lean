module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Expressions
public import ClaferCompiler.Backend.Alloy.Behavioral.Compile
public import ClaferCompiler.IR.Behavioral.Properties

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full
open IR.Behavioral

abbrev Constraint (k : Nat) := Properties.Constraint k (Expression.Atom k) (Expression.Collection k)
abbrev Model (k : Nat) := Properties.Model k (Expression.Atom k) (Expression.Collection k)
abbrev Request (k : Nat) := Properties.Request k (Expression.Atom k) (Expression.Collection k)

/-- Source declaration scopes bound ancestor pools, not the sum of overlapping
views. The integer observation interval is independent of object/time budgets. -/
structure Bounds extends toBehavioralBounds : Behavioral.Bounds where
  values : Option IR.Expr.Interval := none

def integerRange (b : Bounds) : IR.Expr.Interval :=
  b.values.getD ⟨minInt b.bitwidth, maxInt b.bitwidth⟩

def error (code : String) (category : IR.Structural.Category := .unsupported) : IR.Structural.Diagnostic :=
  { category, code }

def declaredScope (v : IR.BehavioralStructural.Validated k) (b : Bounds) (d : Fin k) : Scope :=
  ((b.declarations.find? fun row => row.1 == (v.core.structural.get d).id).map Prod.snd).getD
    ⟨if d == v.core.structural.root then 1 else b.objects, false⟩

def directScope (v : IR.BehavioralStructural.Validated k) (b : Bounds) (d : Fin k) : Scope :=
  if integerDeclaration v d || v.core.authoredAbstract[d] then ⟨0, false⟩ else
    ⟨(v.analysis.ancestors[d].map fun a => (declaredScope v b a).size).foldl min b.objects, false⟩

def scopes (v : IR.BehavioralStructural.Validated k) (b : Bounds) : List Scope :=
  ⟨b.objects, false⟩ :: (List.finRange k).map (directScope v b)

/-- Every estimate is calculated from admitted scope capacities. Integer
reference values are constrained by the emitted value-range fact. -/
def estimates (v : IR.BehavioralStructural.Validated k) (b : Bounds) : Expression.Ranges.Inputs k where
  width := b.bitwidth
  extentAllowed := Vector.ofFn fun d => !integerDeclaration v d
  stepAllowed := fun st => match st with
    | .child d => !integerDeclaration v d
    | _ => true
  context := ⟨1, integerRange b⟩
  root := ⟨1, ⟨0, 0⟩⟩
  extents := Vector.ofFn fun d =>
    ⟨if integerDeclaration v d then 2 ^ b.bitwidth else min b.objects (declaredScope v b d).size,
      if integerDeclaration v d then ⟨minInt b.bitwidth, maxInt b.bitwidth⟩ else ⟨0, 0⟩⟩
  steps := fun step => match step with
    | .parent => ⟨b.objects, ⟨0, 0⟩⟩
    | .child d => ⟨min b.objects (declaredScope v b d).size, ⟨0, 0⟩⟩
    | .deref d =>
      match v.analysis.referenceOwners[d] with
      | none => ⟨0, ⟨0, 0⟩⟩
      | some owner => match (v.core.structural.get owner).reference.target with
        | none => ⟨0, ⟨0, 0⟩⟩
        | some target => ⟨min b.objects (declaredScope v b d).size,
            if integerDeclaration v target then integerRange b else ⟨0, 0⟩⟩

def scopeFact (scope : Scope) (r : Temporal.Rel) : Temporal.Formula :=
  if scope.exact then .compare .eq (.count r) (.literal (Int.ofNat scope.size))
  else .compare .le (.count r) (.literal (Int.ofNat scope.size))

def boundFacts (v : IR.BehavioralStructural.Validated k) (b : Bounds) : List Temporal.Formula :=
  let values := union ((integerCandidates (integerRange b)).map Temporal.Rel.integer)
  (.unary .always (.subset (.values 0) (.product (.sig 0) values))) ::
    ((List.finRange k).filter fun d => !integerDeclaration v d).map
      (fun d => scopeFact (declaredScope v b d) (pool v d))

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

def placement (v : IR.BehavioralStructural.Validated k) : Surface.Modifiers.Placement k → Temporal.Rel
  | .all => live v
  | .heads d => head v d
  | .parents d => match (v.core.structural.get d).parent with
    | none => .empty .unary
    | some p => head v p

def context (b : Bounds) : Expressions.Context 0 :=
  ⟨⟨.var 0, Fin.elim0,
      (List.range b.objects).map (fun i => .var (i + 1)) ++
        (integerCandidates ⟨minInt b.bitwidth, maxInt b.bitwidth⟩).map Temporal.Rel.integer⟩, #v[]⟩

-- [impl->req~compiler-trace-assurance~1]
/-- Explicit budget exhaustion is unsupported, never a successful truncation.
The existing range derivation checks all source operands before target lowering. -/
def attached (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (owners : Temporal.Rel) (a : Expression.Formula k 0) : Except IR.Structural.Diagnostic Temporal.Formula := do
  let _ ← Expression.Ranges.analyze (estimates v b) fuel a #v[]
  let ctx := if owners == head v v.core.structural.root then
    { context b with lexical := { (context b).lexical with this := root v } }
    else context b
  let body ← (Expressions.lowerAt v (estimates v b) fuel fuel).formula ctx a
  let property : Temporal.Formula := .unary .always (.all owners (Partial.satisfaction body true))
  return Behavioral.coverPool b.objects property

def constraint (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (a : Constraint k) : Except IR.Structural.Diagnostic Temporal.Formula := do
  if integerDeclaration v a.owner then throw (error "behavioral.infinite-attachment")
  attached v b fuel (head v a.owner) a.body

def validateBounds (v : IR.BehavioralStructural.Validated k) (b : Bounds) : Except IR.Structural.Diagnostic Unit := do
  unless 0 < b.objects && 1 ≤ b.bitwidth && b.bitwidth ≤ 16 &&
      1 ≤ b.minSteps && b.minSteps ≤ b.maxSteps && (integerRange b).fits b.bitwidth do
    throw (error "behavioral.bounds")
  unless (b.declarations.map Prod.fst).Pairwise (· ≠ ·) &&
      b.declarations.all (fun row => (List.finRange k).any fun d =>
        (v.core.structural.get d).id == row.1 && !integerDeclaration v d) do
    throw (error "behavioral.declaration-scope")
  unless decide (PrimitiveShape v) do throw (error "behavioral.primitive-shape")

-- [impl->req~compiler-trace-assurance~1]
/-- The implicit mathematical integer declaration has no authored modifier
attachment. Raw requests must respect the same finite attachment boundary. -/
def validateModifiers (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List Surface.Modifiers.Modifier) k) : Except IR.Structural.Diagnostic Unit :=
  if (List.finRange k).all (fun d => !integerDeclaration v d ||
      (IR.Behavioral.Modifiers.effective v table d).isEmpty) then .ok ()
  else .error (error "behavioral.infinite-attachment")

structure Compiled where
  module : Temporal.CheckedModule
  /-- Source declaration IDs retain direct signature and inherited live views. -/
  declarations : List (IR.Structural.DeclId × Nat × Temporal.Rel)

-- [impl->req~compiler-trace-assurance~1]
-- [impl->req~compiler-full-behavioral-correctness~1]
-- [impl->req~compiler-behavioral-property-commands~1]
/-- Full in-memory requests keep assertions out of facts. A check command
classically negates the complete attached property, including definedness. -/
def compile (r : Request k) (b : Bounds) (fuel : Nat) : Except IR.Structural.Diagnostic Compiled := do
  let v := r.model.structural
  validateBounds v b
  validateModifiers v r.model.modifiers
  let constraints ← r.model.constraints.mapM (constraint v b fuel)
  let modifiers ← ((List.finRange k).flatMap fun d =>
    (IR.Behavioral.Modifiers.effective v r.model.modifiers d).flatMap (modifierExpansions d)).mapM
      fun (where_, body) => attached v b fuel (placement v where_) body
  let (kind, body) ← match r.command with
    | .check i => do pure (.check, ← constraint v b fuel r.model.assertions[i])
    | .run scenario => do pure (.run, Expressions.all (← scenario.mapM (constraint v b fuel)))
  let raw : Temporal.Module := {
    schema := schema v
    facts := identityFacts v ++ boundFacts v b ++
      (stateFacts v ++ [reachabilityFact v b.objects]).map (.unary .always) ++ constraints ++ modifiers
    command := ⟨kind, body, scopes v b, b.bitwidth, b.minSteps, b.maxSteps⟩ }
  match Temporal.check raw with
  | .error .unsupportedBounds => throw (error "behavioral.target-bounds")
  | .error .malformedSyntax => throw (error "behavioral.internal-target")
  | .ok checked => return ⟨checked, (List.finRange k).map fun d =>
      ((v.core.structural.get d).id, signatureId d, head v d)⟩

end ClaferCompiler.Backend.Alloy.Behavioral.Full
