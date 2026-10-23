module

public import ClaferCompiler.IR.Inherited
public import ClaferCompiler.Backend.Alloy.StructuralRepresentation

@[expose] public section
/-! [impl->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Backend.Alloy.Inherited
open IR.Inherited

/-- Structurally recursive traversal. Its fuel is supplied by the checked super
rank below, so the proof rules out truncation of any real ancestor path. -/
def ancestorWalk (m : IR.Structural.Core n) (fuel : Nat) : Fin n → List (Fin n) :=
  Nat.rec (fun d => [d]) (fun _ step d => d :: match (m.get d).super with
    | none => []
    | some p => step p) fuel

/-- Original declaration ancestors, from the context upwards. -/
def ancestors (v : Validated n) (d : Fin n) : List (Fin n) :=
  ancestorWalk v.core.structural v.certificate.superRank[d] d

def children (v : Validated n) (d : Fin n) : List (Fin n) :=
  (ancestors v d).flatMap (Structural.children v.core.structural)

/-- Union existing head fibers; multiple views never create extra occurrences. -/
def childHeads (v : Validated n) (d : Fin n)
    (a : Structural.Allocation n := Structural.allocation v.layout) : Rel :=
  Structural.union ((children v d).map fun c =>
    .join (.var 0) (a.contains c))

def groups (v : Validated n)
    (a : Structural.Allocation n := Structural.allocation v.layout) : List Formula :=
  ((List.finRange n).filter fun d => !v.core.explicitAbstract[d]).map fun d =>
    .all (a.head d)
      (Structural.interval (v.core.structural.get d).groupBounds (childHeads v d a))

/-- Keep the proved structural layout and add effective ordinary-field groups.
The projected direct groups are unrestricted and contribute no integer count. -/
def target (v : Validated n) (scopes : List Scope) (w : Nat)
    (a : Structural.Allocation n := Structural.allocation v.layout) : Module :=
  { Structural.target v.layout scopes w a with
    facts := (Structural.facts v.layout a).map Prod.snd ++ groups v a }

inductive Obligation where
  | structural (obligation : Structural.Obligation)
  | realizedGroup (declaration : IR.Structural.DeclId)
  deriving DecidableEq

def obligations (v : Validated n)
    (a : Structural.Allocation n := Structural.allocation v.layout) : List Obligation :=
  ((Structural.facts v.layout a).map fun x => .structural x.1) ++
    ((List.finRange n).filter fun d => !v.core.explicitAbstract[d]).map fun d =>
      .realizedGroup (v.core.structural.get d).id

structure Compiled where
  module : CheckedModule
  declarations : List Structural.DeclarationMap
  obligations : List Obligation

def compile (v : Validated n) (b : Structural.Bounds) : Except Structural.Error Compiled := do
  let scopes ← Structural.resolveScopes v.layout b
  match check (target v scopes b.bitwidth) with
  | .error .malformedSyntax => .error .internalTarget
  | .error .unsupportedBounds => .error .unsupportedBounds
  | .ok checked => .ok ⟨checked, Structural.nameMap v.layout, obligations v⟩

/-- Share the same proved allocation across inherited generation and metadata. -/
def compileCached (v : Validated n) (b : Structural.Bounds) : Except Structural.Error Compiled := do
  let scopes ← Structural.resolveScopes v.layout b
  let a := Structural.cachedAllocation v.layout
  match check (target v scopes b.bitwidth a) with
  | .error .malformedSyntax => .error .internalTarget
  | .error .unsupportedBounds => .error .unsupportedBounds
  | .ok checked => .ok ⟨checked, Structural.nameMap v.layout a, obligations v a⟩

@[csimp] theorem compile_eq_compileCached : @compile = @compileCached := by
  funext n v b
  simp only [compile, compileCached, Structural.cachedAllocation_eq]

/-- Native entry point for the explicit inherited profile. -/
def compileRaw (r : IR.Inherited.Raw) (b : Structural.Bounds) :
    Except Structural.Error Compiled := do
  let v ← (IR.Inherited.validateRaw r).mapError Structural.Error.source
  compile v b

abbrev encode (v : Validated n) (o : Structural.Observation n) := Structural.encode v.layout o
abbrev decode (v : Validated n) (i : Instance) := Structural.decode v.layout i

end ClaferCompiler.Backend.Alloy.Inherited
