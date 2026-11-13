module

public import ClaferCompiler.Frontend.Behavioral.Declarations

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Initializers
open IR.Structural

inductive Clock where
  | instanceBirth | parentBirth | globalZero
  deriving DecidableEq, BEq, Repr

inductive AdmissionError where
  | invalidMultiplicity | parentlessMultiplicity | scalarNotEstablished
  deriving DecidableEq, BEq, Repr

/-- Authored omission and the complete effective group are retained separately
from the resolved local bounds. Refinement never reconstructs this record. -/
structure Metadata where
  abstract : Bool
  parented : Bool
  authored : Option Bounds
  parentGroup : Resolution.Group

def plural (r : Bounds) : Bool := match r.upper with
  | .finite n => decide (1 < n)
  | .unbounded => true

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Native counterpart of the accepted upstream resolved classifier. Scalar
admission is a separate obligation, never a choice of initialization clock. -/
def classify (d : Metadata) (scalar : Bool) : Except AdmissionError Clock :=
  let invalid := match d.authored with
    | none => false
    | some r => !decide r.Valid
  let selected : Except AdmissionError Clock :=
    if d.abstract && !d.parented then
      match d.authored with
      | none => .ok .instanceBirth
      | some r => if r = ({} : Bounds) then .ok .globalZero else .error .parentlessMultiplicity
    else if d.abstract && d.authored.isNone then .ok .instanceBirth
    else .ok (if plural (d.authored.getD d.parentGroup.childDefault) then
      .parentBirth else .instanceBirth)
  if invalid then .error .invalidMultiplicity else
    match selected with
    | .error e => .error e
    | .ok clock => if d.abstract && decide (clock = .instanceBirth) && !scalar then
        .error .scalarNotEstablished else .ok clock

-- [impl->req~compiler-behavioral-structural-bridge~1]
def metadata {source : Document} (b : BoundDeclarations source)
    (declaration : Fin b.resolved.count) (header : Header) : Metadata where
  abstract := header.structural.abstractToken.isSome
  parented := (b.resolved.candidate.core.get declaration).parent.isSome
  authored := header.structural.cardinality.map Resolution.cardBounds
  parentGroup := ((b.resolved.candidate.core.get declaration).parent.map
    (fun p => b.resolved.candidate.groups[p])).getD (.bounds {})

/-- Check the retained behavioral header against the structurally resolved
authored record. This certificate also makes projection mismatches diagnostic. -/
def Provenance {source : Document} (b : BoundDeclarations source)
    (declaration : Fin b.resolved.count) (header : Header) : Prop :=
  b.resolved.admitted.core.authoredAbstract[declaration] = header.structural.abstractToken.isSome ∧
  (b.resolved.candidate.core.get declaration).authored = some
    ⟨header.structural.abstractToken.isSome, header.structural.cardinality.map Resolution.cardBounds,
      header.structural.group.map (fun g => (Resolution.authoredGroup g).range)⟩

instance {source : Document} (b : BoundDeclarations source)
    (declaration : Fin b.resolved.count) (header : Header) : Decidable (Provenance b declaration header) :=
  inferInstanceAs (Decidable (_ ∧ _))

end ClaferCompiler.Frontend.Behavioral.Initializers
