module

public import ClaferCompiler.Frontend.Behavioral.InitializerClassification
public import ClaferCompiler.SemanticsBridge.Resolution
public import Clafer.Behavioral.InitializerStructure
public import ClaferCompiler.SemanticsBridge.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Initializers
open Frontend.Behavioral.Initializers
namespace Upstream
abbrev Metadata := Clafer.Behavioral.Initializers.Classification.Declaration
abbrev Clock := Clafer.Behavioral.Initializers.Classification.Clock
abbrev Error := Clafer.Behavioral.Initializers.Classification.Diagnostic
end Upstream

def metadata (d : Metadata) : Upstream.Metadata :=
  ⟨d.abstract, d.parented, d.authored.map Structural.bounds, Resolution.group d.parentGroup⟩

def clock : Clock → Upstream.Clock
  | .instanceBirth => .instanceBirth
  | .parentBirth => .parentBirth
  | .globalZero => .globalZero

def choice : Frontend.Behavioral.ClockChoice → Clafer.Behavioral.Initializers.Classification.Selection
  | .perInstance => .instance
  | .perCollection => .collection

def diagnostic : AdmissionError → Upstream.Error
  | .invalidMultiplicity => .invalidMultiplicity
  | .parentlessMultiplicity => .parentlessMultiplicity
  | .scalarNotEstablished => .scalarNotEstablished

def result : Except AdmissionError Clock → Except Upstream.Error Upstream.Clock
  | .ok c => .ok (clock c)
  | .error e => .error (diagnostic e)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The runtime classifier has exactly the accepted clocks and diagnostics,
including omitted versus unrestricted abstract multiplicities. -/
private theorem shorthand_agrees (d : Metadata) (scalar : Bool) :
    result (classify d scalar) =
      Clafer.Behavioral.Initializers.Classification.classify (metadata d) scalar := by
  rcases d with ⟨abstract, parented, authored, group⟩
  cases abstract <;> cases parented <;> cases scalar <;> cases authored with
  | none =>
    cases group with
    | bounds r =>
      rcases r with ⟨lo, hi⟩
      cases lo <;> cases hi <;> rfl
    | xor | or | mux | opt => rfl
  | some r =>
    rcases r with ⟨lo, hi⟩
    cases hi <;>
      simp only [classify, metadata, Clafer.Behavioral.Initializers.Classification.classify,
        result, clock, diagnostic, plural, Structural.bounds,
        IR.Structural.Bounds.Valid, Clafer.Behavioral.Initializers.Classification.valid,
        Clafer.Behavioral.Initializers.Classification.plural,
        Clafer.unrestricted, Option.map_some, Option.isNone_some,
        Option.getD_some, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true,
        Bool.and_false, Bool.and_true, decide_true,
        Bool.false_eq_true, ↓reduceIte]
    all_goals split_ifs <;> simp_all [IR.Structural.Bounds.mk.injEq, DPGraph.Predicates.Range.mk.injEq]
    all_goals split_ifs <;> rfl

-- [proof->req~compiler-initializer-clocks~1]
theorem classify_agrees (d : Metadata) (scalar : Bool) (selected : Option Frontend.Behavioral.ClockChoice := none) :
    result (classify d scalar selected) =
      Clafer.Behavioral.Initializers.Classification.classify (metadata d) scalar (selected.map choice) := by
  cases selected with
  | none => exact shorthand_agrees d scalar
  | some c =>
    have valid (r : IR.Structural.Bounds) :
        decide r.Valid = Clafer.Behavioral.Initializers.Classification.valid (Structural.bounds r) := by
      cases r with | mk lo hi => cases hi <;> rfl
    rcases d with ⟨abstract, parented, authored, group⟩
    cases authored <;> cases c <;> cases parented <;> cases abstract <;> cases scalar <;>
      simp [classify, metadata, Clafer.Behavioral.Initializers.Classification.classify,
        choice, Clafer.Behavioral.Initializers.Classification.Selection.resolve,
        result, clock, diagnostic, valid] <;> split_ifs <;> rfl

-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- The certified authored header, retained parent/group data and accepted
structural core provide exactly the production classifier's metadata. -/
theorem metadata_agrees {source : Frontend.Behavioral.Document}
    (b : Frontend.Behavioral.BoundDeclarations source) (d : Fin b.resolved.count)
    (header : Frontend.Behavioral.Header) (provenance : Provenance b d header) :
    metadata (Frontend.Behavioral.Initializers.metadata b d header) =
      Clafer.Behavioral.Initializers.Structure.metadata
        (BehavioralStructural.interpret b.resolved.admitted.core) d
        ((header.structural.cardinality.map Frontend.Resolution.cardBounds).map Structural.bounds) := by
  have habstract := provenance.1
  rw [b.resolved.sameCore] at habstract ⊢
  cases hp : (b.resolved.candidate.core.get d).parent <;>
    simp [metadata, Frontend.Behavioral.Initializers.metadata,
      Clafer.Behavioral.Initializers.Structure.metadata, BehavioralStructural.interpret,
      Frontend.BehavioralResolution.core, Structural.interpret, hp, ← habstract,
      Resolution.group]

-- [proof->req~compiler-behavioral-elaboration~1]
theorem global_parentless (d : Metadata) (scalar : Bool) {selected : Option Frontend.Behavioral.ClockChoice}
    (h : classify d scalar selected = .ok .globalZero) : d.parented = false := by
  rcases d with ⟨abstract, parented, authored, group⟩
  cases parented with
  | false => rfl
  | true =>
    cases selected with
    | some c =>
      cases c <;> cases abstract <;> cases scalar <;>
        simp [classify] at h <;> split_ifs at h <;> cases h
    | none =>
      cases abstract <;> cases scalar <;> cases authored <;>
        simp only [classify, Bool.not_true, Bool.and_false, Bool.false_and,
          Bool.true_and, Bool.not_false, Option.isNone_none, Option.isNone_some,
          Option.getD_none, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at h
      all_goals try split_ifs at h
      all_goals cases h

end ClaferCompiler.SemanticsBridge.Behavioral.Initializers
