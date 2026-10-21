module

public import ClaferCompiler.Backend.Alloy.StructuralRepresentation

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Structural

/-! The external adapter parses Analyzer output into checked target tables.
This executable boundary exports stable declaration IDs and original object
labels; it never filters by satisfaction or quotients reference occurrences.
[impl->req~compiler-instance-decode~1] -/
structure Candidate where
  objects : List Nat
  root : Nat
  members : List (Nat × Nat)
  containment : List (Nat × (Nat × Nat))
  references : List (Nat × (Nat × Nat))
  deriving DecidableEq, Repr

def candidate (v : IR.Structural.Validated n) (o : Observation n) : Candidate where
  objects := o.objects
  root := o.root
  members := (List.finRange n).flatMap fun d =>
    (o.heads d).map fun x => ((v.core.get d).id, x)
  containment := (List.finRange n).flatMap fun d =>
    (o.containment d).map fun pair => ((v.core.get d).id, pair)
  references := (List.finRange n).flatMap fun d =>
    (o.dereference d).map fun pair => ((v.core.get d).id, pair)

def decodeCandidate (v : IR.Structural.Validated n) (i : Instance) : Except DecodeError Candidate :=
  (decode v i).map (candidate v)

/-! Exact row correspondence is independent of source or target satisfaction.
The external JSON/Analyzer parser is not kernel verified.
[proof->req~compiler-instance-decode~1] -/
theorem candidate_members (v : IR.Structural.Validated n) (o : Observation n) (id x : Nat) :
    (id, x) ∈ (candidate v o).members ↔
      ∃ d, (v.core.get d).id = id ∧ x ∈ o.heads d := by
  simp only [candidate, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨d, y, hy, e⟩
    cases e
    exact ⟨d, rfl, hy⟩
  · rintro ⟨d, e, hy⟩
    exact ⟨d, _, hy, by simp [e]⟩

theorem candidate_containment (v : IR.Structural.Validated n) (o : Observation n)
    (id p h : Nat) : (id, (p, h)) ∈ (candidate v o).containment ↔
      ∃ d, (v.core.get d).id = id ∧ (p, h) ∈ o.containment d := by
  simp only [candidate, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨d, y, hy, e⟩
    cases e
    exact ⟨d, rfl, hy⟩
  · rintro ⟨d, e, hy⟩
    exact ⟨d, _, hy, by simp [e]⟩

theorem candidate_references (v : IR.Structural.Validated n) (o : Observation n)
    (id h t : Nat) : (id, (h, t)) ∈ (candidate v o).references ↔
      ∃ d, (v.core.get d).id = id ∧ (h, t) ∈ o.dereference d := by
  simp only [candidate, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨d, y, hy, e⟩
    cases e
    exact ⟨d, rfl, hy⟩
  · rintro ⟨d, e, hy⟩
    exact ⟨d, _, hy, by simp [e]⟩

end ClaferCompiler.Backend.Alloy.Structural
