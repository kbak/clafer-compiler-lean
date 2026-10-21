module

public import ClaferCompiler.Correctness.InheritedViews

@[expose] public section
namespace ClaferCompiler.Tests.Inherited
open Backend.Alloy
open Backend.Alloy.Inherited
open Correctness.Inherited

local instance (w : Nat) (b : IR.Structural.Bounds) (k : Nat) :
    Decidable (Correctness.Structural.IntervalFits w b k) := by
  cases b with
  | mk lo hi => cases hi <;> unfold Correctness.Structural.IntervalFits <;> infer_instance

/-! An ordinary xor field under an explicit family has nonempty inherited heads.
[utest->req~compiler-inherited-realization~1] -/
def core : IR.Inherited.Core 6 := ⟨⟨#v[
  { id := 0, name := "root", origin := .syntheticRoot },
  { id := 1, name := "family", isAbstract := true },
  { id := 2, name := "choice", isAbstract := true, parent := some 1,
    localBounds := ⟨1, .finite 1⟩, groupBounds := ⟨1, .finite 1⟩ },
  { id := 3, name := "left", isAbstract := true, parent := some 2,
    localBounds := ⟨0, .finite 1⟩ },
  { id := 4, name := "right", isAbstract := true, parent := some 2,
    localBounds := ⟨0, .finite 1⟩ },
  { id := 5, name := "instance", parent := some 0, super := some 1,
    localBounds := ⟨1, .finite 1⟩, groupBounds := ⟨1, .finite 1⟩ }], 0⟩,
  #v[false, true, false, false, false, false], #v[0, 2, 3, 4, 4, 1]⟩
def validated : IR.Inherited.Validated 6 :=
  ⟨core, ⟨#v[0, 0, 1, 2, 2, 1], #v[0, 0, 0, 0, 0, 1], #v[false, false, false, false, false, false]⟩,
    by decide, by decide⟩

theorem order_eq : Structural.order validated.layout = [0, 1, 2, 3, 4, 5] := by
  have hc : ∀ a b : Fin 6,
      (validated.layout.certificate.superRank[a] < validated.layout.certificate.superRank[b] ||
        (validated.layout.certificate.superRank[a] == validated.layout.certificate.superRank[b] && a.val ≤ b.val)) =
      decide (a ≤ b) := by decide
  unfold Structural.order
  rw [funext (fun a => funext (hc a))]
  exact List.mergeSort_eq_self (r := (· ≤ ·)) (by decide)

theorem ancestors_eq (d : Fin 6) : ancestors validated d =
    if d = 5 then [5, 1] else [d] := by
  fin_cases d <;> simp [ancestors, ancestorWalk, validated, core, IR.Structural.Core.get]

def observation : Structural.Observation 6 := ⟨[0, 1, 2, 3], 0,
  (fun d => (#v[[0], [1], [2], [3], [], [1]])[d]),
  (fun d => (#v[[], [], [(1, 2)], [(2, 3)], [], [(0, 1)]])[d]), fun _ => []⟩
def instance_ : Instance := ⟨[[0, 1, 2, 3], [0], [1], [2], [3], [], [1]],
  [[[1, 2]], [[2, 3]], [], [[0, 1]]], []⟩
def limits : Structural.Bounds := ⟨(List.range 6).map (fun d => (d, ⟨4, false⟩)), 4, 8⟩
def scopes : List Scope := List.replicate 7 ⟨4, false⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem target_satisfies : Satisfies (target validated scopes 8) instance_ := by
  unfold Satisfies target Structural.target Structural.schema Structural.facts
    Structural.declarationFacts Structural.fieldDeclaration Structural.ownership Structural.setKey
    Structural.head Structural.signatureId groups childHeads
  simp only [Structural.head, Structural.signatureId, order_eq, children, ancestors_eq]
  decide

def compiled : Compiled := ⟨⟨target validated scopes 8,
  target_satisfies.1, target_satisfies.2.1⟩, Structural.nameMap validated.layout, obligations validated⟩

theorem actual_compile : compile validated limits = .ok compiled := by
  have hs : Structural.resolveScopes validated.layout limits = .ok scopes := by
    simp only [Structural.resolveScopes, order_eq]
    rfl
  simp only [compile, hs, bind, Except.bind]
  simp only [Backend.Alloy.check, show limits.bitwidth = 8 from rfl,
    dite_eq_left target_satisfies.1, dite_eq_left target_satisfies.2.1]
  rfl

theorem source_satisfies :
    ∃ o, decode validated instance_ = .ok o ∧ ∃ hr,
      Nonempty (Correctness.Structural.Represents validated.layout
        (Correctness.Structural.realize o hr) instance_) ∧
      Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret core)
        (Correctness.Structural.realize o hr) :=
  compiled_sound validated limits compiled actual_compile instance_ target_satisfies

theorem encode_eq : encode validated observation = instance_ := by
  simp only [encode, Structural.encode, order_eq]
  rfl

theorem decode_eq : decode validated instance_ = .ok observation := by
  rw [← encode_eq]
  exact Correctness.Structural.decode_encode validated.layout observation
    (by unfold Correctness.Structural.TableWellFormed; decide) rfl (by decide)

theorem realized_satisfies :
    Clafer.Semantics.Realization.Satisfies (SemanticsBridge.Inherited.interpret core)
      (Correctness.Structural.realize observation (by decide)) := by
  obtain ⟨o, ho, hr, _, hs⟩ := source_satisfies
  rw [decode_eq] at ho
  cases Except.ok.inj ho
  exact hs

theorem count_fits : CountFits validated
    (Correctness.Structural.realize observation (by decide)) 8 := by
  classical
  have small (P : Correctness.Structural.Objects observation → Prop) :
      Fintype.card {x // P x} < 5 := by
    have h := Fintype.card_subtype_le P
    have hc : Fintype.card (Correctness.Structural.Objects observation) = 4 :=
      Correctness.Structural.objects_card observation
    omega
  have hl : ∀ d : Fin 6, ∀ k : Fin 5,
      Correctness.Structural.IntervalFits 8 (validated.layout.core.get d).localBounds k := by decide
  have hg : ∀ d : Fin 6, ∀ k : Fin 5,
      Correctness.Structural.IntervalFits 8 (validated.core.structural.get d).groupBounds k := by decide
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d c _ p _
    exact hl d ⟨Fintype.card {x // (Correctness.Structural.realize observation (by decide)).contains d p x},
      small _⟩
  · intro d _ p _
    simp [IR.Inherited.Validated.layout, Correctness.Structural.IntervalFits]
  · intro d _ p _
    exact hg d ⟨Fintype.card {x // Clafer.Compile.Groups.ChildObjects
      (SemanticsBridge.Inherited.interpret validated.core).family
      (Correctness.Structural.realize observation (by decide)) d p x}, small _⟩

theorem scope_fits : Correctness.Structural.ObservationScopesFit validated.layout
    compiled.module.raw.command.scopes
    (Correctness.Structural.sourceObservation (Correctness.Structural.realize observation (by decide))) := by
  classical
  intro entry he
  have lengths : ∀ xs ∈ ((Correctness.Structural.sourceObservation
      (Correctness.Structural.realize observation (by decide))).objects ::
      (Structural.order validated.layout).map
        (Correctness.Structural.sourceObservation (Correctness.Structural.realize observation (by decide))).heads),
      xs.length ≤ 4 := by
    intro xs hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [Correctness.Structural.source_object_count, Correctness.Structural.objects_card]; decide
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      rw [Correctness.Structural.source_head_count, Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype_le _).trans (by rw [Correctness.Structural.objects_card]; decide)
  have hc : entry.1 ∈ List.replicate 7 (⟨4, false⟩ : Scope) := List.of_mem_zip he |>.1
  have hc : entry.1 = (⟨4, false⟩ : Scope) := List.eq_of_mem_replicate hc
  simpa [hc] using lengths entry.2 (List.of_mem_zip he).2

theorem completed_source_has_target :
    ∃ i, encode validated (Correctness.Structural.sourceObservation
        (Correctness.Structural.realize observation (by decide))) = i ∧
      Nonempty (Correctness.Structural.Represents validated.layout
        (Correctness.Structural.realize observation (by decide)) i) ∧
      Satisfies compiled.module.raw i :=
  compiled_complete validated limits compiled actual_compile _ realized_satisfies scope_fits count_fits

end ClaferCompiler.Tests.Inherited
