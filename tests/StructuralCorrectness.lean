module

public import tests.StructuralRepresentation
public import ClaferCompiler.Correctness.StructuralCorrectness

@[expose] public section
namespace ClaferCompiler.Tests.StructuralCorrectness
open Backend.Alloy Backend.Alloy.Structural Correctness.Structural
open SemanticsBridge.Structural
open Tests.StructuralAlloy (bagValidated bag_order bagInstance)
open Tests.StructuralRepresentation

/-! Kernel witnesses exercise the general preservation theorems and distinguish
missing upper bounds, collapsed occurrence identities and missing global facts.
[utest->req~compiler-structural-correctness~1] -/

def bagLimits : Structural.Bounds :=
  ⟨[(100, ⟨4, false⟩), (200, ⟨4, false⟩), (300, ⟨4, false⟩)], 4, 5⟩

def bagCompiled : Compiled := ⟨
  ⟨target bagValidated.toLayout (List.replicate 4 ⟨4, false⟩) 5,
    bag_target_satisfies.1, bag_target_satisfies.2.1⟩,
  nameMap bagValidated.toLayout, (facts bagValidated.toLayout).map Prod.fst⟩

theorem bag_compile : compile bagValidated bagLimits = .ok bagCompiled := by
  have hs : resolveScopes bagValidated.toLayout bagLimits = .ok (List.replicate 4 ⟨4, false⟩) := by
    simp only [resolveScopes, bag_order]
    rfl
  simp only [compile, hs, bind, Except.bind]
  simp only [Backend.Alloy.check, show bagLimits.bitwidth = 5 from rfl,
    dite_eq_left bag_target_satisfies.1, dite_eq_left bag_target_satisfies.2.1]
  rfl

theorem bag_source_satisfies :
    Clafer.Semantics.StructuralSatisfies (interpret bagValidated.core)
      (realize bagObservation (by decide)) := by
  obtain ⟨hr, ⟨r⟩⟩ := bag_decoded_representation
  exact represented_sound bagValidated.toLayout _ bagInstance r _ 5 bag_target_satisfies

theorem bag_compiled_sound :
    ∃ o, decode bagValidated.toLayout bagInstance = .ok o ∧ ∃ hr : o.root ∈ o.objects,
      Nonempty (Represents bagValidated.toLayout (realize o hr) bagInstance) ∧
      Clafer.Semantics.StructuralSatisfies (interpret bagValidated.core) (realize o hr) :=
  compiled_sound bagValidated bagLimits bagCompiled bag_compile bagInstance bag_target_satisfies

theorem bag_count_fits : SourceCountFits bagValidated.toLayout
    (realize bagObservation (by decide)) 5 := by
  constructor
  · intro d c _ p _
    have hd : ∀ d, (bagValidated.toLayout.core.get d).localBounds = {} := by decide
    simp [hd, IntervalFits]
  · intro d _ p _
    have hd : ∀ d, (bagValidated.toLayout.core.get d).groupBounds = {} := by decide
    simp [hd, IntervalFits]

theorem bag_scope_fits : ObservationScopesFit bagValidated.toLayout bagCompiled.module.raw.command.scopes
    (sourceObservation (realize bagObservation (by decide))) := by
  classical
  intro entry he
  have lengths : ∀ xs ∈ ((sourceObservation (realize bagObservation (by decide))).objects ::
      (order bagValidated.toLayout).map (sourceObservation (realize bagObservation (by decide))).heads),
      xs.length ≤ 4 := by
    intro xs hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [source_object_count, objects_card]
      decide
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      rw [source_head_count, Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype_le _).trans (by rw [objects_card]; decide)
  have hc : entry.1 ∈ List.replicate 4 (⟨4, false⟩ : Scope) := List.of_mem_zip he |>.1
  have hc : entry.1 = (⟨4, false⟩ : Scope) := List.eq_of_mem_replicate hc
  simpa [hc] using lengths entry.2 (List.of_mem_zip he).2

theorem bag_compiled_complete :
    ∃ i, encode bagValidated.toLayout (sourceObservation (realize bagObservation (by decide))) = i ∧
      Nonempty (Represents bagValidated.toLayout (realize bagObservation (by decide)) i) ∧
      Satisfies bagCompiled.module.raw i :=
  compiled_complete bagValidated bagLimits bagCompiled bag_compile _ bag_source_satisfies
    bag_scope_fits bag_count_fits

/-- The same concrete bag remains a source model under bijective relabelling. -/
theorem bag_renamed_sound :
    Clafer.Semantics.StructuralSatisfies (interpret bagValidated.core)
      ((realize bagObservation (by decide)).rename (Fintype.equivFin (Objects bagObservation))) := by
  obtain ⟨hr, ⟨r⟩⟩ := bag_decoded_representation
  exact represented_sound bagValidated.toLayout _ bagInstance (r.rename _) _ 5 bag_target_satisfies

def optionalCore : IR.Structural.Core 2 := ⟨#v[
  { id := 100, name := "root", origin := .syntheticRoot },
  { id := 200, name := "child", parent := some 0, localBounds := ⟨0, .finite 1⟩ }], 0⟩
def optionalValidated : IR.Structural.Validated 2 :=
  ⟨optionalCore, ⟨#v[0, 1], #v[0, 0], #v[false, false]⟩, by decide, by decide⟩
theorem optional_order : order optionalValidated.toLayout = [0, 1] := by
  have hc : ∀ a b : Fin 2,
      (optionalValidated.toLayout.certificate.superRank[a] < optionalValidated.toLayout.certificate.superRank[b] ||
        (optionalValidated.toLayout.certificate.superRank[a] == optionalValidated.toLayout.certificate.superRank[b] && a.val ≤ b.val)) =
      decide (a ≤ b) := by decide
  unfold order
  rw [funext (fun a => funext (hc a))]
  exact List.mergeSort_eq_self (r := (· ≤ ·)) (by decide)

def optionalObservation : Observation 2 := ⟨[0, 1, 2], 0,
  fun d => if d == 0 then [0] else [1, 2],
  fun d => if d == 0 then [] else [(0, 1), (0, 2)], fun _ => []⟩

def omitFact (v : IR.Structural.Layout n) (scopes : List Scope) (w : Nat)
    (tag : Obligation) : Module :=
  { target v scopes w with facts := ((facts v).filter fun f => f.1 != tag).map Prod.snd }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem omitted_upper_bound_accepts :
    Satisfies (omitFact optionalValidated.toLayout (List.replicate 3 ⟨4, false⟩) 5 (.localBounds 200))
      (encode optionalValidated.toLayout optionalObservation) := by
  unfold Satisfies omitFact target schema facts declarationFacts fieldDeclaration ownership setKey encode
  simp only [allocation_head_apply, allocation_contains_apply, allocation_deref_apply,
    allocation_head, allocation_fields, allocation_signatures]
  unfold head signatureId
  simp only [optional_order]
  decide

theorem omitted_upper_bound_source_rejects :
    ¬ Clafer.Semantics.StructuralSatisfies (interpret optionalCore)
      (realize optionalObservation (by decide)) := by
  intro h
  have hm := h.2.2.2.2.2.2.2.1 1 0 rfl ⟨0, by decide⟩ (by change (0 : Nat) ∈ [0]; decide)
  change DPGraph.Predicates.InRange ⟨0, .finite 1⟩ {x : Objects optionalObservation // (0, x.val) ∈ [(0, 1), (0, 2)]} at hm
  rw [DPGraph.Predicates.inRange_card] at hm
  have hc : Fintype.card {x : Objects optionalObservation //
      (0, x.val) ∈ [(0, 1), (0, 2)]} = 2 := by decide
  change DPGraph.Predicates.CountInRange ⟨0, .finite 1⟩ _ at hm
  rw [hc] at hm
  exact (by decide : ¬DPGraph.Predicates.CountInRange ⟨0, .finite 1⟩ 2) hm

def leafCore : IR.Structural.Core 2 := ⟨#v[
  { id := 100, name := "root", origin := .syntheticRoot },
  { id := 200, name := "abstract", isAbstract := true }], 0⟩
def leafValidated : IR.Structural.Validated 2 :=
  ⟨leafCore, ⟨#v[0, 0], #v[0, 0], #v[false, false]⟩, by decide, by decide⟩
theorem leaf_order : order leafValidated.toLayout = [0, 1] := by
  have hc : ∀ a b : Fin 2,
      (leafValidated.toLayout.certificate.superRank[a] < leafValidated.toLayout.certificate.superRank[b] ||
        (leafValidated.toLayout.certificate.superRank[a] == leafValidated.toLayout.certificate.superRank[b] && a.val ≤ b.val)) =
      decide (a ≤ b) := by decide
  unfold order
  rw [funext (fun a => funext (hc a))]
  exact List.mergeSort_eq_self (r := (· ≤ ·)) (by decide)

def leafObservation : Observation 2 := ⟨[0, 1], 0,
  fun d => if d == 0 then [0] else [1], fun _ => [], fun _ => []⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem omitted_abstract_cover_accepts :
    Satisfies (omitFact leafValidated.toLayout (List.replicate 3 ⟨4, false⟩) 5 (.abstractCover 200))
      (encode leafValidated.toLayout leafObservation) := by
  unfold Satisfies omitFact target schema facts declarationFacts fieldDeclaration ownership setKey encode
  simp only [allocation_head_apply, allocation_contains_apply, allocation_deref_apply,
    allocation_head, allocation_fields, allocation_signatures]
  unfold head signatureId
  simp only [leaf_order]
  decide

theorem omitted_abstract_cover_source_rejects :
    ¬ Clafer.Semantics.StructuralSatisfies (interpret leafCore)
      (realize leafObservation (by decide)) := by
  intro h
  obtain ⟨c, hc, _⟩ := (h.2.2.2.1 1 rfl).1 ⟨1, by decide⟩ (by change (1 : Nat) ∈ [1]; decide)
  have hn : ∀ c : Fin 2, (interpret leafCore).family.super c = none := by decide
  simp [hn] at hc

def collapsedBag : Observation 3 :=
  { bagObservation with
    objects := [0, 1, 2]
    heads := fun d => if d == 2 then [2] else bagObservation.heads d
    containment := fun d => if d == 2 then [(0, 2)] else bagObservation.containment d
    dereference := fun d => if d == 2 then [(2, 1)] else bagObservation.dereference d }

/-- Even if an unconstrained bag quotient still satisfies a target, it cannot
represent the original source: the concrete object bijection detects the loss. -/
theorem collapsed_bag_not_representation :
    ¬ Nonempty (Represents bagValidated.toLayout (realize bagObservation (by decide))
      (encode bagValidated.toLayout collapsedBag)) := by
  rintro ⟨r⟩
  have he := Fintype.card_congr r.objects
  change Fintype.card (Objects bagObservation) = Fintype.card (Objects collapsedBag) at he
  rw [objects_card, objects_card] at he
  have hne : bagObservation.objects.toFinset.card ≠ collapsedBag.objects.toFinset.card := by decide
  exact hne he

end ClaferCompiler.Tests.StructuralCorrectness
