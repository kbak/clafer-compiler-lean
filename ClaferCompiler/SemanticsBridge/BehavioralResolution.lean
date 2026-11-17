module

public import ClaferCompiler.Frontend.BehavioralResolution
public import ClaferCompiler.SemanticsBridge.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.BehavioralResolution
open Frontend Frontend.Resolution Frontend.BehavioralResolution

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem sourceRow_of_user (doc : Document) (e : BehavioralResolution.Elaborated doc)
    (i : Fin e.count) (hu : (e.candidate.core.get i).origin = .user) :
    BehavioralResolution.SourceRow doc e.candidate i e.aggregate := by
  have h := e.correspondence.2.2.2.1 i
  have hr := e.admitted.checked.1.2.1 i
  rw [e.sameCore] at hr
  split at h
  · rename_i hi
    have := hr.mpr hi
    change (e.candidate.core.get i).origin = .syntheticRoot at this
    rw [hu] at this; cases this
  · simpa only [hu, reduceCtorEq, ↓reduceIte] using h

theorem sourceRow_of_path (doc : Document) (e : BehavioralResolution.Elaborated doc)
    (i : Fin e.count) (path : Path) (hp : e.candidate.paths[i] = some path) :
    BehavioralResolution.SourceRow doc e.candidate i e.aggregate := by
  have h := e.correspondence.2.2.2.1 i
  split at h
  · simp_all
  · split at h
    · simp_all
    · exact h

/-- Every authored declaration occurs, with the original path and constraints.
The proof covers manually supplied trees as well as parser-produced trees. -/
theorem source_coverage (doc : Document) (e : BehavioralResolution.Elaborated doc) {p : Path}
    (h : Resolution.Declared doc p) : ∃ i : Fin e.count, e.candidate.paths[i] = some p := by
  induction h with
  | root k hk => exact e.correspondence.2.2.1 k hk
  | @child p _ k hk ih =>
    obtain ⟨i, hi⟩ := ih
    have hs := sourceRow_of_path doc e i p hi
    unfold BehavioralResolution.SourceRow at hs
    rw [hi] at hs
    split at hs
    · rename_i hh
      simp_all only [Option.some.injEq]
      subst p
      exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2 k hk
    · contradiction

/-- The existing independent default relation applies also to nested authored
abstracts and concrete supers; neither defaulting nor this proof requires truth. -/
theorem defaults (doc : Document) (e : BehavioralResolution.Elaborated doc) (i : Fin e.count)
    (hu : (e.candidate.core.get i).origin = .user) (historical : e.aggregate = false) :
    Clafer.Defaults (Resolution.declaration doc e.candidate i)
      ((e.candidate.core.get i).parent.map (Resolution.declaration doc e.candidate))
      ((e.candidate.core.get i).super.map (Resolution.declaration doc e.candidate)) := by
  have hs := sourceRow_of_user doc e i hu
  unfold BehavioralResolution.SourceRow at hs
  split at hs
  · rename_i path h hp hh
    obtain ⟨_, _, _, _, _, ha, _, _, _, hg, _, hl, hab, _⟩ := hs
    unfold Clafer.Defaults Resolution.declaration explicitAbstract
    simp only [hh, Option.map_some, Option.getD_some, Option.bind_some, ha]
    constructor
    · rw [hg]
      cases h.group <;> cases (e.candidate.core.get i).super <;> rfl
    constructor
    · rw [hl]
      simp only [localBounds, historical, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases h.cardinality <;> cases (e.candidate.core.get i).parent <;>
        simp [Function.comp_def, Resolution.group_default, Structural.bounds, Clafer.one]
    · rw [hab]
      cases (e.candidate.core.get i).parent <;> rfl
  · contradiction


-- [proof->req~compiler-abstract-multiplicity~1]
/-- Validated aggregate rows retain the authored interval, while their effective
local slot is unrestricted. Invalid authored bounds cannot disappear in lowering. -/
theorem aggregate_bounds (doc : Document) (e : BehavioralResolution.Elaborated doc)
    (selected : e.aggregate = true) (i : Fin e.count)
    (abstract : e.admitted.core.authoredAbstract[i] = true) :
    (e.admitted.core.structural.get i).localBounds = {} ∧
      (((e.admitted.core.structural.get i).authored.bind (·.localBounds)).getD {}).Valid := by
  have valid := (e.admitted.checked.1.2.2.2.2.2.1 i).1
  rw [e.sameCore] at abstract valid ⊢
  simp only [core] at abstract
  unfold explicitAbstract at abstract
  cases header : e.candidate.header doc i with
  | none => simp [header] at abstract
  | some h =>
    have abs : h.abstractToken.isSome = true := by simpa [header] using abstract
    have path : ∃ p, e.candidate.paths[i] = some p := by
      cases hp : e.candidate.paths[i] with
      | none => simp [Candidate.header, hp] at header
      | some p => exact ⟨p, rfl⟩
    obtain ⟨p, hp⟩ := path
    have row := sourceRow_of_path doc e i p hp
    simp only [BehavioralResolution.SourceRow, hp, header] at row
    obtain ⟨_, _, _, _, _, authored, _, _, _, _, _, effective, _⟩ := row
    change (e.candidate.core.get i).localBounds.Valid at valid
    change (e.candidate.core.get i).localBounds = {} ∧
      (((e.candidate.core.get i).authored.bind (·.localBounds)).getD {}).Valid
    rw [effective, authored]
    simp only [Option.bind_some]
    rw [effective] at valid
    simp only [localBounds, selected, abs, Bool.true_and] at valid ⊢
    by_cases authoredValid : ((h.cardinality.map cardBounds).getD {}).Valid
    · simp [authoredValid]
    · simp only [authoredValid, decide_false, Bool.false_eq_true, ↓reduceIte] at valid
      cases card : h.cardinality with
      | none => simp [card, IR.Structural.Bounds.Valid] at authoredValid
      | some a => exact False.elim (authoredValid (by simpa [card] using valid))

theorem wellFormed (doc : Document) (e : BehavioralResolution.Elaborated doc) :
    (BehavioralStructural.interpret (Frontend.BehavioralResolution.core doc e.candidate)).WellFormed := by
  rw [← e.sameCore]
  exact BehavioralStructural.validated_wellFormed e.admitted

end ClaferCompiler.SemanticsBridge.BehavioralResolution
