module

public import ClaferCompiler.Frontend.BehavioralResolution
public import ClaferCompiler.SemanticsBridge.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.BehavioralResolution
open Frontend Frontend.Resolution Frontend.BehavioralResolution

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem sourceRow_of_user (doc : Document) (e : BehavioralResolution.Elaborated doc)
    (i : Fin e.count) (hu : (e.candidate.core.get i).origin = .user) :
    BehavioralResolution.SourceRow doc e.candidate i := by
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
    BehavioralResolution.SourceRow doc e.candidate i := by
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
    (hu : (e.candidate.core.get i).origin = .user) :
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
      cases h.cardinality <;> cases (e.candidate.core.get i).parent <;>
        simp [Function.comp_def, Resolution.group_default, Structural.bounds, Clafer.one]
    · rw [hab]
      cases (e.candidate.core.get i).parent <;> rfl
  · contradiction

theorem wellFormed (doc : Document) (e : BehavioralResolution.Elaborated doc) :
    (BehavioralStructural.interpret (Frontend.BehavioralResolution.core doc e.candidate)).WellFormed := by
  rw [← e.sameCore]
  exact BehavioralStructural.validated_wellFormed e.admitted

end ClaferCompiler.SemanticsBridge.BehavioralResolution
