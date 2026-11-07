module

public import ClaferCompiler.Frontend.Behavioral.Elaborate
public import ClaferCompiler.SemanticsBridge.BehavioralResolution
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Frontend Frontend.Resolution
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Primitive completion's shape premises follow from the source/table
correspondence; they are not additional restrictions on authored models. -/
theorem resolution_primitiveShape (doc : Frontend.Document)
    (e : Frontend.BehavioralResolution.Elaborated doc) : PrimitiveShape e.admitted := by
  have checks := e.admitted.checked.1
  rw [e.sameCore] at checks
  change IR.Structural.coreChecks e.candidate.core e.admitted.certificate at checks
  unfold PrimitiveShape
  rw [e.sameCore]
  change ∀ p, (e.candidate.core.get p).origin = .integer → _
  intro p hp
  have pne : p ≠ e.candidate.core.root := by
    intro he
    have hr := (checks.2.1 p).mpr he
    rw [hp] at hr
    cases hr
  have prow := e.correspondence.2.2.2.1 p
  simp only [pne, hp, ↓reduceIte] at prow
  obtain ⟨path, _, _, _, _, _, _, group, localBounds, _, _⟩ := prow
  have root := e.correspondence.2.2.2.1 e.candidate.core.root
  simp only at root
  refine ⟨?_, localBounds, group, root.2.2.2.1, ?_, ?_⟩
  · simp [Frontend.BehavioralResolution.core, explicitAbstract, Candidate.header, path]
  · intro d hd
    change (e.candidate.core.get d).super = some p at hd
    have row := e.correspondence.2.2.2.1 d
    by_cases dr : d = e.candidate.core.root
    · subst d
      have hs := checks.2.2.1.2.2.1
      rw [hs] at hd
      cases hd
    · simp only [dr, ↓reduceIte] at row
      split at row
      · have hs := row.2.2.2.1
        rw [hs] at hd
        cases hd
      · unfold Frontend.BehavioralResolution.SourceRow at row
        split at row
        · have hs := row.2.2.2.2.2.2.2.1
          unfold Frontend.BehavioralResolution.SuperRule at hs
          rw [hd] at hs
          split at hs <;> simp_all
        · contradiction
  · intro d hd
    change (e.candidate.core.get d).parent = some p at hd
    have row := e.correspondence.2.2.2.1 d
    by_cases dr : d = e.candidate.core.root
    · subst d
      have hs := checks.2.2.1.1
      rw [hs] at hd
      cases hd
    · simp only [dr, ↓reduceIte] at row
      split at row
      · have he := Option.some.inj (row.2.2.1.symm.trans hd)
        exact pne he.symm
      · unfold Frontend.BehavioralResolution.SourceRow at row
        split at row
        · have parent := row.2.2.2.2.2.2.1
          split at parent
          · split at parent
            · rw [parent] at hd
              cases hd
            · exact pne (Option.some.inj (hd.symm.trans parent))
          · obtain ⟨q, hq, pathq⟩ := parent
            have he := Option.some.inj (hq.symm.trans hd)
            rw [he, path] at pathq
            cases pathq
        · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem frontend_primitive (e : Frontend.Behavioral.Elaborated source) :
    PrimitiveShape e.model.structural ∧
      ∃ p, (e.model.structural.core.structural.get p).origin = .integer := by
  refine ⟨resolution_primitiveShape _ e.declarations.resolved, ?_⟩
  have h := e.declarations.integerDomain
  simpa [Frontend.Behavioral.Elaborated.model, e.declarations.resolved.sameCore,
    Frontend.BehavioralResolution.core] using h

end ClaferCompiler.Correctness.Behavioral.Full
