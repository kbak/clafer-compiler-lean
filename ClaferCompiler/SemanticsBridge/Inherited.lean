module

public import ClaferCompiler.IR.Inherited
public import ClaferCompiler.SemanticsBridge.Structural
public import Clafer.Semantics.RealizationCompatibility

@[expose] public section
/-! [proof->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.SemanticsBridge.Inherited
open IR.Inherited

/-- Interpret the original effective table and its independent authored flag. -/
def interpret (m : Core n) : Clafer.Semantics.Realization.Core n where
  toEffectiveCore := Structural.interpret m.structural
  explicitAbstract d := m.explicitAbstract[d]

theorem selected (v : Validated n) : (interpret v.core).Selected := by
  rcases v.selectedChecked with ⟨explicit, parentless, supers, refs, subrank, parentrank, _⟩
  refine ⟨explicit, parentless, ?_, ?_, ⟨fun d => v.core.realizationRank[d], subrank, parentrank⟩⟩
  · intro d c hc
    exact ⟨(supers d c hc).1, by simp [interpret, Structural.interpret, Structural.reference, (supers d c hc).2.1]⟩
  · intro d t ht
    exact (refs d t (by simpa [interpret, Structural.interpret] using ht)).1

theorem wellFormed (v : Validated n) : (interpret v.core).toEffectiveCore.WellFormed := by
  rcases v.coreChecked with ⟨ids, origins, root, parents, supers, bounds, parentless⟩
  rcases v.selectedChecked with ⟨explicit, _, sub, _, _, _, allowed, primitive, unique, nested⟩
  refine ⟨?_, ?_, ?_⟩
  · refine {
      root_origin := by simpa [interpret, Structural.interpret] using origins
      root_shape := by simpa [interpret, Structural.interpret] using root
      parent_rank := ⟨fun d => v.certificate.parentRank[d], parents⟩
      super_rank := ⟨fun d => v.certificate.superRank[d], supers⟩
      valid_bounds := by intro d; simpa [interpret, Structural.interpret] using (bounds d).1
      parentless_abstract := parentless
      nested_abstract := nested
      primitive_shape := ?_
      unique_primitive := ?_
      inheritance_kind := ?_
      inheritance_parent := ?_ }
    · intro d dom hd
      rcases allowed d with ho | ho | ho
      · simp [interpret, Structural.interpret, Structural.origin, ho] at hd
      · simp [interpret, Structural.interpret, Structural.origin, ho] at hd
      · simpa [interpret, Structural.interpret] using primitive d ho
    · intro d e dom hd he
      have int (c : Fin n) (hc : (interpret v.core).family.origin c = .primitive dom) :
          (v.core.structural.get c).origin = .integer := by
        rcases allowed c with ho | ho | ho
        · simp [interpret, Structural.interpret, Structural.origin, ho] at hc
        · simp [interpret, Structural.interpret, Structural.origin, ho] at hc
        · exact ho
      exact unique d e (int d hd) (int e he)
    · intro d c hc
      have h := sub d c hc
      simp [interpret, Structural.interpret, Structural.reference, h.2.1, h.2.2,
        Clafer.MCS.ReferenceTo.kind, Clafer.Kind.CanExtend]
    · intro d c hc hn
      exact (hn (explicit c (sub d c hc).1).2).elim
  · intro d e he
    exact ids d e (by simpa [interpret, Structural.interpret] using he)
  · intro d
    simpa [interpret, Structural.interpret] using (bounds d).2

/-- The allocation projection changes only abstract/group policy, not identities,
root, edges, origins, names or local multiplicities. -/
theorem layout_local {U : Type} (m : Core n)
    (s : Clafer.Semantics.Configuration (Fin n) U) :
    s.LocalConditions (Structural.interpret m.layoutCore) ↔
      s.LocalConditions (interpret m).toEffectiveCore := by
  simp only [Clafer.Semantics.Configuration.LocalConditions,
    Clafer.Semantics.Configuration.Inherits, Clafer.Semantics.Configuration.Parents,
    Clafer.Semantics.Configuration.References, Clafer.Semantics.Configuration.Keys,
    Clafer.Semantics.Configuration.Multiplicities, interpret, Structural.interpret, layout_get]

theorem layout_groups {U : Type} (m : Core n)
    (s : Clafer.Semantics.Configuration (Fin n) U) :
    s.Groups (Structural.interpret m.layoutCore) := by
  intro d _ p _
  simp only [Structural.interpret, layout_get, Structural.bounds]
  exact ⟨⟨Function.Embedding.ofIsEmpty⟩, trivial⟩

/-- Explicit-family projection preserves every nongroup structural clause.
The actual inherited group obligation is kept separate, not assumed away. -/
theorem satisfies_iff {U : Type} (m : Core n)
    (s : Clafer.Semantics.Configuration (Fin n) U) :
    Clafer.Semantics.Realization.Satisfies (interpret m) s ↔
      Clafer.Semantics.StructuralSatisfies (Structural.interpret m.layoutCore) s ∧
        Clafer.Semantics.Realization.Groups (interpret m) s := by
  have ht : s.Typed (Structural.interpret m.layoutCore) ↔ s.Typed (interpret m).toEffectiveCore := by
    simp only [Clafer.Semantics.Configuration.Typed, interpret, Structural.interpret, layout_get]
  have hr : s.Rooted (Structural.interpret m.layoutCore) ↔ s.Rooted (interpret m).toEffectiveCore := Iff.rfl
  have ha : s.Abstracts (Structural.interpret m.layoutCore) ↔
      Clafer.Semantics.Realization.Abstracts (interpret m) s := by
    simp only [Clafer.Semantics.Configuration.Abstracts, Clafer.Semantics.Realization.Abstracts,
      interpret, Structural.interpret, layout_get]
  have hd : s.DeclarationDisjoint (Structural.interpret m.layoutCore) ↔
      s.DeclarationDisjoint (interpret m).toEffectiveCore := by
    simp only [Clafer.Semantics.Configuration.DeclarationDisjoint, Clafer.Semantics.EffectiveCore.Ancestor,
      interpret, Structural.interpret, layout_get]
  rw [Clafer.Semantics.Configuration.structural_split]
  unfold Clafer.Semantics.Configuration.GlobalConditions
  rw [ht, hr, ha, hd, layout_local]
  have hg := layout_groups m s
  unfold Clafer.Semantics.Realization.Satisfies
  tauto

/-- On the exact admitted M1 overlap, the new meaning is the old meaning.
The flag equality is derived from the guards, not supplied by the caller. -/
theorem m1_compatibility {U : Type} (v : Validated n) (old : IR.Structural.Validated n)
    (same : v.core.structural = old.core) (s : Clafer.Semantics.Configuration (Fin n) U) :
    Clafer.Semantics.Realization.Satisfies (interpret v.core) s ↔
      Clafer.Semantics.StructuralSatisfies (Structural.interpret old.core) s := by
  have hs : (interpret v.core).toEffectiveCore.Supported := by
    simpa only [interpret, same] using (Structural.validated_domain old).2
  have h := Clafer.Semantics.Realization.guarded_compatibility (interpret v.core) s hs
    (Clafer.Semantics.Realization.guarded_flags _ (selected v) hs) (fun _ => rfl)
  simpa only [interpret, same] using h

end ClaferCompiler.SemanticsBridge.Inherited
