module

public import ClaferCompiler.Backend.Alloy.Inherited
public import ClaferCompiler.SemanticsBridge.Inherited
public import ClaferCompiler.Correctness.StructuralCorrectness

@[expose] public section
/-! [proof->req~compiler-inherited-realization~1] -/
namespace ClaferCompiler.Correctness.Inherited
open Backend.Alloy Backend.Alloy.Inherited IR.Inherited

/-- Checked rank fuel never truncates a source super path. -/
theorem mem_ancestorWalk (v : Validated n) (fuel : Nat) (d a : Fin n)
    (bound : v.certificate.superRank[d] ≤ fuel) :
    a ∈ ancestorWalk v.core.structural fuel d ↔
      Clafer.Compile.Groups.Ancestor (SemanticsBridge.Inherited.interpret v.core).family d a := by
  induction fuel generalizing d with
  | zero =>
    change a ∈ [d] ↔ _
    simp only [List.mem_singleton]
    constructor
    · rintro rfl; exact .refl
    · intro ha
      rcases ha.cases_head with he | ⟨p, hp, _⟩
      · exact he.symm
      · have h := v.coreChecked.2.2.2.2.1 d p hp
        omega
  | succ fuel ih =>
    change a ∈ d :: (match (v.core.structural.get d).super with
      | none => [] | some p => ancestorWalk v.core.structural fuel p) ↔ _
    constructor
    · intro ha
      rcases List.mem_cons.mp ha with he | ha
      · subst a; exact .refl
      · split at ha
        · cases ha
        · rename_i p hp
          have smaller := v.coreChecked.2.2.2.2.1 d p hp
          have step : Clafer.Compile.Groups.Ancestor
              (SemanticsBridge.Inherited.interpret v.core).family d p :=
            Relation.ReflTransGen.single hp
          exact step.trans ((ih p (by omega)).mp ha)
    · intro ha
      rcases ha.cases_head with he | ⟨p, hp, path⟩
      · exact List.mem_cons.mpr (Or.inl he.symm)
      · apply List.mem_cons.mpr
        right
        change (v.core.structural.get d).super = some p at hp
        rw [hp]
        have smaller := v.coreChecked.2.2.2.2.1 d p hp
        exact (ih p (by omega)).mpr path

/-- The executable inventory is exactly the independent reflexive super path. -/
theorem mem_ancestors (v : Validated n) (d a : Fin n) :
    a ∈ ancestors v d ↔
      Clafer.Compile.Groups.Ancestor (SemanticsBridge.Inherited.interpret v.core).family d a :=
  mem_ancestorWalk v _ d a (Nat.le_refl _)

theorem mem_children (v : Validated n) (d c : Fin n) :
    c ∈ children v d ↔ ∃ a,
      Clafer.Compile.Groups.Ancestor (SemanticsBridge.Inherited.interpret v.core).family d a ∧
        (v.core.structural.get c).parent = some a := by
  simp [children, List.mem_flatMap, mem_ancestors, Backend.Alloy.Structural.child_inventory]

theorem compile_output (v : Validated n) (b : Backend.Alloy.Structural.Bounds) (c : Compiled)
    (h : compile v b = .ok c) :
    ∃ scopes, Backend.Alloy.Structural.resolveScopes v.layout b = .ok scopes ∧
      c.module.raw = target v scopes b.bitwidth ∧
      c.declarations = Backend.Alloy.Structural.nameMap v.layout ∧ c.obligations = obligations v := by
  unfold compile at h
  cases hs : Backend.Alloy.Structural.resolveScopes v.layout b with
  | error e => simp [hs, bind, Except.bind] at h
  | ok scopes =>
    simp only [hs, bind, Except.bind] at h
    cases hc : check (target v scopes b.bitwidth) with
    | error e => cases e <;> simp [hc] at h
    | ok checked =>
      simp only [hc, Except.ok.injEq] at h
      subst c
      refine ⟨scopes, rfl, ?_, rfl, rfl⟩
      unfold check at hc
      split at hc
      · split at hc
        · cases hc; rfl
        · cases hc
      · cases hc

end ClaferCompiler.Correctness.Inherited
