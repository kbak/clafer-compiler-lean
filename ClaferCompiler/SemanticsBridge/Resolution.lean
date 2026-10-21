module

public import ClaferCompiler.Frontend.Resolve
public import ClaferCompiler.SemanticsBridge.Structural
public import Clafer.Semantics.Realization

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Resolution
open Frontend Frontend.Resolution IR.Structural

/-- Exact interpretation of retained keyword/numeric provenance. -/
def group : Group → Clafer.GroupCard
  | .bounds r => .bounds (Structural.bounds r)
  | .xor => .xor | .or => .or | .mux => .mux | .opt => .opt

@[simp] theorem group_range (g : Group) : (group g).range = Structural.bounds g.range := by
  cases g <;> rfl

@[simp] theorem group_default (g : Group) :
    (group g).childDefault = Structural.bounds g.childDefault := by
  cases g <;> rfl

/-- Interpretation uses original authored flags, never reconstructs them from
an erased effective abstractness bit. -/
def interpret (doc : Document) (c : Candidate n) : Clafer.Semantics.Realization.Core n where
  toEffectiveCore := Structural.interpret c.core
  explicitAbstract := explicitAbstract doc c

/-- Kernel-checked success statement for all accepted source documents. -/
theorem elaborate_correspondence (doc : Document) (e : Elaborated doc)
    (_h : elaborate doc = .ok e) : Elaboration doc e.candidate := e.correspondence

theorem sourceRow_of_path (doc : Document) (e : Elaborated doc) (i : Fin e.count)
    (path : Path) (hp : e.candidate.paths[i] = some path) : SourceRow doc e.candidate i := by
  have h := e.correspondence.2.2.2.2.1 i
  split at h
  · simp_all
  · split at h
    · simp_all
    · exact h

theorem sourceRow_of_user (doc : Document) (e : Elaborated doc) (i : Fin e.count)
    (hu : (e.candidate.core.get i).origin = .user) : SourceRow doc e.candidate i := by
  have h := e.correspondence.2.2.2.2.1 i
  have hr := e.correspondence.1.2.1 i
  split at h
  · rename_i hi
    have := hr.mpr hi
    rw [hu] at this
    cases this
  · simp only [hu, reduceCtorEq, ↓reduceIte] at h
    exact h

/-- Independent grammar occurrence relation. Constraints occupy indices but are
not declarations. Every finite declaration path is covered, including descendants. -/
inductive Declared (doc : Document) : Path → Prop where
  | root (k : Fin doc.elements.length) (h : isDeclaration doc.elements[k] = true) :
      Declared doc [k.val]
  | child {p : Path} (parent : Declared doc p)
      (k : Fin ((childrenAt doc p).getD []).length)
      (h : isDeclaration (((childrenAt doc p).getD [])[k]) = true) :
      Declared doc (p ++ [k.val])

theorem source_coverage (doc : Document) (e : Elaborated doc) {p : Path}
    (h : Declared doc p) : ∃ i : Fin e.count, e.candidate.paths[i] = some p := by
  induction h with
  | root k hk => exact e.correspondence.2.2.2.1 k hk
  | @child p _ k hk ih =>
    obtain ⟨i, hi⟩ := ih
    have hs := sourceRow_of_path doc e i p hi
    unfold SourceRow at hs
    rw [hi] at hs
    split at hs
    · rename_i hh
      simp_all only [Option.some.injEq]
      subst p
      exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2 k hk
    · contradiction

/-- Separate syntax declaration interpretation for the upstream Defaults relation. -/
def declaration (doc : Document) (c : Candidate n) (i : Fin n) : Clafer.Declaration where
  id := ⟨(c.core.get i).id⟩
  name := (c.core.get i).name
  origin := Structural.origin (c.core.get i).origin
  reference := match (c.core.get i).reference with
    | .basic => .basic | .set t => .set ⟨(c.core.get t).id⟩ | .bag t => .bag ⟨(c.core.get t).id⟩
  super := (c.core.get i).super.map (fun j => ⟨(c.core.get j).id⟩)
  authoredAbstract := explicitAbstract doc c i
  isAbstract := (c.core.get i).isAbstract
  multiplicity := ⟨((c.core.get i).authored.bind (·.localBounds)).map Structural.bounds,
    Structural.bounds (c.core.get i).localBounds⟩
  group := ⟨((c.header doc i).bind (·.group)).map (group ∘ authoredGroup), group c.groups[i]⟩

theorem defaults (doc : Document) (e : Elaborated doc) (i : Fin e.count)
    (hu : (e.candidate.core.get i).origin = .user) :
    Clafer.Defaults (declaration doc e.candidate i)
      ((e.candidate.core.get i).parent.map (declaration doc e.candidate))
      ((e.candidate.core.get i).super.map (declaration doc e.candidate)) := by
  have hs := sourceRow_of_user doc e i hu
  unfold SourceRow at hs
  split at hs
  · rename_i path h hp hh
    obtain ⟨_, _, _, _, _, ha, _, _, _, hg, _, hl, hab, _⟩ := hs
    unfold Clafer.Defaults declaration explicitAbstract
    simp only [hh, Option.map_some, Option.getD_some, Option.bind_some, ha]
    constructor
    · rw [hg]
      cases h.group <;> cases (e.candidate.core.get i).super <;> rfl
    constructor
    · rw [hl]
      cases h.cardinality <;> cases (e.candidate.core.get i).parent <;>
        simp [Function.comp_def, group_default, Structural.bounds, Clafer.one]
    · rw [hab]
      cases (e.candidate.core.get i).parent <;> rfl
  · contradiction

theorem structural_checks (doc : Document) (e : Elaborated doc) :
    StructuralChecks doc e.candidate := e.correspondence.2.2.2.2.2.2.2.2.2

theorem resolves_unique (doc : Document) (e : Elaborated doc) (context : Path)
    (super : Bool) (name : String) (i j : Fin e.count)
    (hi : Resolves doc e.candidate context super name i)
    (hj : Resolves doc e.candidate context super name j) : i = j := by
  unfold Resolves at hi hj
  split at hi
  · split at hj
    · exact (structural_checks doc e).2.2.1 i j hi.2 hj.2
    · contradiction
  · split at hj
    · contradiction
    · have a := hi.2 j hj.1
      have b := hj.2 i hi.1
      exact (a.2 (Nat.le_antisymm a.1 b.1)).symm

theorem selected (doc : Document) (e : Elaborated doc) : (interpret doc e.candidate).Selected := by
  have hs := structural_checks doc e
  have he := e.correspondence
  refine ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro d s h
    exact ⟨hs.2.2.2.2.2.2 d s h, by
      change Structural.reference (e.candidate.core.get s).reference = .basic
      rw [(he.2.2.2.2.2.2.1 d s h).2.2.1]
      rfl⟩
  · intro d t h
    change (Structural.reference (e.candidate.core.get d).reference).target = some t at h
    rw [Structural.reference_target] at h
    exact (he.2.2.2.2.2.2.2.1 d t h).1
  · refine ⟨fun d => e.candidate.realizationRank[d], ?_, ?_⟩
    · intro d c _ h
      exact (he.2.2.2.2.2.2.1 c d h).2.2.2.2
    · intro d p _ h
      exact he.2.2.2.2.2.2.2.2.1 d p h

/-- The selected frontend produces an independently well-formed effective core,
including primitive and inherited-field obligations absent from the M1 guard. -/
theorem wellFormed (doc : Document) (e : Elaborated doc) :
    (interpret doc e.candidate).toEffectiveCore.WellFormed := by
  let c := e.candidate
  have hc := (Structural.coreChecks_iff c.core c.certificate).mp e.correspondence.1
  have hs := structural_checks doc e
  have hi := e.correspondence.2.2.2.2.2.2.1
  refine ⟨?_, hc.1, fun d => (hc.2.2.2.2.2.1 d).2⟩
  refine {
    root_origin := hc.2.1
    root_shape := hc.2.2.1
    parent_rank := ⟨_, hc.2.2.2.1⟩
    super_rank := ⟨_, hc.2.2.2.2.1⟩
    valid_bounds := fun d => (hc.2.2.2.2.2.1 d).1
    parentless_abstract := hc.2.2.2.2.2.2
    nested_abstract := hs.2.2.2.1
    primitive_shape := ?_
    unique_primitive := ?_
    inheritance_kind := ?_
    inheritance_parent := ?_ }
  · intro d dom hd
    change Structural.origin (c.core.get d).origin = .primitive dom at hd
    rcases hs.1 d with h | h | h
    · rw [h] at hd; cases hd
    · rw [h] at hd; cases hd
    · obtain ⟨hp, hr, hh, _⟩ := hs.2.1 d h
      refine ⟨hp, ?_, hh⟩
      change Structural.reference (c.core.get d).reference = .basic
      rw [hr]; rfl
  · intro d f dom hd hf
    change Structural.origin (c.core.get d).origin = .primitive dom at hd
    change Structural.origin (c.core.get f).origin = .primitive dom at hf
    have prim : ∀ x : Fin e.count, Structural.origin (c.core.get x).origin = .primitive dom →
        (c.core.get x).origin = .integer := by
      intro x hx
      rcases hs.1 x with h | h | h
      · rw [h] at hx; cases hx
      · rw [h] at hx; cases hx
      · exact h
    exact hs.2.2.1 d f (prim d hd) (prim f hf)
  · intro d s h
    obtain ⟨_, _, hr, hd, _⟩ := hi d s h
    change (Structural.reference (c.core.get d).reference).kind.CanExtend
      (Structural.reference (c.core.get s).reference).kind
    rw [hr, hd]
    simp [Structural.reference, Clafer.MCS.ReferenceTo.kind, Clafer.Kind.CanExtend]
  · intro d s h hp
    exact False.elim (hp (hi d s h).2.1)

theorem m1_preserves (doc : Document) (e : Elaborated doc) (v : Validated e.count)
    (h : toM1 doc e = .ok v) : v.core = m1Core e.candidate ∧
      v.certificate = e.candidate.certificate := by
  unfold toM1 at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : validate (m1Core e.candidate) e.candidate.certificate with
    | error err => simp [hv, Except.mapError] at h
    | ok result =>
      simp only [hv, Except.mapError, Except.ok.injEq] at h
      subst v
      exact Structural.validate_preserves _ _ _ hv

/-- M1 conversion retains the existing independent admission theorem. -/
theorem m1_admitted (doc : Document) (e : Elaborated doc) (v : Validated e.count)
    (_h : toM1 doc e = .ok v) :
    (Structural.interpret v.core).WellFormed ∧ (Structural.interpret v.core).Supported :=
  Structural.validated_domain v

end ClaferCompiler.SemanticsBridge.Resolution
