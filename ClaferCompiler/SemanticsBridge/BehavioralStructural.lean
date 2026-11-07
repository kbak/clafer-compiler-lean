module

public import ClaferCompiler.IR.BehavioralStructural
public import ClaferCompiler.SemanticsBridge.Resolution
public import Clafer.Behavioral.Structural

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.BehavioralStructural
open IR.BehavioralStructural
open IR.Structural (Certificate Reference)

/-- Field interpretation retains names, IDs, authored abstractness and effective
group provenance. It assumes neither admission nor model satisfaction. -/
def interpret (m : Core n) : Clafer.Behavioral.Structural.Core n where
  toEffectiveCore := { Structural.interpret m.structural with
    family := { (Structural.interpret m.structural).family with
      group := fun d => ⟨none, Resolution.group m.groups[d]⟩ } }
  authoredAbstract := fun d => m.authoredAbstract[d]

variable {n : Nat} {m : Core n} {k : Certificate n} {a : Analysis n}

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem ancestor_sound (paths : a.Valid m)
    (ranks : ∀ d s, (m.structural.get d).super = some s → k.superRank[s] < k.superRank[d])
    {d p : Fin n} (hp : p ∈ a.ancestors[d]) :
    (interpret m).toEffectiveCore.Ancestor d p := by
  suffices ∀ r d, k.superRank[d] = r → p ∈ a.ancestors[d] →
      (interpret m).toEffectiveCore.Ancestor d p from this _ d rfl hp
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro d hd hp
    rw [paths.1 d] at hp
    rcases List.mem_cons.mp hp with he | hp
    · subst p; exact .refl
    · cases hs : (m.structural.get d).super with
      | none => simp [hs] at hp
      | some s =>
        have hsp : p ∈ a.ancestors[s] := by simpa [hs] using hp
        exact (ih _ (hd ▸ ranks d s hs) s rfl hsp).head hs

theorem ancestor_complete (paths : a.Valid m) {d p : Fin n}
    (hp : (interpret m).toEffectiveCore.Ancestor d p) : p ∈ a.ancestors[d] := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => rw [paths.1 p]; exact List.mem_cons_self
  | @head d s hs _ ih =>
    rw [paths.1 d]
    have edge : (m.structural.get d).super = some s := hs
    simpa [edge] using List.mem_cons_of_mem d ih

theorem owner_sound (paths : a.Valid m)
    (ranks : ∀ d s, (m.structural.get d).super = some s → k.superRank[s] < k.superRank[d])
    {d o : Fin n} (ho : a.referenceOwners[d] = some o) :
    Clafer.Behavioral.InheritedReference.Owner (interpret m).family d o := by
  suffices ∀ r d, k.superRank[d] = r → a.referenceOwners[d] = some o →
      Clafer.Behavioral.InheritedReference.Owner (interpret m).family d o from this _ d rfl ho
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro d hd ho
    rw [paths.2 d] at ho
    split at ho
    · rename_i hb
      cases hs : (m.structural.get d).super with
      | none => simp [hs] at ho
      | some s =>
        have hso : a.referenceOwners[s] = some o := by simpa [hs] using ho
        exact .inherited (by simpa [interpret, Structural.interpret] using hb) hs
          (ih _ (hd ▸ ranks d s hs) s rfl hso)
    · rename_i hb
      cases Option.some.inj ho
      exact .declared (by simpa [interpret, Structural.interpret] using hb)

theorem owner_complete (paths : a.Valid m) {d o : Fin n}
    (ho : Clafer.Behavioral.InheritedReference.Owner (interpret m).family d o) :
    a.referenceOwners[d] = some o := by
  induction ho with
  | @declared d ref =>
    have hr : (m.structural.get d).reference ≠ .basic := by simpa [interpret, Structural.interpret] using ref
    simp [paths.2 d, hr]
  | @inherited d s o basic edge _ ih =>
    have hb : (m.structural.get d).reference = .basic := by simpa [interpret, Structural.interpret] using basic
    have hs : (m.structural.get d).super = some s := edge
    rw [paths.2 d]
    simpa only [hb, ↓reduceIte, hs, Option.bind_some] using ih

@[simp] theorem canExtend_iff (x y : Reference (Fin n)) :
    canExtend x y ↔ (Structural.reference x).kind.CanExtend (Structural.reference y).kind := by
  cases x <;> cases y <;> simp [canExtend, Structural.reference,
    Clafer.MCS.ReferenceTo.kind, Clafer.Kind.CanExtend]

-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- Admission establishes the accepted richer upstream model obligations.
No constraint truth, candidate validity or target correctness is a premise. -/
theorem validated_wellFormed (v : Validated n) : (interpret v.core).WellFormed := by
  rcases v.checked with ⟨hc, paths, root, authored, parentless, primitive, unique,
    parents, references, groups⟩
  rcases hc with ⟨ids, origins, rootShape, parentRanks, superRanks, bounds, _⟩
  constructor
  · intro d; simpa [interpret, Structural.interpret] using origins d
  · exact ⟨rootShape.1, by simpa [interpret, Structural.interpret] using rootShape.2.1,
      rootShape.2.2.1, root, rootShape.2.2.2⟩
  · intro d p hp
    rcases v.support d with hr | hu | hi
    · simp [interpret, Structural.interpret, hr, Structural.origin] at hp
    · simp [interpret, Structural.interpret, hu, Structural.origin] at hp
    · exact ⟨(primitive d hi).1, by simpa [interpret, Structural.interpret] using (primitive d hi).2.1,
        (primitive d hi).2.2⟩
  · intro d e p hd he
    have integer (x : Fin n) (hx : Structural.origin (v.core.structural.get x).origin = .primitive p) :
        (v.core.structural.get x).origin = .integer := by
      rcases v.support x with hr | hu | hi
      · simp [hr, Structural.origin] at hx
      · simp [hu, Structural.origin] at hx
      · exact hi
    exact unique d e (integer d hd) (integer e he)
  · exact authored
  · exact parentless
  · intro d s p hs hp
    obtain ⟨q, hq, ha⟩ := parents d s p hs hp
    exact ⟨q, hq, ancestor_sound paths superRanks ha⟩
  · intro d s o x y hs ho hx hy
    obtain ⟨ha, kind⟩ := references d s o x y hs (owner_complete paths ho)
      (by simpa [interpret, Structural.interpret] using hx)
      (by simpa [interpret, Structural.interpret] using hy)
    exact ⟨ancestor_sound paths superRanks ha, (canExtend_iff _ _).mp kind⟩
  · exact ⟨fun d => v.certificate.parentRank[d], parentRanks⟩
  · exact ⟨fun d => v.certificate.superRank[d], superRanks⟩
  · intro d e h; apply ids d e; exact congrArg Clafer.DeclId.value h
  · intro d; exact (Structural.bounds_valid _).mpr (bounds d).1
  · intro d; exact (Structural.bounds_valid _).mpr (bounds d).2
  · intro d
    change Structural.bounds (v.core.structural.get d).groupBounds = (Resolution.group v.core.groups[d]).range
    rw [Resolution.group_range, groups d]

theorem validate_preserves (selected : String) (m : Core n) (k : Certificate n)
    (v : Validated n) (h : validate selected m k = .ok v) :
    selected = profile ∧ v.core = m ∧ v.certificate = k := by
  unfold validate at h
  split at h
  · cases h
  · rename_i hp
    split at h
    · dsimp only at h
      split at h
      · cases h; exact ⟨by simpa using hp, rfl, rfl⟩
      · cases h
    · cases h

/-- On supported primitives and checked hierarchy tables/ranks, the executable
guard is exactly upstream well-formedness. No static M1 guard is used. -/
theorem checks_iff (support : supported m) (paths : a.Valid m)
    (parents : ∀ d p, (m.structural.get d).parent = some p → k.parentRank[p] < k.parentRank[d])
    (supers : ∀ d s, (m.structural.get d).super = some s → k.superRank[s] < k.superRank[d]) :
    checks m k a ↔ (interpret m).WellFormed := by
  constructor
  · intro h; exact validated_wellFormed ⟨m, k, a, h, support⟩
  intro h
  have origins : ∀ d, (m.structural.get d).origin = .syntheticRoot ↔ d = m.structural.root := by
    intro d
    cases ho : (m.structural.get d).origin <;>
      simpa [interpret, Structural.interpret, Structural.origin, ho] using h.root_origin d
  refine ⟨⟨?_, origins, ?_, parents, supers, ?_, ?_⟩, paths,
    h.root_shape.2.2.2.1, h.authored_effective, h.parentless_abstract, ?_, ?_, ?_, ?_, ?_⟩
  · intro d e ids
    apply h.ids
    exact congrArg Clafer.DeclId.mk ids
  · exact ⟨h.root_shape.1, by simpa [interpret, Structural.interpret] using h.root_shape.2.1,
      h.root_shape.2.2.1, h.root_shape.2.2.2.2⟩
  · intro d
    exact ⟨(Structural.bounds_valid _).mp (h.multiplicity_bounds d),
      (Structural.bounds_valid _).mp (h.group_bounds d)⟩
  · intro d hp hn; exact h.authored_effective d (h.parentless_abstract d hp hn)
  · intro d hd
    have hp : (interpret m).family.origin d = .primitive .int := by
      simp [interpret, Structural.interpret, Structural.origin, hd]
    have shape := h.primitive_shape d _ hp
    exact ⟨shape.1, by simpa [interpret, Structural.interpret] using shape.2.1, shape.2.2⟩
  · intro d e hd he
    apply h.unique_primitive d e .int <;>
      simp [interpret, Structural.interpret, Structural.origin, hd, he]
  · intro d s p hs hp
    obtain ⟨q, hq, ha⟩ := h.refined_parent d s p hs hp
    exact ⟨q, hq, ancestor_complete paths ha⟩
  · intro d s o x y hs ho hx hy
    obtain ⟨ha, hk⟩ := h.reference_refinement d s o x y hs (owner_sound paths supers ho)
      (by simpa [interpret, Structural.interpret] using hx)
      (by simpa [interpret, Structural.interpret] using hy)
    exact ⟨ancestor_complete paths ha, (canExtend_iff _ _).mpr hk⟩
  · intro d
    have hg := h.group_agrees d
    change Structural.bounds (m.structural.get d).groupBounds = (Resolution.group m.groups[d]).range at hg
    rw [Resolution.group_range] at hg
    have injective : Function.Injective Structural.bounds := by
      rintro ⟨al, au⟩ ⟨bl, bu⟩ eq
      cases au <;> cases bu <;> simp_all [Structural.bounds]
    exact (injective hg).symm

universe u
variable {U : Type u}

/-- Effective groups count the union of the original head fibers selected by
the runtime table, including added subtype children and ordinary inherited fields. -/
theorem childObjects_iff (v : Validated n) (s : Clafer.Semantics.Configuration (Fin n) U)
    (d : Fin n) (p x : U) :
    Clafer.Semantics.Groups.ChildObjects (interpret v.core).family s d p x ↔
      ∃ c ∈ childDeclarations v d, s.contains c p x := by
  have member (c : Fin n) : c ∈ childDeclarations v d ↔
      ∃ a, (v.core.structural.get c).parent = some a ∧ a ∈ v.analysis.ancestors[d] := by
    cases hp : (v.core.structural.get c).parent <;> simp [childDeclarations, hp]
  constructor
  · rintro ⟨a, ha, c, hc, hx⟩
    exact ⟨c, (member c).mpr ⟨a, hc, ancestor_complete v.checked.2.1 ha⟩, hx⟩
  · rintro ⟨c, hc, hx⟩
    obtain ⟨a, hp, ha⟩ := (member c).mp hc
    exact ⟨a, ancestor_sound v.checked.2.1 v.checked.1.2.2.2.2.1 ha, c, hp, hx⟩

end ClaferCompiler.SemanticsBridge.BehavioralStructural
