module

public import ClaferCompiler.Correctness.PipelineIntegers
public import ClaferCompiler.SemanticsBridge.Inherited

@[expose] public section
/-! Primitive completion preserves finite ordinary objects and their original
relations. No expression agreement or source truth is included in the data.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Clafer.Semantics DPGraph.Predicates

structure PrimitiveShape (m : Realization.Core n) (p : Fin n) : Prop where
  notRoot : p ≠ m.family.root
  parent : m.family.parent p = some m.family.root
  reference : m.family.reference p = .basic
  super : m.family.super p = none
  noSuper : ∀ d, m.family.super d ≠ some p
  noChild : ∀ d, m.family.parent d ≠ some p
  explicit : m.explicitAbstract p = false
  multiplicity : m.family.multiplicity p = ⟨0, .unbounded⟩
  primitiveGroup : (m.family.group p).effective.range = ⟨0, .unbounded⟩
  rootGroup : (m.family.group m.family.root).effective.range = ⟨0, .unbounded⟩
  rootAncestor : ∀ d, m.toEffectiveCore.Ancestor d m.family.root → d = m.family.root

noncomputable def completePrimitive {U V : Type} (s : Configuration (Fin n) U)
    (p : Fin n) (g : U ↪ V) (P : Set V) : Configuration (Fin n) V := {
  root := g s.root
  head := fun d => if d = p then P else g '' s.head d
  contains := fun d a b => if d = p then a = g s.root ∧ b ∈ P
    else ∃ x y, s.contains d x y ∧ g x = a ∧ g y = b
  deref := fun d a b => ∃ x y, s.deref d x y ∧ g x = a ∧ g y = b }

theorem completed_head {U V : Type} (s : Configuration (Fin n) U)
    (p : Fin n) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p) (d : Fin n) (x : U) :
    g x ∈ (completePrimitive s p g P).head d ↔ x ∈ s.head d := by
  classical
  by_cases hd : d = p
  · simpa [completePrimitive,hd] using agree x
  · simp [completePrimitive,hd,g.injective.eq_iff]

theorem primitive_contains {U : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (x y : U) :
    s.contains p x y ↔ x = s.root ∧ y ∈ s.head p := by
  constructor
  · intro h
    obtain ⟨hy,c,hc,hx⟩ := hs.1.1 p x y h
    have he : c = m.family.root := Option.some.inj (hc.symm.trans hp.parent)
    exact ⟨(hs.2.1.1 x).mp (he ▸ hx),hy⟩
  · rintro ⟨rfl,hy⟩
    obtain ⟨x,hx,_⟩ := hs.2.2.1.2.1 p _ hp.parent y hy
    obtain ⟨_,c,hc,hc'⟩ := hs.1.1 p x y hx
    have he : c = m.family.root := Option.some.inj (hc.symm.trans hp.parent)
    have hr := (hs.2.1.1 x).mp (he ▸ hc')
    simpa only [hr] using hx

theorem completed_contains {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p) (d : Fin n) (x y : U) :
    (completePrimitive s p g P).contains d (g x) (g y) ↔ s.contains d x y := by
  classical
  by_cases hd : d = p
  · rw [hd,primitive_contains m s p hp hs]
    simp [completePrimitive,agree,g.injective.eq_iff]
  · simp [completePrimitive,hd,g.injective.eq_iff]

theorem completed_deref {U V : Type} (s : Configuration (Fin n) U)
    (p : Fin n) (g : U ↪ V) (P : Set V) (d : Fin n) (x y : U) :
    (completePrimitive s p g P).deref d (g x) (g y) ↔ s.deref d x y := by
  simp [completePrimitive,g.injective.eq_iff]

theorem completed_typed_rooted {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p)
    (cover : ∀ y, y ∈ P ∨ ∃ x, g x = y) :
    (completePrimitive s p g P).Typed m.toEffectiveCore ∧
      (completePrimitive s p g P).Rooted m.toEffectiveCore := by
  classical
  have head := completed_head s p g P agree
  have root : s.root ∈ s.head m.family.root := (hs.2.1.1 _).mpr rfl
  constructor
  · constructor
    · intro d a b h
      by_cases hd : d = p
      · subst d
        have h : a = g s.root ∧ b ∈ P := by simpa [completePrimitive] using h
        exact ⟨by simpa [completePrimitive] using h.2,
          m.family.root,hp.parent,h.1 ▸ (head _ _).mpr root⟩
      · obtain ⟨x,y,hr,rfl,rfl⟩ := (by simpa [completePrimitive,hd] using h :
          ∃ x y, s.contains d x y ∧ g x = a ∧ g y = b)
        obtain ⟨hy,c,hc,hx⟩ := hs.1.1 d x y hr
        exact ⟨(head _ _).mpr hy,c,hc,(head _ _).mpr hx⟩
    · rintro d a b ⟨x,y,hr,rfl,rfl⟩
      obtain ⟨hx,c,hc,hy⟩ := hs.1.2 d x y hr
      exact ⟨(head _ _).mpr hx,c,hc,(head _ _).mpr hy⟩
  · refine ⟨?_,?_,?_⟩
    · intro y
      simp only [completePrimitive,ite_eq_right hp.notRoot.symm]
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact congrArg g ((hs.2.1.1 x).mp hx)
      · rintro rfl
        exact ⟨s.root,root,rfl⟩
    · intro d hd h
      exact hs.2.1.2.1 d hd ((head d _).mp h)
    · intro y
      rcases cover y with hy | ⟨x,rfl⟩
      · exact .inr ⟨p,hp.notRoot,by simpa [completePrimitive] using hy⟩
      · rcases hs.2.1.2.2 x with hx | ⟨d,hd,hx⟩
        · exact .inl (congrArg g hx)
        · exact .inr ⟨d,hd,(head d x).mpr hx⟩

theorem completed_local {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p) :
    (completePrimitive s p g P).LocalConditions m.toEffectiveCore := by
  classical
  let t := completePrimitive s p g P
  have head := completed_head s p g P agree
  have contains := completed_contains m s p hp hs g P agree
  have deref := completed_deref s p g P
  have ordinary (d : Fin n) (hd : d ≠ p) (y : V) (hy : y ∈ t.head d) :
      ∃ x, x ∈ s.head d ∧ g x = y := by simpa [t,completePrimitive,hd] using hy
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro d c hc y hy
    have hd : d ≠ p := by intro he; subst d; rw [hp.super] at hc; cases hc
    have hcp : c ≠ p := by intro he; subst c; exact hp.noSuper d hc
    obtain ⟨x,hx,rfl⟩ := ordinary d hd y hy
    exact (head c x).mpr (hs.2.2.1.1 d c hc x hx)
  · intro d c hc y hy
    by_cases hd : d = p
    · subst d
      have hy : y ∈ P := by simpa [t,completePrimitive] using hy
      refine ⟨g s.root,by simp [completePrimitive,hy],?_⟩
      intro z hz
      exact (by simpa [completePrimitive] using hz : z = g s.root ∧ y ∈ P).1
    · obtain ⟨x,hx,rfl⟩ := ordinary d hd y hy
      obtain ⟨a,ha,hu⟩ := hs.2.2.1.2.1 d c hc x hx
      refine ⟨g a,(contains d a x).mpr ha,?_⟩
      intro z hz
      obtain ⟨b,w,hbw,hbz,hw⟩ := (by simpa [completePrimitive,hd] using hz :
        ∃ b w, s.contains d b w ∧ g b = z ∧ g w = g x)
      have hw : w = x := g.injective hw
      subst w
      exact hbz.symm.trans (congrArg g (hu b hbw))
  · intro d c hc y hy
    have hd : d ≠ p := by
      intro he; subst d; rw [hp.reference] at hc; cases hc
    obtain ⟨x,hx,rfl⟩ := ordinary d hd y hy
    obtain ⟨a,ha,hu⟩ := hs.2.2.1.2.2.1 d c hc x hx
    refine ⟨g a,(deref d x a).mpr ha,?_⟩
    rintro z ⟨b,w,hbw,hb,hw⟩
    have hb : b = x := g.injective hb
    subst b
    exact hw.symm.trans (congrArg g (hu w hbw))
  · intro d hd a b x y hax hxb hay hyb
    have hdp : d ≠ p := by
      intro he; subst d; rw [hp.reference] at hd; cases hd
    obtain ⟨a₁,x₁,hax₁,rfl,rfl⟩ := (by simpa [completePrimitive,hdp] using hax :
      ∃ a₁ x₁, s.contains d a₁ x₁ ∧ g a₁ = a ∧ g x₁ = x)
    obtain ⟨a₂,y₁,hay₁,ha,rfl⟩ := (by simpa [completePrimitive,hdp] using hay :
      ∃ a₂ y₁, s.contains d a₂ y₁ ∧ g a₂ = g a₁ ∧ g y₁ = y)
    have ha : a₂ = a₁ := g.injective ha
    subst a₂
    obtain ⟨x₂,b₁,hxb₁,hx,rfl⟩ := hxb
    have hx : x₂ = x₁ := g.injective hx
    subst x₂
    exact congrArg g (hs.2.2.1.2.2.2.1 d hd a₁ b₁ x₁ y₁ hax₁ hxb₁ hay₁
      ((deref d y₁ b₁).mp hyb))
  · intro d c hc a ha
    by_cases hd : d = p
    · subst d
      rw [hp.multiplicity]
      exact ⟨⟨Function.Embedding.ofIsEmpty⟩,trivial⟩
    · have hcp : c ≠ p := by intro he; subst c; exact hp.noChild d hc
      obtain ⟨x,hx,rfl⟩ := ordinary c hcp a ha
      let f : {y : U // s.contains d x y} → {y : V // t.contains d (g x) y} :=
        fun y => ⟨g y.val,(contains d x y.val).mpr y.property⟩
      have hf : Function.Bijective f := by
        constructor
        · intro a b he
          exact Subtype.ext (g.injective (congrArg Subtype.val he))
        · rintro ⟨y,hy⟩
          obtain ⟨a,b,hab,ha,rfl⟩ := (by simpa [t,completePrimitive,hd] using hy :
            ∃ a b, s.contains d a b ∧ g a = g x ∧ g b = y)
          have ha : a = x := g.injective ha
          subst a
          exact ⟨⟨b,hab⟩,rfl⟩
      exact (inRange_iff _ (Equiv.ofBijective f hf)).mp (hs.2.2.1.2.2.2.2 d c hc x hx)

theorem completed_children {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (g : U ↪ V) (P : Set V) (d : Fin n) (hd : d ≠ m.family.root) (x : U) (y : V) :
    Clafer.Compile.Groups.ChildObjects m.family (completePrimitive s p g P) d (g x) y ↔
      ∃ z, Clafer.Compile.Groups.ChildObjects m.family s d x z ∧ g z = y := by
  classical
  have child (a e : Fin n) (ha : Clafer.Compile.Groups.Ancestor m.family d a)
      (he : m.family.parent e = some a) : e ≠ p := by
    intro h; subst e
    have he : a = m.family.root := Option.some.inj (he.symm.trans hp.parent)
    subst a
    exact hd (hp.rootAncestor d ha)
  constructor
  · rintro ⟨a,ha,e,he,hr⟩
    obtain ⟨u,z,huz,hu,rfl⟩ := (by simpa [completePrimitive,child a e ha he] using hr :
      ∃ u z, s.contains e u z ∧ g u = g x ∧ g z = y)
    have hu : u = x := g.injective hu
    subst u
    exact ⟨z,⟨a,ha,e,he,huz⟩,rfl⟩
  · rintro ⟨z,⟨a,ha,e,he,hr⟩,rfl⟩
    refine ⟨a,ha,e,he,?_⟩
    simpa [completePrimitive,child a e ha he,g.injective.eq_iff] using hr

theorem completed_global {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p) :
    Realization.Abstracts m (completePrimitive s p g P) ∧
      Realization.Groups m (completePrimitive s p g P) ∧
      (completePrimitive s p g P).DeclarationDisjoint m.toEffectiveCore := by
  classical
  let t := completePrimitive s p g P
  have head := completed_head s p g P agree
  have ordinary (d : Fin n) (hd : d ≠ p) (y : V) (hy : y ∈ t.head d) :
      ∃ x, x ∈ s.head d ∧ g x = y := by simpa [t,completePrimitive,hd] using hy
  refine ⟨?_,?_,?_⟩
  · intro d hd
    have hdp : d ≠ p := by intro he; subst d; rw [hp.explicit] at hd; cases hd
    constructor
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := ordinary d hdp y hy
      obtain ⟨c,hc,hx⟩ := (hs.2.2.2.1 d hd).1 x hx
      exact ⟨c,hc,(head c x).mpr hx⟩
    · intro c e hc he hce y hy
      have hcp : c ≠ p := by intro h; subst c; rw [hp.super] at hc; cases hc
      obtain ⟨x,hx,rfl⟩ := ordinary c hcp y hy.1
      exact (hs.2.2.2.1 d hd).2 c e hc he hce x ⟨hx,(head e x).mp hy.2⟩
  · intro d hd y
    by_cases hdp : d = p
    · subst d
      rw [hp.primitiveGroup]
      exact ⟨⟨Function.Embedding.ofIsEmpty⟩,trivial⟩
    by_cases hdr : d = m.family.root
    · subst d
      rw [hp.rootGroup]
      exact ⟨⟨Function.Embedding.ofIsEmpty⟩,trivial⟩
    obtain ⟨x,hx,hxy⟩ := ordinary d hdp y.val y.property
    let f : {z : U // Clafer.Compile.Groups.ChildObjects m.family s d x z} →
        {z : V // Clafer.Compile.Groups.ChildObjects m.family t d y.val z} := fun z =>
      ⟨g z.val, hxy ▸ (completed_children m s p hp g P d hdr x _).mpr ⟨z.val,z.property,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b he
        exact Subtype.ext (g.injective (congrArg Subtype.val he))
      · rintro ⟨z,hz⟩
        rw [← hxy] at hz
        obtain ⟨a,ha,he⟩ := (completed_children m s p hp g P d hdr x z).mp hz
        exact ⟨⟨a,ha⟩,Subtype.ext he⟩
    exact (inRange_iff _ (Equiv.ofBijective f hf)).mp (hs.2.2.2.2.1 d hd ⟨x,hx⟩)
  · intro d e y hy hz
    by_cases hd : d = p
    · subst d
      by_cases he : e = p
      · subst e; exact .inl .refl
      · obtain ⟨x,hx,rfl⟩ := ordinary e he y hz
        exact hs.2.2.2.2.2 p e x ((head p x).mp hy) hx
    · obtain ⟨x,hx,rfl⟩ := ordinary d hd y hy
      exact hs.2.2.2.2.2 d e x hx ((head e x).mp hz)

/-- Every clause of selected structural satisfaction, including the infinite
primitive's ownership, multiplicity and group obligations, is retained. -/
theorem completed_structure {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p)
    (cover : ∀ y, y ∈ P ∨ ∃ x, g x = y) :
    Realization.Satisfies m (completePrimitive s p g P) := by
  obtain ⟨ht,hr⟩ := completed_typed_rooted m s p hp hs g P agree cover
  obtain ⟨ha,hg,hd⟩ := completed_global m s p hp hs g P agree
  exact ⟨ht,hr,completed_local m s p hp hs g P agree,ha,hg,hd⟩

theorem full_integer_structure {U : Type} [Fintype U] (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (hs : Realization.Satisfies m s) (g : U ↪ IR.Expr.Atom)
    (ordinary : ∀ x, x ∉ s.head p → ∃ a, g x = .object a) (observed : Finset Int) :
    ∃ R : FormalCD.IntegerRealization IR.Expr.Atom,
      (∀ z ∈ observed, R.encode z = .integer z) ∧
      (∀ x, g x ∈ R.domain ↔ x ∈ s.head p) ∧
      Realization.Satisfies m (completePrimitive s p g R.domain) := by
  classical
  let objects := (Finset.univ.filter (fun x => x ∉ s.head p)).image g
  have ho : ∀ z, IR.Expr.Atom.integer z ∉ objects := by
    intro z hz
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha⟩ := ordinary x (Finset.mem_filter.mp hx).2
    rw [ha] at he
    cases he
  obtain ⟨R,hr,hfixed⟩ := integer_completion objects ho observed
  have hagree : ∀ x, g x ∈ R.domain ↔ x ∈ s.head p := by
    intro x
    rw [hr]
    simp only [Set.mem_ofPred_eq,objects,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
      true_and,g.injective.eq_iff,not_exists,not_and]
    constructor
    · intro h
      by_contra hn
      exact h x hn rfl
    · intro hx y hy he
      exact hy (he.symm ▸ hx)
  have hcover : ∀ y, y ∈ R.domain ∨ ∃ x, g x = y := by
    intro y
    by_cases hy : y ∈ R.domain
    · exact .inl hy
    · rw [hr] at hy
      have hm : y ∈ objects := by simpa using hy
      obtain ⟨x,_,he⟩ := Finset.mem_image.mp hm
      exact .inr ⟨x,he⟩
  exact ⟨R,hfixed,hagree,completed_structure m s p hp hs g R.domain hagree hcover⟩

end ClaferCompiler.Correctness.Pipeline
