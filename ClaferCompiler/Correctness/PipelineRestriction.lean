module

public import ClaferCompiler.Correctness.PipelineCompletion

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open Clafer.Semantics DPGraph.Predicates

/-- Finite restriction uses data equations, not finite satisfaction as a premise.
Only the unrestricted primitive fiber is shortened. -/
theorem restricted_structure {U V : Type} (m : Realization.Core n)
    (s : Configuration (Fin n) U) (p : Fin n) (hp : PrimitiveShape m p)
    (g : U ↪ V) (P : Set V)
    (agree : ∀ x, g x ∈ P ↔ x ∈ s.head p)
    (primitive : ∀ x y, s.contains p x y ↔ x = s.root ∧ y ∈ s.head p)
    (hs : Realization.Satisfies m (completePrimitive s p g P)) :
    Realization.Satisfies m s := by
  classical
  let t := completePrimitive s p g P
  have head := completed_head s p g P agree
  have contains (d : Fin n) (x y : U) : t.contains d (g x) (g y) ↔ s.contains d x y := by
    by_cases hd : d = p
    · subst d
      simpa [t,completePrimitive,agree,g.injective.eq_iff] using (primitive x y).symm
    · simp [t,completePrimitive,hd,g.injective.eq_iff]
  have deref := completed_deref s p g P
  have ordinary (d : Fin n) (hd : d ≠ p) (y : V) (hy : y ∈ t.head d) :
      ∃ x, x ∈ s.head d ∧ g x = y := by simpa [t,completePrimitive,hd] using hy
  have fiber (d : Fin n) (hd : d ≠ p) (x : U) :
      {y : U // s.contains d x y} ≃ {y : V // t.contains d (g x) y} :=
    Equiv.ofBijective (fun y => ⟨g y.val,(contains d x y.val).mpr y.property⟩) (by
      constructor
      · intro a b he
        exact Subtype.ext (g.injective (congrArg Subtype.val he))
      · rintro ⟨y,hy⟩
        obtain ⟨a,b,hab,ha,rfl⟩ := (by simpa [t,completePrimitive,hd] using hy :
          ∃ a b, s.contains d a b ∧ g a = g x ∧ g b = y)
        have ha : a = x := g.injective ha
        subst a
        exact ⟨⟨b,hab⟩,rfl⟩)
  refine ⟨⟨?_,?_⟩,⟨?_,?_,?_⟩,⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro d x y h
    obtain ⟨hy,c,hc,hx⟩ := hs.1.1 d (g x) (g y) ((contains d x y).mpr h)
    exact ⟨(head d y).mp hy,c,hc,(head c x).mp hx⟩
  · intro d x y h
    obtain ⟨hx,c,hc,hy⟩ := hs.1.2 d (g x) (g y) ((deref d x y).mpr h)
    exact ⟨(head d x).mp hx,c,hc,(head c y).mp hy⟩
  · intro x
    exact (head _ x).symm.trans ((hs.2.1.1 (g x)).trans g.injective.eq_iff)
  · intro d hd hx
    exact hs.2.1.2.1 d hd ((head d s.root).mpr hx)
  · intro x
    rcases hs.2.1.2.2 (g x) with hx | ⟨d,hd,hx⟩
    · exact .inl (g.injective hx)
    · exact .inr ⟨d,hd,(head d x).mp hx⟩
  · intro d c hc x hx
    exact (head c x).mp (hs.2.2.1.1 d c hc (g x) ((head d x).mpr hx))
  · intro d c hc y hy
    by_cases hd : d = p
    · subst d
      exact ⟨s.root,(primitive _ _).mpr ⟨rfl,hy⟩,fun x hx => ((primitive _ _).mp hx).1⟩
    · obtain ⟨a,ha,hu⟩ := hs.2.2.1.2.1 d c hc (g y) ((head d y).mpr hy)
      obtain ⟨x,z,hxz,hxa,hzy⟩ := (by simpa [completePrimitive,hd] using ha :
        ∃ x z, s.contains d x z ∧ g x = a ∧ g z = g y)
      have hzy : z = y := g.injective hzy
      subst z
      refine ⟨x,hxz,?_⟩
      intro w hw
      exact g.injective ((hu (g w) ((contains d w y).mpr hw)).trans hxa.symm)
  · intro d c hc x hx
    obtain ⟨a,⟨u,y,huy,hux,hya⟩,hu⟩ := hs.2.2.1.2.2.1 d c hc (g x) ((head d x).mpr hx)
    have hux : u = x := g.injective hux
    subst u
    exact ⟨y,huy,fun w hw => g.injective ((hu (g w) ((deref d x w).mpr hw)).trans hya.symm)⟩
  · intro d hd a b x y hax hxb hay hyb
    exact g.injective (hs.2.2.1.2.2.2.1 d hd (g a) (g b) (g x) (g y)
      ((contains d a x).mpr hax) ((deref d x b).mpr hxb)
      ((contains d a y).mpr hay) ((deref d y b).mpr hyb))
  · intro d c hc x hx
    by_cases hd : d = p
    · subst d
      rw [hp.multiplicity]
      exact ⟨⟨Function.Embedding.ofIsEmpty⟩,trivial⟩
    · exact (inRange_iff _ (fiber d hd x)).mpr
        (hs.2.2.1.2.2.2.2 d c hc (g x) ((head c x).mpr hx))
  · intro d hd
    constructor
    · intro x hx
      obtain ⟨c,hc,hx⟩ := (hs.2.2.2.1 d hd).1 (g x) ((head d x).mpr hx)
      exact ⟨c,hc,(head c x).mp hx⟩
    · intro c e hc he hce x hx
      exact (hs.2.2.2.1 d hd).2 c e hc he hce (g x)
        ⟨(head c x).mpr hx.1,(head e x).mpr hx.2⟩
  · intro d hd x
    by_cases hdr : d = m.family.root
    · subst d
      rw [hp.rootGroup]
      exact ⟨⟨Function.Embedding.ofIsEmpty⟩,trivial⟩
    · let f : {z : U // Clafer.Compile.Groups.ChildObjects m.family s d x.val z} →
          {z : V // Clafer.Compile.Groups.ChildObjects m.family t d (g x.val) z} :=
        fun z => ⟨g z.val,(completed_children m s p hp g P d hdr x.val _).mpr ⟨z.val,z.property,rfl⟩⟩
      have hf : Function.Bijective f := by
        constructor
        · intro a b he
          exact Subtype.ext (g.injective (congrArg Subtype.val he))
        · rintro ⟨z,hz⟩
          obtain ⟨a,ha,he⟩ := (completed_children m s p hp g P d hdr x.val z).mp hz
          exact ⟨⟨a,ha⟩,Subtype.ext he⟩
      exact (inRange_iff _ (Equiv.ofBijective f hf)).mpr
        (hs.2.2.2.2.1 d hd ⟨g x.val,(head d x.val).mpr x.property⟩)
  · intro d e x hx hy
    exact hs.2.2.2.2.2 d e (g x) ((head d x).mpr hx) ((head e x).mpr hy)

end ClaferCompiler.Correctness.Pipeline
