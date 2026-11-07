module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsCapture

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
variable {U : Type}

 theorem ContextRep.bind (hc : ContextRep v w τ f c ρ e) (x : U) :
    ContextRep v w τ f ((c.shift 1).push (.var 0)) (ρ.push {x}) (.object (f x) :: e) :=
  (hc.shift [.object (f x)]).push ⟨.var 0, fun _ => Relations.unary_singleton x⟩

theorem ContextRep.bindTwo (hc : ContextRep v w τ f c ρ e) (x y : U) :
    ContextRep v w τ f ((c.shift 2).push (.var 0)) (ρ.push {y}) (.object (f y) :: .object (f x) :: e) :=
  (hc.shift [.object (f y), .object (f x)]).push ⟨.var 0, fun _ => Relations.unary_singleton y⟩

namespace Encoding

theorem all_unary (hp : Formula.Built p)
    (hr : Relations.Unary f D (r.eval s w τ e t)) :
    (Formula.all r p).Holds s w τ e t ↔
      ∀ x ∈ D, p.Holds s w τ (.object (f x) :: e) t := by
  rw [holds_all hp]
  constructor
  · intro h x hx
    exact h _ ((hr _).mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, he⟩ := (hr _).mp hy
    have he' : y = .object (f x) := by simpa using he
    subst y
    exact h x hx

theorem exists_unary (hp : Formula.Built p)
    (hr : Relations.Unary f D (r.eval s w τ e t)) :
    (Formula.exists_ r p).Holds s w τ e t ↔
      ∃ x ∈ D, p.Holds s w τ (.object (f x) :: e) t := by
  rw [holds_exists hp]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, hx, he⟩ := (hr _).mp hy
    have he' : y = .object (f x) := by simpa using he
    subst y
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨_, (hr _).mpr ⟨x, hx, rfl⟩, h⟩

theorem equal_variables (hf : Function.Injective f) (x y : U) :
    (Formula.equal (.var 0) (.var 1)).Holds s w τ (.object (f y) :: .object (f x) :: e) t ↔ y = x := by
  have h : Relations.Unary f {y} ((Rel.var 0).eval s w τ (.object (f y) :: .object (f x) :: e) t) := Relations.unary_singleton _
  have h' : Relations.Unary f {x} ((Rel.var 1).eval s w τ (.object (f y) :: .object (f x) :: e) t) := Relations.unary_singleton _
  exact (Relations.unary_equal hf h h').trans (by simp)

-- [proof->req~compiler-behavioral-correctness~1]
/-- Counting uses the raw body under two independent singleton binders. -/
theorem unique_meaning (hf : Function.Injective f) (hd : Rel.Term d)
    (hD : Relations.Unary f D (d.eval s w τ e t)) (ha : a.Built)
    (P : U → Prop)
    (hP : ∀ x y, a.Holds s w τ (.object (f y) :: .object (f x) :: e) t ↔ P y)
    (x : U) :
    (Formula.all (shift 1 d) (.binary .implies a (.equal (.var 0) (.var 1)))).Holds
      s w τ (.object (f x) :: e) t ↔ ∀ y ∈ D, P y → y = x := by
  have hD' : Relations.Unary f D ((shift 1 d).eval s w τ (.object (f x) :: e) t) := by
    rw [show (1 : Nat) = ([.object (f x)] : Environment).length from rfl,
      show .object (f x) :: e = [.object (f x)] ++ e from rfl, shift_eval hd]
    exact hD
  rw [all_unary (.binary .implies ha (.equal _ _)) hD']
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro _
  rw [holds_implies ha (.equal _ _), hP, equal_variables hf]

theorem one_meaning (hf : Function.Injective f) (hd : Rel.Term d)
    (hD : Relations.Unary f D (d.eval s w τ e t)) (ha : a.Built) (hb : b.Built)
    (P : U → Prop)
    (hP : ∀ x, a.Holds s w τ (.object (f x) :: e) t ↔ P x)
    (hQ : ∀ x y, b.Holds s w τ (.object (f y) :: .object (f x) :: e) t ↔ P y) :
    (Formula.exists_ d (.binary .conj a (.all (shift 1 d)
      (.binary .implies b (.equal (.var 0) (.var 1)))))).Holds s w τ e t ↔
      Clafer.Behavioral.Quantifier.one.eval D P := by
  rw [exists_unary (.binary .conj ha (.all _ (.binary .implies hb (.equal _ _)))) hD]
  simp only [holds_and ha (.all _ (.binary .implies hb (.equal _ _))), hP,
    unique_meaning hf hd hD hb P hQ, Clafer.Behavioral.Quantifier.eval, ExistsUnique]
  aesop

theorem lone_meaning (hf : Function.Injective f) (hd : Rel.Term d)
    (hD : Relations.Unary f D (d.eval s w τ e t)) (ha : a.Built) (hb : b.Built)
    (P : U → Prop)
    (hP : ∀ x, a.Holds s w τ (.object (f x) :: e) t ↔ P x)
    (hQ : ∀ x y, b.Holds s w τ (.object (f y) :: .object (f x) :: e) t ↔ P y) :
    (Formula.all d (.binary .implies a (.all (shift 1 d)
      (.binary .implies b (.equal (.var 0) (.var 1)))))).Holds s w τ e t ↔
      Clafer.Behavioral.Quantifier.lone.eval D P := by
  rw [all_unary (.binary .implies ha (.all _ (.binary .implies hb (.equal _ _)))) hD]
  simp only [holds_implies ha (.all _ (.binary .implies hb (.equal _ _))), hP,
    unique_meaning hf hd hD hb P hQ, Clafer.Behavioral.Quantifier.eval]
  aesop

end Encoding
end ClaferCompiler.Correctness.Behavioral
