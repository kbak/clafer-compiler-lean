module

public import Clafer.Behavioral.Snapshot
public import ClaferCompiler.SemanticsBridge.Behavioral.Trace

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Clafer.Semantics
open Clafer.Behavioral

instance liveSnapshotFintype [Fintype U] (τ : Trace C U) (t : Nat) : Fintype (τ.Live t) :=
  Fintype.ofFinite {x : U // x ∈ τ.live t}

/-- The upstream live snapshot data, requiring only a live root. This avoids
assuming complete source validity while deriving its state obligations. -/
def liveSnapshot (m : EffectiveCore k) (τ : Trace (Fin k) U) (t : Nat)
    (rootLive : τ.identities.root ∈ τ.live t) : Configuration (Fin k) (τ.Live t) where
  root := ⟨τ.identities.root, rootLive⟩
  head d := {x | x.val ∈ (τ.raw m t).head d}
  contains d p x := (τ.raw m t).contains d p.val x.val
  deref d x y := (τ.raw m t).deref d x.val y.val

def liveFiberEquiv (m : EffectiveCore k) (τ : Trace (Fin k) U) (t : Nat)
    (rootLive : τ.identities.root ∈ τ.live t) (d : Fin k) (p : τ.Live t) :
    {x // (liveSnapshot m τ t rootLive).contains d p x} ≃
      {x // (τ.raw m t).contains d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def liveChildEquiv (m : EffectiveCore k) (τ : Trace (Fin k) U) (t : Nat)
    (rootLive : τ.identities.root ∈ τ.live t) (d : Fin k) (p : τ.Live t) :
    {x // (liveSnapshot m τ t rootLive).Child m d p x} ≃
      {x // (τ.raw m t).Child m d p.val x} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by obtain ⟨c, _, hc⟩ := x.property; exact hc.1.2.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- [proof->req~compiler-behavioral-correctness~1]
/-- Structural truth of the concrete live restriction recovers every upstream
state obligation. Reference endpoints must be live; no dangling row is dropped. -/
theorem stateValid_of_liveSnapshot (m : EffectiveCore k) (τ : Trace (Fin k) U) (t : Nat)
    (rootLive : τ.identities.root ∈ τ.live t)
    (refsLive : ∀ d x y, τ.deref t d x y → x ∈ τ.live t ∧ y ∈ τ.live t)
    (h : StructuralSatisfies m (liveSnapshot m τ t rootLive)) : τ.StateValid m t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro d p x hx
      exact h.1.1 d ⟨p, hx.1.1⟩ ⟨x, hx.1.2.1⟩ hx
    · intro d x y hy
      have live := refsLive d x y hy
      exact h.1.2 d ⟨x, live.1⟩ ⟨y, live.2⟩ hy
  · intro x
    constructor
    · intro hx
      exact congrArg Subtype.val ((h.2.1.1 ⟨x, hx.1⟩).mp hx)
    · rintro rfl
      exact (h.2.1.1 ⟨τ.identities.root, rootLive⟩).mpr rfl
  · exact h.2.1.2.1
  · intro d c hc x hx
    exact h.2.2.1 d c hc ⟨x, hx.1⟩ hx
  · intro d hd
    constructor
    · intro x hx
      exact (h.2.2.2.1 d hd).1 ⟨x, hx.1⟩ hx
    · intro c e hc he hne x hx
      exact (h.2.2.2.1 d hd).2 c e hc he hne ⟨x, hx.1.1⟩ hx
  · intro d c hc x hx
    obtain ⟨p, hp, unique⟩ := h.2.2.2.2.1 d c hc ⟨x, hx.1⟩ hx
    refine ⟨p.val, hp, ?_⟩
    intro q hq
    exact congrArg Subtype.val (unique ⟨q, hq.1.1⟩ hq)
  · intro d c hc x hx
    obtain ⟨y, hy, unique⟩ := h.2.2.2.2.2.1 d c hc ⟨x, hx.1⟩ hx
    refine ⟨y.val, hy, ?_⟩
    intro z hz
    exact congrArg Subtype.val (unique ⟨z, (refsLive d x z hz).2⟩ hz)
  · intro d hd p y x z hpx hxy hpz hzy
    exact congrArg Subtype.val (h.2.2.2.2.2.2.1 d hd
      ⟨p, hpx.1.1⟩ ⟨y, (refsLive d x y hxy).2⟩
      ⟨x, hpx.1.2.1⟩ ⟨z, hpz.1.2.1⟩ hpx hxy hpz hzy)
  · intro d c hc p hp
    exact (DPGraph.Predicates.inRange_iff _ (liveFiberEquiv m τ t rootLive d ⟨p, hp.1⟩)).mp
      (h.2.2.2.2.2.2.2.1 d c hc ⟨p, hp.1⟩ hp)
  · intro d hd p hp
    exact (DPGraph.Predicates.inRange_iff _ (liveChildEquiv m τ t rootLive d ⟨p, hp.1⟩)).mp
      (h.2.2.2.2.2.2.2.2.1 d hd ⟨p, hp.1⟩ hp)
  · intro d e x hd he
    exact h.2.2.2.2.2.2.2.2.2 d e ⟨x, hd.1⟩ hd he

theorem liveSnapshot_eq_upstream (m : EffectiveCore k) (τ : Trace (Fin k) U)
    (valid : τ.Valid m) (t : Nat) :
    liveSnapshot m τ t (valid.root_live t) = τ.snapshot valid t := rfl

end ClaferCompiler.Correctness.Behavioral
