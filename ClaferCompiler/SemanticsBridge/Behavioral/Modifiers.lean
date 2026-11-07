module

public import ClaferCompiler.IR.Behavioral.Modifiers
public import ClaferCompiler.SemanticsBridge.Behavioral.Surface
public import ClaferCompiler.SemanticsBridge.BehavioralStructural

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Modifiers
open IR.Behavioral
open IR.Behavioral.Surface.Modifiers
open Surface.Modifiers (modifier placement)

def declared (table : Vector (List Modifier) k) (d : Fin k) :
    Set Clafer.Behavioral.Modifiers.Modifier := {m | m ∈ (table[d].map modifier)}

theorem modifier_injective : Function.Injective modifier := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Inheritance uses the independently defined upstream ancestor relation;
repetition affects provenance, not membership or modifier meaning. -/
theorem effective_agrees (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List Modifier) k) (d : Fin k) (m : Modifier) :
    m ∈ IR.Behavioral.Modifiers.effective v table d ↔
      Clafer.Behavioral.Modifiers.Effective (BehavioralStructural.interpret v.core).family
        (declared table) d (modifier m) := by
  simp only [IR.Behavioral.Modifiers.effective, List.mem_flatMap,
    Clafer.Behavioral.Modifiers.Effective, declared, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨a, ha, hm⟩
    exact ⟨a, BehavioralStructural.ancestor_sound v.checked.2.1
      v.checked.1.2.2.2.2.1 ha, m, hm, rfl⟩
  · rintro ⟨a, ha, b, hb, he⟩
    have : b = m := modifier_injective he
    subst b
    exact ⟨a, BehavioralStructural.ancestor_complete v.checked.2.1 ha, hb⟩

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Every effective modifier contributes every accepted attachment/formula.
The conclusion is the upstream model-wide modifier meaning, not table validity. -/
theorem expansions_agree (v : IR.BehavioralStructural.Validated k)
    (table : Vector (List Modifier) k) (τ : Clafer.Behavioral.Trace (Fin k) U)
    (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret v.core) τ) :
    (∀ item ∈ IR.Behavioral.Modifiers.expansions v table,
      (formula item.2).Attached τ
        (.sets (BehavioralStructural.interpret v.core).toEffectiveCore
          (Clafer.Behavioral.Structural.observed (BehavioralStructural.interpret v.core) τ))
        ((placement item.1).contexts (BehavioralStructural.interpret v.core) τ)) ↔
      Clafer.Behavioral.Modifiers.Holds (BehavioralStructural.interpret v.core) τ (declared table) := by
  simp only [IR.Behavioral.Modifiers.expansions, List.forall_mem_flatMap,
    List.mem_finRange, forall_const]
  simp_rw [Surface.Modifiers.expand_agrees _ τ valid, effective_agrees]
  unfold Clafer.Behavioral.Modifiers.Holds
  constructor
  · intro h d
    exact ⟨h d .initial, h d .final, h d .finalref, h d .finaltarget⟩
  · intro h d m hm
    cases m with
    | initial => exact (h d).1 hm
    | final => exact (h d).2.1 hm
    | finalref => exact (h d).2.2.1 hm
    | finaltarget => exact (h d).2.2.2 hm

end ClaferCompiler.SemanticsBridge.Behavioral.Modifiers
