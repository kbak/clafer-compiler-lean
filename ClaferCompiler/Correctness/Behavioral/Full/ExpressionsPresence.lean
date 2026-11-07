module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsSets
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSteps

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem Mixed.unary_some {U : Type} {f : U → Atom} {S : Set U}
    (rows : Mixed.Unary f S (r.eval s w τ e t)) :
    (Formula.mult .some r).Holds s w τ e t ↔ S.Nonempty := by
  change Backend.Alloy.Multiplicity.some.holds (r.eval s w τ e t).eraseDups.length = true ↔ _
  simp only [Backend.Alloy.Multiplicity.holds, decide_eq_true_eq]
  rw [List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨row, member⟩
    obtain ⟨x, hx, _⟩ := (rows row).mp (List.mem_eraseDups.mp member)
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨[f x], List.mem_eraseDups.mpr ((rows _).mpr ⟨x, hx, rfl⟩)⟩

namespace Sets
variable {U : Type} {v : IR.BehavioralStructural.Validated k}
  {s : Schema} {w : Nat} {σ : Clafer.Behavioral.Trace (Fin k) U} {τ : Trace}
  {f : U → Atom} {A : Set U} {c : Expressions.Context n}
  {ρ : Clafer.Behavioral.Environment U n} {e : Environment}

theorem present_built : (Expressions.present v c).Built := .mult _ _

theorem parentPresent_built : (Expressions.parentPresent v c).Built :=
  .binary .disj (.subset _ _) (.mult _ _)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem present_meaning (hp : PrimitiveRows v s w σ τ f A)
    (hc : ContextRows s w τ f A c ρ e) (t : Nat) :
    (Expressions.present v c).Holds s w τ e t ↔ ρ.this ∈ σ.live t := by
  have rows := Mixed.unary_inter hp.injective hc.this_term (observedLive_term v)
    (hc.this t) (hp.live e t)
  rw [Expressions.present, Mixed.unary_some rows]
  simp only [Set.inter_nonempty, Set.mem_singleton_iff, exists_eq_left, Set.mem_inter_iff]
  exact and_iff_left hc.this_inside

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The source context remains frozen while its actual parent is observed at
each time. Navigation does not require the captured context to be live. -/
theorem parentPresent_meaning (hp : PrimitiveRows v s w σ τ f A)
    (hc : ContextRows s w τ f A c ρ e) (t : Nat) :
    (Expressions.parentPresent v c).Holds s w τ e t ↔ σ.ParentPresent ρ.this t := by
  have rows := image_rows hp .parent True.intro hc.this_term (hc.this t)
    (Set.singleton_subset_iff.mpr hc.this_inside)
  rw [Expressions.parentPresent, Encoding.holds_or (.subset _ _) (.mult _ _),
    Mixed.unary_subset hp.injective (hc.this t) (hp.root e t), Mixed.unary_some rows]
  simp only [Set.singleton_subset_iff, Set.mem_singleton_iff]
  change (_ ∨ ∃ y, ∃ x ∈ ({ρ.this} : Set U),
    σ.identities.parent x = some y ∧ y ∈ σ.live t) ↔ _
  simp only [Set.mem_singleton_iff, exists_eq_left]
  rfl

end Sets
end ClaferCompiler.Correctness.Behavioral.Full
