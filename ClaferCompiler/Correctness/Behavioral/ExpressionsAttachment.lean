module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsDefined
public import ClaferCompiler.Correctness.Behavioral.RepresentationContext

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open Encoding

namespace Encoding

 theorem exists_repeat_built (r : Rel) (p : Formula) (hp : p.Built) (n : Nat) :
    (Nat.repeat (Formula.exists_ r) n p).Built := by
  induction n with
  | zero => exact hp
  | succ n ih => exact .exists_ r ih

theorem coverPool_built (capacity : Nat) (p : Formula) (hp : p.Built) :
    (coverPool capacity p).Built := exists_repeat_built _ _ (.binary .conj (.equal _ _) hp) _

theorem attached_built (v : IR.Structural.Layout k) (capacity : Nat) (d : Fin k)
    (a : IR.Behavioral.Formula k 0) (fuel : Nat) (h : sizeOf a < fuel) :
    (attached v capacity d a fuel h).Built :=
  coverPool_built _ _ (.unary .always (.all _ (formulaAt_built _ _ _ _ _).positive))

theorem exists_repeat_relational (r : Rel) (p : Formula) (hp : NoArithmetic p) (n : Nat) :
    NoArithmetic (Nat.repeat (Formula.exists_ r) n p) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (noArithmetic_exists _ _).mpr ih

theorem coverPool_relational (capacity : Nat) (p : Formula) (hp : NoArithmetic p) :
    NoArithmetic (coverPool capacity p) :=
  exists_repeat_relational _ _ ((noArithmetic_binary _ _ _).mpr ⟨noArithmetic_equal _ _, hp⟩) _

-- [proof->req~compiler-behavioral-correctness~1]
theorem attached_defined (v : IR.Structural.Layout k) (capacity : Nat) (d : Fin k)
    (a : IR.Behavioral.Formula k 0) (fuel : Nat) (h : sizeOf a < fuel)
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat) :
    (attached v capacity d a fuel h).Defined s w τ e t := by
  apply noArithmetic_defined (attached_built _ _ _ _ _ _)
  exact coverPool_relational _ _ ((noArithmetic_unary _ _).mpr
    ((noArithmetic_all _ _).mpr (formulaAt_relational _ _ _ _ _).2.1))

end Encoding

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Backend.Alloy.Temporal.Lasso}

-- [proof->req~compiler-behavioral-correctness~1]
theorem TraceRep.attached_body (rep : TraceRep v source target) (w : Nat)
    (objects : List (Fin o)) (cover : ∀ x, x ∈ objects) (d : Fin k)
    (a : IR.Behavioral.Formula k 0) (fuel : Nat) (h : sizeOf a < fuel) :
    (Formula.unary .always (.all (head v d)
      (formulaAt v fuel ⟨.var 0, Fin.elim0,
        (List.range objects.length).map fun i => .var (i + 1)⟩ a h).positive)).Holds
      (schema v) w target.unfold (objects.map fun x => .object (rep.label x)) 0 ↔
    ∀ t x, x ∈ ((SemanticsBridge.Behavioral.trace source).raw
      (SemanticsBridge.Structural.interpret v.core) t).head d →
      (SemanticsBridge.Behavioral.formula a).denote (SemanticsBridge.Behavioral.trace source)
        (.sets (SemanticsBridge.Structural.interpret v.core) (SemanticsBridge.Behavioral.trace source)) true (.closed x) t := by
  have hb := (formulaAt_built v fuel
    ⟨.var 0, Fin.elim0, (List.range objects.length).map fun i => .var (i + 1)⟩ a h).positive
  unfold Formula.Holds
  rw [Formula.fold_unary _ _ _ _ (.all _ hb)]
  change (∀ t, 0 ≤ t → (Formula.all (head v d) _).Holds (schema v) w target.unfold
    (objects.map fun x => .object (rep.label x)) t) ↔ _
  simp only [Nat.zero_le, forall_const]
  apply forall_congr'
  intro t
  rw [all_unary hb (rep.head_meaning w _ t d)]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  exact rep.formula_positive w _ _ _ (attachmentContext v w target.unfold rep.label x objects cover)
    t fuel a h

-- [proof->req~compiler-behavioral-correctness~1]
/-- The emitted attachment is equivalent to the source obligation for every
applicable live context. The capacity assumption only supplies a finite frozen
enumeration; it never truncates time or changes formula meaning. -/
theorem TraceRep.attached_meaning (rep : TraceRep v source target) (w capacity : Nat)
    (fits : o ≤ capacity) (d : Fin k) (a : IR.Behavioral.Formula k 0)
    (fuel : Nat) (h : sizeOf a < fuel) :
    (attached v capacity d a fuel h).Holds (schema v) w target.unfold [] 0 ↔
    ∀ t x, x ∈ ((SemanticsBridge.Behavioral.trace source).raw
      (SemanticsBridge.Structural.interpret v.core) t).head d →
      (SemanticsBridge.Behavioral.formula a).denote (SemanticsBridge.Behavioral.trace source)
        (.sets (SemanticsBridge.Structural.interpret v.core) (SemanticsBridge.Behavioral.trace source)) true (.closed x) t := by
  unfold attached
  rw [coverPool_meaning rep w capacity _
    (.unary .always (.all _ (formulaAt_built _ _ _ _ _).positive))]
  constructor
  · rintro ⟨objects, length, cover, hbody⟩
    apply (rep.attached_body w objects cover d a fuel h).mp
    simpa only [length] using hbody
  · intro hbody
    obtain ⟨objects, length, cover⟩ := padded_enumeration source capacity fits
    refine ⟨objects, length, cover, ?_⟩
    have hb := (rep.attached_body w objects cover d a fuel h).mpr hbody
    simpa only [length] using hb

end ClaferCompiler.Correctness.Behavioral
