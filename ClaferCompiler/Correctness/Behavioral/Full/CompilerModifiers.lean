module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCommands
public import ClaferCompiler.Correctness.Behavioral.Full.ModifierMeaning
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPlacement
public import ClaferCompiler.Correctness.Behavioral.Full.ModifierPrimitiveVacuity

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full
open IR.Behavioral

theorem paired_forall_mem {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    {xs : List α} {ys : List β} (paired : List.Forall₂ R xs ys)
    (meaning : ∀ x ∈ xs, ∀ y, R x y → (Q y ↔ P x)) :
    (∀ y ∈ ys, Q y) ↔ ∀ x ∈ xs, P x := by
  induction paired with
  | nil => simp
  | @cons x y xs ys related _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_congr (meaning x List.mem_cons_self y related)
      (ih (fun x member y related => meaning x (List.mem_cons_of_mem _ member) y related))

/-- One accepted modifier expansion on the full completed source carrier. -/
abbrev SourceModifierItem (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (source : ObservedLasso k o steps)
    (item : Surface.Modifiers.Placement k × Expression.Formula k 0) : Prop :=
  (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source)) completeIntegers item.2).PartialAttached
    (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation
    ((SemanticsBridge.Behavioral.Surface.Modifiers.placement item.1).contexts
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source))

namespace ModifierPlacement
variable (v : IR.BehavioralStructural.Validated k) (p : Fin k) (source : ObservedLasso k o steps)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem object (where_ : Surface.Modifiers.Placement k) (t : Nat) (x : Fin o) :
    (Sum.inl x ∈ (SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t ∧
      Sum.inl x ∈ (completeTrace v p source).live t) ↔
      x ∈ placementObjects v source where_ t := by
  cases where_ with
  | all => simp [SemanticsBridge.Behavioral.Surface.Modifiers.placement,
      Clafer.Behavioral.Modifiers.Placement.contexts, placementObjects]
  | heads d =>
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, h.1⟩
  | parents d =>
    change ((∃ q, (v.core.structural.get d).parent = some q ∧
      Sum.inl x ∈ ((completeTrace v p source).raw (Sets.model v) t).head q) ∧ _) ↔ _
    constructor
    · exact fun h => h.1
    · rintro ⟨q, parent, head⟩
      exact ⟨⟨q, parent, head⟩, head.1⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem integer (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (where_ : Surface.Modifiers.Placement k) (ordinary : OrdinaryPlacement v where_)
    (t : Nat) (z : Int)
    (member : Sum.inr z ∈ (SemanticsBridge.Behavioral.Surface.Modifiers.placement where_).contexts
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t) :
    where_ = .all := by
  cases where_ with
  | all => rfl
  | heads d =>
    have equal := (completeHead_integer v p primitive source t d z).mp member
    have hd := (integerDeclaration_eq v p primitive d).mpr equal.symm
    exact False.elim (by simp [OrdinaryPlacement, hd] at ordinary)
  | parents d =>
    obtain ⟨q, parent, head⟩ := member
    have equal := (completeHead_integer v p primitive source t q z).mp head
    subst q
    exact ((shape p primitive).2.2.2.2.2 d parent).elim

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem sourceItem (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (where_ : Surface.Modifiers.Placement k) (ordinary : OrdinaryPlacement v where_)
    (a : Expression.Formula k 0)
    (integers : where_ = .all → ∀ t z,
      (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) completeIntegers a).Satisfies
        (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
          (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation true
        (.closed (Sum.inr z)) t) :
    SourceModifierItem v p source (where_, a) ↔
      ∀ t x, x ∈ placementObjects v source where_ t →
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v)
          (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
            (completeTrace v p source)) completeIntegers a).Satisfies
          (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
            (completeTrace v p source)) SemanticsBridge.Behavioral.Expression.observation true
          (.closed (Sum.inl x)) t := by
  constructor
  · intro h t x hx
    obtain ⟨member, live⟩ := (object v p source where_ t x).mpr hx
    exact h t (Sum.inl x) member live
  · intro h t x member live
    cases x with
    | inl x => exact h t x ((object v p source where_ t x).mp ⟨member, live⟩)
    | inr z => exact integers (integer v p source primitive shape where_ ordinary t z member) t z

end ModifierPlacement

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem modifier_item_source (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (capacity : o ≤ b.objects) (shape : PrimitiveShape v)
    (model : Expressions.ModelRows v (estimates v b) (schema v) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) rep.labels)
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (d : Fin k) (modifier : Surface.Modifiers.Modifier)
    (item : Surface.Modifiers.Placement k × Expression.Formula k 0)
    (member : item ∈ modifierExpansions d modifier) (ordinary : OrdinaryPlacement v item.1)
    (result : Formula)
    (success : attached v b fuel (placement v item.1) item.2 = .ok result) :
    result.Holds (schema v) b.bitwidth target.unfold [] 0 ↔ SourceModifierItem v p source item := by
  rw [rep.placement_attached b fuel capacity shape (Expressions.lowerAt_preserves model fuel fuel)
    facts item.1 ordinary item.2 result success]
  apply Iff.symm
  apply ModifierPlacement.sourceItem v p source primitive shape item.1 ordinary item.2
  intro all t z
  cases modifier <;> simp only [modifierExpansions, List.mem_cons, List.not_mem_nil, or_false] at member
  · subst item; contradiction
  · rcases member with rfl | rfl
    · exact ModifierPrimitive.stable_integer v p source d (.heads d) z t
    · contradiction
  · subst item; contradiction
  · subst item
    exact ModifierPrimitive.stable_integer v p source d (.targets d) z t

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The executable conjunctive expansion list preserves the exact inherited
source modifier contract, including the primitive completion's live owners. -/
theorem modifiers_source (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer)
    (capacity : o ≤ b.objects) (shape : PrimitiveShape v)
    (model : Expressions.ModelRows v (estimates v b) (schema v) target.unfold
      (Clafer.Behavioral.Structural.observed (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source)) rep.labels)
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (valid : Clafer.Behavioral.Structural.Valid (SemanticsBridge.BehavioralStructural.interpret v.core)
      (completeTrace v p source))
    (table : Vector (List Surface.Modifiers.Modifier) k)
    (primitiveMetadata : ∀ d, integerDeclaration v d = true →
      IR.Behavioral.Modifiers.effective v table d = [])
    (results : List Formula)
    (success : ((List.finRange k).flatMap fun d =>
      (IR.Behavioral.Modifiers.effective v table d).flatMap (modifierExpansions d)).mapM
        (fun item => attached v b fuel (placement v item.1) item.2) = .ok results) :
    (∀ f ∈ results, f.Holds (schema v) b.bitwidth target.unfold [] 0) ↔
      Clafer.Behavioral.Modifiers.Holds (SemanticsBridge.BehavioralStructural.interpret v.core)
        (completeTrace v p source) (SemanticsBridge.Behavioral.Modifiers.declared table) := by
  rw [← modifierExpansions_source v table completeIntegers (completeTrace v p source) valid]
  have paired := Expressions.mapM_ok _ _ _ success
  apply paired_forall_mem paired
  intro item itemMember result success
  obtain ⟨d, _, declaration⟩ := List.mem_flatMap.mp itemMember
  obtain ⟨modifier, hm, member⟩ := List.mem_flatMap.mp declaration
  have ordinaryD : integerDeclaration v d = false := by
    cases h : integerDeclaration v d with
    | false => rfl
    | true => simp [primitiveMetadata d h] at hm
  have ordinary : OrdinaryPlacement v item.1 := by
    cases modifier <;> simp only [modifierExpansions, List.mem_cons, List.not_mem_nil, or_false] at member
    · subst item; trivial
    · rcases member with rfl | rfl
      · trivial
      · exact ordinaryD
    · subst item; exact ordinaryD
    · subst item; trivial
  exact rep.modifier_item_source b fuel p primitive capacity shape model facts
    d modifier item member ordinary result success

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
