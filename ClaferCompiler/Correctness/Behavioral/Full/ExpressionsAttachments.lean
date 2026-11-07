module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsAttachmentContext
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaQuantifiers
public import ClaferCompiler.Correctness.Behavioral.Full.StructureReachability

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open IR.Behavioral

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem attached_built (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (owners : Rel) (a : Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result) : result.Built := by
  have built : SyntaxBuilt.Success Formula.Built (attached v b fuel owners a) := by
    unfold attached
    apply SyntaxBuilt.bind_any (Q := Formula.Built)
    intro _
    apply SyntaxBuilt.bind (Q := Formula.Built)
      ((SyntaxBuilt.lowerAt v (estimates v b) fuel fuel).formula _ a)
    intro body hb
    apply SyntaxBuilt.pure
    exact Behavioral.exists_many_built b.objects _
      (.binary .conj (.equal _ _) (.unary .always
        (.all _ (.binary .conj hb.defined hb.truth.positive))))
  exact built result success

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem constraint_built (v : IR.BehavioralStructural.Validated k) (b : Bounds) (fuel : Nat)
    (a : Constraint k) (result : Formula) (success : constraint v b fuel a = .ok result) : result.Built := by
  cases ordinary : integerDeclaration v a.owner with
  | true =>
    change (if integerDeclaration v a.owner = true then Except.error (error "behavioral.infinite-attachment")
      else attached v b fuel (head v a.owner) a.body) = .ok result at success
    rw [ordinary] at success
    contradiction
  | false =>
    apply attached_built v b fuel (head v a.owner) a.body result
    simpa only [constraint, ordinary, Bool.false_eq_true, ↓reduceIte] using success

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}
  {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The actual attachment binds a trace-wide object cover and evaluates the
original strict source formula at every applicable object and every time. -/
theorem attached_meaning (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (capacity : o ≤ b.objects)
    (pass : Expressions.PassObservation v (estimates v b) (schema v) target.unfold σ rep.labels
      (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel))
    (owners : Rel) (D : Nat → Set (Fin o))
    (ownerRows : ∀ e t, Relations.Unary rep.label (D t) (owners.eval (schema v) b.bitwidth target.unfold e t))
    (rootOwner : owners = head v v.core.structural.root → ∀ t x, x ∈ D t → x = source.objects.identities.root)
    (a : Expression.Formula k 0) (result : Formula)
    (success : attached v b fuel owners a = .ok result) :
    result.Holds (schema v) b.bitwidth target.unfold [] 0 ↔
      ∀ t x, x ∈ D t →
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a).Satisfies
          σ SemanticsBridge.Behavioral.Expression.observation true (.closed (Sum.inl x)) t := by
  classical
  let ctx := if owners == head v v.core.structural.root then
    { context b with lexical := { (context b).lexical with this := root v } } else context b
  change (do
    let _ ← Expression.Ranges.analyze (estimates v b) fuel a #v[]
    let body ← (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel).formula ctx a
    pure (Backend.Alloy.Behavioral.coverPool b.objects
      (.unary .always (.all owners (Backend.Alloy.Behavioral.Partial.satisfaction body true))))) = .ok result at success
  cases analyzed : Expression.Ranges.analyze (estimates v b) fuel a #v[] with
  | error err => rw [analyzed] at success; contradiction
  | ok checked =>
    simp only [analyzed, bind, Except.bind] at success
    cases lowered : (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel).formula ctx a with
    | error err => rw [lowered] at success; contradiction
    | ok body =>
      have resultEq : result = Backend.Alloy.Behavioral.coverPool b.objects
          (.unary .always (.all owners (Backend.Alloy.Behavioral.Partial.satisfaction body true))) := by
        rw [lowered] at success
        exact (Except.ok.inj success).symm
      subst result
      have built := (SyntaxBuilt.lowerAt v (estimates v b) fuel fuel).formula ctx a body lowered
      have satisfactionBuilt : (Backend.Alloy.Behavioral.Partial.satisfaction body true).Built :=
        .binary .conj built.defined built.truth.positive
      have propertyBuilt : (Formula.unary .always (.all owners
          (Backend.Alloy.Behavioral.Partial.satisfaction body true))).Built :=
        .unary .always (.all _ satisfactionBuilt)
      have bodyMeaning (objects : List (Fin o)) (length : objects.length = b.objects)
          (cover : ∀ x, x ∈ objects) :
          (Formula.unary .always (.all owners (Backend.Alloy.Behavioral.Partial.satisfaction body true))).Holds
            (schema v) b.bitwidth target.unfold (objects.map (fun x => .object (rep.label x))) 0 ↔
          ∀ t x, x ∈ D t →
            (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a).Satisfies
              σ SemanticsBridge.Behavioral.Expression.observation true (.closed (Sum.inl x)) t := by
        unfold Formula.Holds
        rw [Formula.fold_unary _ _ _ _ (.all _ satisfactionBuilt)]
        change (∀ t, 0 ≤ t → (Formula.all owners _).Holds (schema v) b.bitwidth target.unfold
          (objects.map fun x => .object (rep.label x)) t) ↔ _
        simp only [Nat.zero_le, forall_const]
        apply forall_congr'
        intro t
        rw [Mixed.all_unary satisfactionBuilt (ownerRows _ t)]
        apply forall_congr'
        intro x
        apply imp_congr_right
        intro hx
        have lexical : Expressions.LexicalRows (estimates v b) (schema v) target.unfold rep.labels ctx
            (.closed (Sum.inl x)) (.object (rep.label x) :: objects.map (fun x => .object (rep.label x))) := by
          dsimp only [ctx]
          split
          · next eq =>
            have equal : x = source.objects.identities.root := rootOwner (beq_iff_eq.mp eq) t x hx
            subst x
            exact rep.root_attachmentContext b objects length cover
          · exact Expressions.attachmentContext v b (schema v) target.unfold rep.labels x objects length cover
        have bound : Expression.Ranges.FormulaBound (estimates v b) ctx.estimates a := by
          dsimp only [ctx]
          split <;> exact checked.property
        exact (pass.formula lexical t a body bound lowered).satisfaction true
      rw [rep.coverPool_meaning b.bitwidth b.objects _ propertyBuilt]
      constructor
      · rintro ⟨objects, length, cover, holds⟩
        exact (bodyMeaning objects length cover).mp holds
      · intro holds
        obtain ⟨objects, length, cover⟩ := Behavioral.padded_enumeration source.objects b.objects capacity
        exact ⟨objects, length, cover, (bodyMeaning objects length cover).mpr holds⟩

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The emitted root-state fact supplies the specialization law for any object
placement with the same relation syntax as the root head. -/
theorem owner_root (rep : TraceRep v source target) (w : Nat)
    (owners : Rel) (D : Nat → Set (Fin o))
    (rows : ∀ e t, Relations.Unary rep.label (D t) (owners.eval (schema v) w target.unfold e t))
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) w target.unfold [] t)
    (same : owners = head v v.core.structural.root) (t : Nat) (x : Fin o) (hx : x ∈ D t) :
    x = source.objects.identities.root := by
  have member := (rows [] t [.object (rep.label x)]).mpr ⟨x, hx, rfl⟩
  rw [same] at member
  have equal := facts t (.equal (head v v.core.structural.root) (root v)) (by simp [stateFacts])
  obtain ⟨y, hy, he⟩ := (rep.root_meaning w [] t [.object (rep.label x)]).mp ((equal _).mp member)
  have labels : rep.label x = rep.label y := by simpa using he
  exact (rep.label_injective labels).trans (Set.mem_singleton_iff.mp hy)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem constraint_meaning (rep : TraceRep v source target) (b : Bounds) (fuel : Nat)
    (capacity : o ≤ b.objects)
    (pass : Expressions.PassObservation v (estimates v b) (schema v) target.unfold σ rep.labels
      (Backend.Alloy.Behavioral.Full.Expressions.lowerAt v (estimates v b) fuel fuel))
    (facts : ∀ t f, f ∈ stateFacts v → f.Holds (schema v) b.bitwidth target.unfold [] t)
    (a : Constraint k) (result : Formula) (success : constraint v b fuel a = .ok result) :
    result.Holds (schema v) b.bitwidth target.unfold [] 0 ↔
      ∀ t x, x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head a.owner →
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a.body).Satisfies
          σ SemanticsBridge.Behavioral.Expression.observation true (.closed (Sum.inl x)) t := by
  cases ordinary : integerDeclaration v a.owner with
  | true =>
    change (if integerDeclaration v a.owner = true then Except.error (error "behavioral.infinite-attachment")
      else attached v b fuel (head v a.owner) a.body) = .ok result at success
    rw [ordinary] at success
    contradiction
  | false =>
    have run : attached v b fuel (head v a.owner) a.body = .ok result := by
      simpa only [constraint, ordinary, Bool.false_eq_true, ↓reduceIte] using success
    exact rep.attached_meaning b fuel capacity pass (head v a.owner) _
      (fun e t => rep.head_source b.bitwidth e t a.owner ordinary)
      (rep.owner_root b.bitwidth (head v a.owner) _
        (fun e t => rep.head_source b.bitwidth e t a.owner ordinary) facts) a.body result run

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
