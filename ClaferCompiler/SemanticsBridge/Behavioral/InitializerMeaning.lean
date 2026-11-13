module

public import ClaferCompiler.SemanticsBridge.Behavioral.InitializerEquations

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Initializers
open IR.Behavioral
open Clafer.Behavioral (Trace Environment)
open Clafer.Behavioral.Initializers (Meaning)
namespace Production
open Clafer.Behavioral.Initializers.Structure

variable {U : Type} (m : Clafer.Behavioral.Structural.Core k) (τ : Trace (Fin k) U)
  (R : Clafer.Constraints.IntegerRealization U)
  (valid : Clafer.Behavioral.Structural.Valid m τ) {d o : Fin k}
  (owner : Clafer.Behavioral.InheritedReference.Owner m.family d o)

abbrev headSet (d : Fin k) : SetExpr k n :=
  if (m.family.parent d).isSome then .thisStep (.child d) else .extent d

abbrev originalSet (d : Fin k) : SetExpr k n :=
  if (m.family.parent d).isSome then .thisStep .parent else .root

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem heads_agree (ρ : Environment U n) (t : Nat) :
    Clafer.Behavioral.Structural.eval m τ (setExpr (headSet m d)) ρ t = heads m τ d t ρ.this := by
  cases hp : m.family.parent d with
  | none => simp [headSet, hp, setExpr, Clafer.Behavioral.Structural.eval,
      Clafer.Behavioral.SetExpr.eval, heads]
  | some p =>
    ext x
    simp [headSet, hp, setExpr, step, Clafer.Behavioral.Structural.eval,
      Clafer.Behavioral.SetExpr.eval, Clafer.Behavioral.Step.image,
      Clafer.Behavioral.Step.relation, heads, Clafer.Behavioral.ReferenceObservation.heads,
      Clafer.Behavioral.Structural.current]

-- [proof->req~compiler-behavioral-elaboration~1]
include valid in
theorem original_agrees (ρ : Environment U n) (t : Nat) (p : U)
    (hp : p ∈ contexts m τ d t) (hx : ρ.this ∈ heads m τ d t p) :
    Clafer.Behavioral.Structural.eval m τ (setExpr (originalSet m d)) ρ t = {p} := by
  have origin := fiber_origin m τ hp hx
  cases parent : m.family.parent d with
  | none =>
    have same : p = τ.identities.root := by simpa [contexts, parent] using hp
    simp [originalSet, parent, setExpr, Clafer.Behavioral.Structural.eval,
      Clafer.Behavioral.SetExpr.eval, Clafer.Behavioral.Structural.observed, same]
  | some q =>
    have fixed : τ.identities.parent ρ.this = some p := by
      simpa [Clafer.Behavioral.Initializers.Structure.origin, parent,
        Clafer.Behavioral.Initializers.Transport.original] using origin
    simpa [originalSet, parent, setExpr, step] using
      parent_context m τ valid ρ t fixed (head_mem m τ hx).1

-- [proof->req~compiler-behavioral-elaboration~1]
theorem captured_target (ρ : Environment U n) (t : Nat) (x : U)
    (hx : x ∈ (τ.raw m.toEffectiveCore t).head d) :
    Clafer.Behavioral.Structural.eval m τ (setExpr (.step (.deref d) (.var 0))) (ρ.push {x}) t =
      {target m τ valid owner t x} := by
  ext y
  rw [show setExpr (.step (.deref d) (.var 0)) = .step (.deref d) (.var 0) from rfl,
    Clafer.Behavioral.Structural.captured_deref m τ valid]
  exact Set.ext_iff.mp (target_singleton m τ valid owner t x hx) y

-- [proof->req~compiler-behavioral-elaboration~1]
theorem singleton_equation (right : Expression.Collection k 0) (ρ : Environment U 0)
    (t : Nat) (p : U) (hp : p ∈ contexts m τ d t) (hx : ρ.this ∈ heads m τ d t p) :
    Holds (Clafer.Behavioral.Structural.observed m τ)
      (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
        (.quant .all (.set .this) (.atom (.inContext (originalSet m d)
          (.atom (.equalClosed (.step (.deref d) (.var 0)) right)))))) ρ t ↔
      rhs m τ R right (.closed p) t = some {target m τ valid owner t ρ.this} := by
  rw [all_holds]
  have this := Clafer.Behavioral.SetExpr.this_live m.toEffectiveCore
    (Clafer.Behavioral.Structural.observed m τ) ρ t (head_mem m τ hx).1
  change (∀ x ∈ Clafer.Behavioral.SetExpr.eval _ _ _ _ .this, _) ↔ _
  rw [this]
  simp only [Set.mem_singleton_iff, forall_eq, context_holds]
  have original := original_agrees m τ valid (ρ.push {ρ.this}) t p hp hx
  change (∀ x ∈ Clafer.Behavioral.Structural.eval m τ (setExpr (originalSet m d)) (ρ.push {ρ.this}) t, _) ↔ _
  rw [original]
  simp only [Set.mem_singleton_iff, forall_eq, equal_closed]
  change Expression.collection m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R right
    (.closed p) t = some (Clafer.Behavioral.Structural.eval m τ
      (setExpr (.step (.deref d) (.var 0))) ({ρ with this := p}.push {ρ.this}) t) ↔ _
  rw [captured_target m τ valid owner _ t ρ.this (head_mem m τ hx)]
  rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem targets_agree (ρ : Environment U n) (t : Nat) :
    Clafer.Behavioral.Structural.eval m τ (setExpr (.step (.deref d) (headSet m d))) ρ t =
      (view m τ valid owner).targets t ρ.this := by
  rw [target_image m τ valid owner]
  ext y
  change (∃ x ∈ Clafer.Behavioral.Structural.eval m τ (setExpr (headSet m d)) ρ t,
    (Clafer.Behavioral.Step.deref d).relation m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) t x y) ↔ _
  rw [heads_agree]
  exact exists_congr fun x => and_congr_right fun _ =>
    Clafer.Behavioral.Structural.observed_deref m τ valid t d x y

abbrev aggregateBody (right : Expression.Collection k 0) : Expression.Formula k 0 :=
  .quant .all (.set (headSet m d))
    (.atom (.equalClosed (.step (.deref d) (headSet m d)) right))

-- [proof->req~compiler-behavioral-elaboration~1]
theorem aggregate_agrees (right : Expression.Collection k 0) (ρ : Environment U 0) (t : Nat) :
    Holds (Clafer.Behavioral.Structural.observed m τ)
      (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
        (aggregateBody m (d := d) right)) ρ t ↔
      Clafer.Behavioral.Initializers.Candidate.Guarded (heads m τ d t ρ.this)
        ((view m τ valid owner).targets t ρ.this) (rhs m τ R right (.closed ρ.this) t) := by
  rw [aggregate_equation m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
    (headSet m d) (.step (.deref d) (headSet m d)) right ρ t
    ((view m τ valid owner).targets t ρ.this)
    (fun x _ => targets_agree m τ valid owner (ρ.push {x}) t)]
  rw [show (setExpr (headSet m d)).eval m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) ρ t = heads m τ d t ρ.this from heads_agree m τ ρ t]
  rfl

-- [proof->req~compiler-behavioral-elaboration~1]
theorem single_formula (right : Expression.Collection k 0) (t : Nat) (p : U)
    (hp : p ∈ contexts m τ d t) :
    Holds (Clafer.Behavioral.Structural.observed m τ)
      (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
        (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
          (some .instanceBirth) right)) (.closed p) t ↔
      ∀ x ∈ heads m τ d t p, τ.Starts t x →
        rhs m τ R right (.closed p) t = some {target m τ valid owner t x} := by
  change Holds _ (Expression.formula _ _ _ (.atom (.inContext (headSet m d)
    (.initially (.quant .all (.set .this) (.atom (.inContext (originalSet m d)
      (.atom (.equalClosed (.step (.deref d) (.var 0)) right))))))))) _ _ ↔ _
  rw [context_holds]
  change (∀ x ∈ Clafer.Behavioral.Structural.eval m τ (setExpr (headSet m d)) (.closed p) t, _) ↔ _
  rw [heads_agree]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro hx
  rw [initially_holds]
  apply imp_congr_right
  intro _
  exact singleton_equation m τ R valid owner right {Environment.closed p with this := x} t p hp hx

-- [proof->req~compiler-behavioral-elaboration~1]
/-- The generated instance clock satisfies the accepted production meaning over
actual structural fibers and inherited references, for the actual closed RHS. -/
theorem single_meaning (right : Expression.Collection k 0) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
        (some .instanceBirth) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    Meaning τ (view m τ valid owner) (rhs m τ R)
      ⟨d, origin m d, .instanceBirth, right⟩ := by
  rw [single_fibers m τ valid owner (rhs m τ R) right]
  constructor
  · intro h t p hp
    exact (single_formula m τ R valid owner right t p hp).mp
      (h t p hp (contexts_live m τ valid d t hp))
  · intro h t p hp _
    exact (single_formula m τ R valid owner right t p hp).mpr (h t p hp)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem every_meaning (right : Expression.Collection k 0) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (aggregateBody m (d := d) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    Meaning τ (view m τ valid owner) (rhs m τ R) ⟨d, origin m d, .everyLive, right⟩ := by
  constructor
  · intro h t p hp live
    exact (aggregate_agrees m τ R valid owner right (.closed p) t).mp (h t p hp live)
  · intro h t p hp live
    exact (aggregate_agrees m τ R valid owner right (.closed p) t).mpr (h t p hp live)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem collection_meaning (right : Expression.Collection k 0) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
        (some .parentBirth) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    Meaning τ (view m τ valid owner) (rhs m τ R) ⟨d, origin m d, .parentBirth, right⟩ := by
  change (Expression.formula _ _ _ (aggregateBody m (d := d) right)).initially.PartialAttached _ _ _ ↔ _
  rw [Clafer.Behavioral.Anchors.initially_at_births]
  constructor
  · intro h t p hp birth
    exact (aggregate_agrees m τ R valid owner right (.closed p) t).mp (h t p hp birth)
  · intro h t p hp birth
    exact (aggregate_agrees m τ R valid owner right (.closed p) t).mpr (h t p hp birth)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem global_meaning (right : Expression.Collection k 0) (parentless : m.family.parent d = none) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
        (some .globalZero) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    Meaning τ (view m τ valid owner) (rhs m τ R) ⟨d, origin m d, .globalZero, right⟩ := by
  change (Expression.formula _ _ _ (aggregateBody m (d := d) right)).initially.PartialAttached _ _ _ ↔ _
  rw [Clafer.Behavioral.Anchors.initially_at_births]
  have context : contexts m τ d = fun _ => {τ.identities.root} := by
    funext t
    simp [contexts, parentless]
  change (∀ t p, p ∈ contexts m τ d t → τ.Starts t p → _) ↔ _
  simp only [show ∀ t p, (Expression.formula m.toEffectiveCore
      (Clafer.Behavioral.Structural.observed m τ) R (aggregateBody m (d := d) right)).Satisfies
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation true (.closed p) t ↔
        Clafer.Behavioral.Initializers.Candidate.Guarded (heads m τ d t p)
          ((view m τ valid owner).targets t p) (rhs m τ R right (.closed p) t) from
      fun t p => aggregate_agrees m τ R valid owner right (.closed p) t, context]
  exact Clafer.Behavioral.Initializers.Candidate.permanent_context_iff τ τ.identities.root
    valid.root_live (heads m τ d) (view m τ valid owner).targets (fun t p => rhs m τ R right (.closed p) t)

-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- With no authored temporal feature every accepted initializer uses the
ordinary aggregate equation. Generated anchors cannot select the source profile. -/
theorem static_formula (clock : Option Frontend.Behavioral.Initializers.Clock)
    (right : Expression.Collection k 0) :
    Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true false clock right =
      aggregateBody m (d := d) right := by
  simp [Frontend.Behavioral.initializerFormula, Frontend.Behavioral.initializerSingle, aggregateBody, headSet]

include valid owner in
-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- Finalref is sufficient only with stable complete RHS observations (including
undefinedness) and independent singleton/scalar admission. -/
theorem finalref_equivalence (right : Expression.Collection k 0)
    (final : Clafer.Behavioral.Modifiers.FinalRef m τ d)
    (admission : ∀ t p, p ∈ contexts m τ d t →
      (heads m τ d t p).Subsingleton ∨
        ∀ S, rhs m τ R right (.closed p) t = some S → S.Subsingleton)
    (stable : ∀ x, Clafer.Behavioral.Modifiers.Stable (fun j => x ∈ τ.live j)
      (fun j => (Clafer.Behavioral.Initializers.Transport.original τ.identities (origin m d) x).bind
        (fun p => rhs m τ R right (.closed p) j))) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
        (some .instanceBirth) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (aggregateBody m (d := d) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) :=
  (single_meaning m τ R valid owner right).trans
    ((Clafer.Behavioral.Initializers.Finality.production_equivalence m τ valid owner final
      (rhs m τ R) right admission stable).trans (every_meaning m τ R valid owner right).symm)

-- [proof->req~compiler-behavioral-structural-bridge~1]
include valid in
theorem attachment_contexts (d : Fin k) :
    (fun t => (τ.raw m.toEffectiveCore t).head ((m.family.parent d).getD m.family.root)) =
      contexts m τ d := by
  funext t
  cases parent : m.family.parent d with
  | some p => simp [contexts, parent]
  | none =>
    simp only [contexts, parent, Option.getD_none]
    exact Set.ext (fun x => (valid.states t).root_head x)

-- [proof->req~compiler-behavioral-structural-bridge~1]
/-- Constant-live specialization reuses the accepted aggregate bridge with the
actual closed RHS, without requiring definedness for absent heads. -/
theorem single_constant_aggregate (right : Expression.Collection k 0)
    (live : ∀ t, τ.live t = τ.live 0)
    (admission : ∀ p ∈ contexts m τ d 0,
      (heads m τ d 0 p).Subsingleton ∨
        ∀ S, rhs m τ R right (.closed p) 0 = some S → S.Subsingleton) :
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerFormula d (m.family.parent d).isSome true true
        (some .instanceBirth) right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation (contexts m τ d) ↔
    Clafer.Behavioral.Initializers.Candidate.Static (τ.live 0) (contexts m τ d 0)
      (heads m τ d 0) ((view m τ valid owner).targets 0) (fun p => rhs m τ R right (.closed p) 0) :=
  (single_meaning m τ R valid owner right).trans
    (Clafer.Behavioral.Initializers.Compatibility.single_constant_aggregate m τ valid owner
      (rhs m τ R) right live admission)

end Production

-- [proof->req~compiler-behavioral-elaboration~1]
theorem body_expansion {source : Frontend.Behavioral.Document}
    (b : Frontend.Behavioral.BoundDeclarations source)
    (p : Frontend.Behavioral.BoundHeaderProperty b.resolved.candidate.core)
    (clock : Option Frontend.Behavioral.Initializers.Clock)
    (right : Expression.Collection b.resolved.count 0)
    (reference : (IR.BehavioralSupport.referenceView b.resolved.admitted p.declaration).isSome = true) :
    Frontend.Behavioral.initializerBody b p clock right =
      Frontend.Behavioral.initializerFormula p.declaration
        ((BehavioralStructural.interpret b.resolved.admitted.core).family.parent p.declaration).isSome
        true source.temporal clock right := by
  unfold Frontend.Behavioral.initializerBody
  rw [reference, b.resolved.sameCore]
  rfl

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Certified classification of the authored header selects the production
meaning of the actual generated formula. Reference and validity premises describe
structural observations; neither supplies initializer truth. -/
theorem body_meaning {U : Type} {source : Frontend.Behavioral.Document}
    (b : Frontend.Behavioral.BoundDeclarations source)
    (p : Frontend.Behavioral.BoundHeaderProperty b.resolved.candidate.core)
    (right : Expression.Collection b.resolved.count 0) (header : Frontend.Behavioral.Header)
    (op : Frontend.Token) (clock : Option Frontend.Behavioral.Initializers.Clock)
    (classification : Frontend.Behavioral.InitializerClassification b p header op right clock)
    (reference : (IR.BehavioralSupport.referenceView b.resolved.admitted p.declaration).isSome = true)
    (τ : Trace (Fin b.resolved.count) U) (R : Clafer.Constraints.IntegerRealization U)
    (valid : Clafer.Behavioral.Structural.Valid (BehavioralStructural.interpret b.resolved.admitted.core) τ)
    {o : Fin b.resolved.count}
    (owner : Clafer.Behavioral.InheritedReference.Owner
      (BehavioralStructural.interpret b.resolved.admitted.core).family p.declaration o) :
    let m := BehavioralStructural.interpret b.resolved.admitted.core
    (Expression.formula m.toEffectiveCore (Clafer.Behavioral.Structural.observed m τ) R
      (Frontend.Behavioral.initializerBody b p clock right)).PartialAttached
      (Clafer.Behavioral.Structural.observed m τ) Expression.observation
      (Clafer.Behavioral.Initializers.Structure.contexts m τ p.declaration) ↔
    Clafer.Behavioral.Initializers.Meaning τ (Clafer.Behavioral.Initializers.Structure.view m τ valid owner) (rhs m τ R)
      ⟨p.declaration, Clafer.Behavioral.Initializers.Structure.origin m p.declaration,
        if source.temporal then productionClock clock else .everyLive, right⟩ := by
  dsimp only
  rw [body_expansion b p clock right reference]
  cases temporal : source.temporal with
  | false =>
    rw [Production.static_formula]
    exact Production.every_meaning _ τ R valid owner right
  | true =>
    cases clock with
    | none => exact Production.every_meaning _ τ R valid owner right
    | some c =>
      cases c with
      | instanceBirth => exact Production.single_meaning _ τ R valid owner right
      | parentBirth => exact Production.collection_meaning _ τ R valid owner right
      | globalZero =>
        apply Production.global_meaning _ τ R valid owner right
        rcases classification with ⟨_, impossible⟩ | ⟨_, c, selected, eq⟩
        · cases impossible
        · cases Option.some.inj eq
          have parent := global_parentless _ _ selected
          change (b.resolved.candidate.core.get p.declaration).parent.isSome = false at parent
          rw [b.resolved.sameCore]
          change (b.resolved.candidate.core.get p.declaration).parent = none
          cases h : (b.resolved.candidate.core.get p.declaration).parent <;> simp_all

end ClaferCompiler.SemanticsBridge.Behavioral.Initializers
