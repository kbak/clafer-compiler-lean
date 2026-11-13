module

public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionFormula

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full IR.BehavioralStructural
open SemanticsBridge.Behavioral.Expression

theorem conditional_map {A B : Type} (f : A → B) (c : Option Bool) (a b : Option A) :
    IR.BehavioralArithmetic.conditional c (a.map f) (b.map f) =
      (IR.BehavioralArithmetic.conditional c a b).map f := by
  cases c with
  | none => rfl
  | some value => cases value <;> cases a <;> cases b <;> rfl

namespace ObservesCompletion
variable {U : Type} {v : Validated k} {p : Fin k} {l : ObservedLasso k o steps}
  {τ : Clafer.Behavioral.Trace (Fin k) U} {R : Clafer.Constraints.IntegerRealization U}
  {objects : Fin o ↪ U}

local notation "M" => SemanticsBridge.BehavioralStructural.interpret v.core
local notation "CT" => Clafer.Behavioral.Structural.observed M (completeTrace v p l)
local notation "ST" => Clafer.Behavioral.Structural.observed M τ

mutual
  -- [proof->req~compiler-full-behavioral-correctness~1]
  theorem collection_image (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Collection k n)
      (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
      collection (M).toEffectiveCore ST R e (h.environment ρ) t =
        (collection (M).toEffectiveCore CT completeIntegers e ρ t).map (Set.image h.embedding) := by
    cases e with
    | set a => exact congrArg some (h.setExpr_image ρ t (SemanticsBridge.Behavioral.setExpr a)).symm
    | literal z => exact congrArg some (by simp)
    | integer a =>
      change (integer (M).toEffectiveCore ST R a (h.environment ρ) t).map _ =
        ((integer (M).toEffectiveCore CT completeIntegers a ρ t).map
          (fun z => {completeIntegers.encode z})).map (Set.image h.embedding)
      rw [integer_image h a]
      simp only [Option.map_map, Function.comp_def, Set.image_singleton]
      rfl
    | extreme op a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).bind _ =
        ((collection (M).toEffectiveCore CT completeIntegers a ρ t).bind
          ((SemanticsBridge.Behavioral.Primitive.extreme op).select completeIntegers)).map (Set.image h.embedding)
      rw [collection_image h a]
      cases value : collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S => exact h.select_image (SemanticsBridge.Behavioral.Primitive.extreme op) S
    | union a b =>
      change Clafer.Constraints.lift₂ (· ∪ ·)
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collection (M).toEffectiveCore ST R b (h.environment ρ) t) = (Clafer.Constraints.lift₂ (· ∪ ·)
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collection (M).toEffectiveCore CT completeIntegers b ρ t)).map (Set.image h.embedding)
      rw [collection_image h a, collection_image h b]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collection (M).toEffectiveCore CT completeIntegers b ρ t <;>
        simp [Clafer.Constraints.lift₂, Set.image_union]
    | inter a b =>
      change Clafer.Constraints.lift₂ (· ∩ ·)
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collection (M).toEffectiveCore ST R b (h.environment ρ) t) = (Clafer.Constraints.lift₂ (· ∩ ·)
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collection (M).toEffectiveCore CT completeIntegers b ρ t)).map (Set.image h.embedding)
      rw [collection_image h a, collection_image h b]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collection (M).toEffectiveCore CT completeIntegers b ρ t <;>
        simp [Clafer.Constraints.lift₂, Set.image_inter h.embedding.injective]
    | diff a b =>
      change Clafer.Constraints.lift₂ (· \ ·)
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collection (M).toEffectiveCore ST R b (h.environment ρ) t) = (Clafer.Constraints.lift₂ (· \ ·)
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collection (M).toEffectiveCore CT completeIntegers b ρ t)).map (Set.image h.embedding)
      rw [collection_image h a, collection_image h b]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collection (M).toEffectiveCore CT completeIntegers b ρ t <;>
        simp [Clafer.Constraints.lift₂, Set.image_sdiff h.embedding.injective]
    | step s a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).map _ =
        ((collection (M).toEffectiveCore CT completeIntegers a ρ t).map
          ((SemanticsBridge.Behavioral.step s).image (M).toEffectiveCore CT t)).map (Set.image h.embedding)
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S => exact congrArg some (h.step_image t (SemanticsBridge.Behavioral.step s) S).symm
    | ofType d a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).map _ =
        ((collection (M).toEffectiveCore CT completeIntegers a ρ t).map
          (fun S => {x | x ∈ S ∧ (M).toEffectiveCore.Ancestor ((CT).identities.directType x) d})).map
            (Set.image h.embedding)
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S =>
        apply congrArg some
        ext y
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, typed⟩
          exact ⟨x, ⟨hx, (h.type_eq x) ▸ typed⟩, rfl⟩
        · rintro ⟨x, ⟨hx, typed⟩, rfl⟩
          exact ⟨⟨x, hx, rfl⟩, (h.type_eq x).symm ▸ typed⟩
    | ite c a b =>
      rw [collection_ite, collection_ite, condition_observed, condition_observed,
        (formula_transport h c).condition, collection_image h a, collection_image h b]
      exact conditional_map _ _ _ _
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  theorem integer_image (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Integer k n)
      (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
      integer (M).toEffectiveCore ST R e (h.environment ρ) t =
        integer (M).toEffectiveCore CT completeIntegers e ρ t := by
    cases e with
    | literal z => rfl
    | coerce a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).bind _ =
        (collection (M).toEffectiveCore CT completeIntegers a ρ t).bind (Clafer.Behavioral.IntegerObservation.coerce completeIntegers)
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S => exact h.coerce_image S
    | extract a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).bind _ =
        (collection (M).toEffectiveCore CT completeIntegers a ρ t).bind (completeIntegers.extract)
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S => exact h.extract_image S
    | cardinality a =>
      change ((collection (M).toEffectiveCore ST R a (h.environment ρ) t).bind _).map _ =
        ((collection (M).toEffectiveCore CT completeIntegers a ρ t).bind Clafer.Constraints.finiteCard).map ULift.down
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t with
      | none => rfl
      | some S => exact finiteCard_image h.embedding S
    | binary op a b =>
      change (SemanticsBridge.BehavioralArithmetic.binary op).eval
        (integer (M).toEffectiveCore ST R a (h.environment ρ) t)
        (integer (M).toEffectiveCore ST R b (h.environment ρ) t) = _
      rw [integer_image h a, integer_image h b]
      rfl
    | negate a =>
      change (integer (M).toEffectiveCore ST R a (h.environment ρ) t).map _ = _
      rw [integer_image h a]
      rfl
    | fold op ds body =>
      change (collections (M).toEffectiveCore ST R ds (h.environment ρ) t).bind _ =
        (collections (M).toEffectiveCore CT completeIntegers ds ρ t).bind (fun sets =>
          (SemanticsBridge.BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
            (fun ix => integer (M).toEffectiveCore CT completeIntegers body (ρ.push {ix.2}) t))
      rw [collections_image h ds]
      cases collections (M).toEffectiveCore CT completeIntegers ds ρ t with
      | none => rfl
      | some sets =>
        change (SemanticsBridge.BehavioralArithmetic.fold op).eval
          (Clafer.Behavioral.PrimitiveExpression.occurrences (sets.map (Set.image h.embedding))) _ = _
        rw [← occurrences_image h.embedding sets]
        apply fold_image (occurrenceEmbedding h.embedding sets)
        intro ix _
        change integer (M).toEffectiveCore ST R body ((h.environment ρ).push {h.embedding ix.2}) t = _
        rw [MeaningTransport.push_singleton]
        exact integer_image h body _ t
    | ite c a b =>
      rw [integer_ite, integer_ite, condition_observed, condition_observed,
        (formula_transport h c).condition, integer_image h a, integer_image h b]
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  theorem collections_image (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Collections k n)
      (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
      collections (M).toEffectiveCore ST R e (h.environment ρ) t =
        (collections (M).toEffectiveCore CT completeIntegers e ρ t).map
          (List.map (Set.image h.embedding)) := by
    cases e with
    | nil => rfl
    | cons a ds =>
      change Clafer.Constraints.lift₂ List.cons
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collections (M).toEffectiveCore ST R ds (h.environment ρ) t) =
        (Clafer.Constraints.lift₂ List.cons
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collections (M).toEffectiveCore CT completeIntegers ds ρ t)).map (List.map (Set.image h.embedding))
      rw [collection_image h a, collections_image h ds]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collections (M).toEffectiveCore CT completeIntegers ds ρ t <;> rfl
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  theorem predicate_image (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Predicate k n)
      (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
      predicate (M).toEffectiveCore ST R e (h.environment ρ) t =
        predicate (M).toEffectiveCore CT completeIntegers e ρ t := by
    cases e with
    | inhabited a =>
      change (collection (M).toEffectiveCore ST R a (h.environment ρ) t).map Set.Nonempty =
        (collection (M).toEffectiveCore CT completeIntegers a ρ t).map Set.Nonempty
      rw [collection_image h a]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;> simp
    | equal a b =>
      change Clafer.Constraints.lift₂ (· = ·)
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collection (M).toEffectiveCore ST R b (h.environment ρ) t) =
        Clafer.Constraints.lift₂ (· = ·)
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collection (M).toEffectiveCore CT completeIntegers b ρ t)
      rw [collection_image h a, collection_image h b]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collection (M).toEffectiveCore CT completeIntegers b ρ t <;>
        simp [Clafer.Constraints.lift₂, (Set.image_injective.mpr h.embedding.injective).eq_iff]
    | subset a b =>
      change Clafer.Constraints.lift₂ (· ⊆ ·)
        (collection (M).toEffectiveCore ST R a (h.environment ρ) t)
        (collection (M).toEffectiveCore ST R b (h.environment ρ) t) =
        Clafer.Constraints.lift₂ (· ⊆ ·)
          (collection (M).toEffectiveCore CT completeIntegers a ρ t)
          (collection (M).toEffectiveCore CT completeIntegers b ρ t)
      rw [collection_image h a, collection_image h b]
      cases collection (M).toEffectiveCore CT completeIntegers a ρ t <;>
        cases collection (M).toEffectiveCore CT completeIntegers b ρ t <;>
        simp [Clafer.Constraints.lift₂, Set.image_subset_image_iff h.embedding.injective]
    | integerEqual a b =>
      change Clafer.Constraints.lift₂ (· = ·)
        (integer (M).toEffectiveCore ST R a (h.environment ρ) t)
        (integer (M).toEffectiveCore ST R b (h.environment ρ) t) = _
      rw [integer_image h a, integer_image h b]
      rfl
    | less a b =>
      change Clafer.Constraints.lift₂ (· < ·)
        (integer (M).toEffectiveCore ST R a (h.environment ρ) t)
        (integer (M).toEffectiveCore ST R b (h.environment ρ) t) = _
      rw [integer_image h a, integer_image h b]
      rfl
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  theorem atom_image (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Atom k n)
      (ρ : Clafer.Behavioral.Environment (Completion o) n) (t : Nat) :
      atom (M).toEffectiveCore ST R e (h.environment ρ) t =
        atom (M).toEffectiveCore CT completeIntegers e ρ t := by
    cases e with
    | primitive a => exact predicate_image h a ρ t
    | equalClosed a d =>
      change (collection (M).toEffectiveCore ST R d (.closed (h.environment ρ).this) t).map _ =
        (collection (M).toEffectiveCore CT completeIntegers d (.closed ρ.this) t).map _
      have closed : Clafer.Behavioral.Environment.closed (h.environment ρ).this =
          h.environment (.closed ρ.this) := by
        unfold environment Clafer.Behavioral.Environment.closed
        congr 1
        funext i
        exact Fin.elim0 i
      rw [closed, collection_image h d]
      have image := h.setExpr_image ρ t (SemanticsBridge.Behavioral.setExpr a)
      unfold Clafer.Behavioral.Structural.eval at image
      rw [← image]
      cases collection (M).toEffectiveCore CT completeIntegers d (.closed ρ.this) t with
      | none => rfl
      | some S =>
        apply congrArg some
        exact propext (Set.image_injective.mpr h.embedding.injective).eq_iff
    | inContext d body =>
      classical
      change contextObservation (M).toEffectiveCore ST d (formula (M).toEffectiveCore ST R body)
        (h.environment ρ) t =
        contextObservation (M).toEffectiveCore CT d (formula (M).toEffectiveCore CT completeIntegers body) ρ t
      unfold contextObservation
      have image := h.setExpr_image ρ t (SemanticsBridge.Behavioral.setExpr d)
      unfold Clafer.Behavioral.Structural.eval at image
      dsimp only
      rw [← image]
      simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      have domains : (∀ x ∈ (SemanticsBridge.Behavioral.setExpr d).eval (M).toEffectiveCore CT ρ t,
          (formula (M).toEffectiveCore ST R body).Defined ST observation
            {h.environment ρ with this := h.embedding x} t) ↔
        (∀ x ∈ (SemanticsBridge.Behavioral.setExpr d).eval (M).toEffectiveCore CT ρ t,
          (formula (M).toEffectiveCore CT completeIntegers body).Defined CT observation {ρ with this := x} t) := by
        apply forall_congr'
        intro x
        apply imp_congr_right
        intro _
        rw [observed_formula_defined, observed_formula_defined]
        exact (formula_transport h body).defined {ρ with this := x} t
      simp only [domains]
      split
      · apply congrArg some
        apply propext
        apply forall_congr'
        intro x
        apply imp_congr_right
        intro _
        rw [observed_formula_raw, observed_formula_raw]
        exact (formula_transport h body).raw {ρ with this := x} t
      · rfl
    | count q arity disjoint d body =>
      change countObservation ST q arity disjoint
        (collection (M).toEffectiveCore ST R d) (formula (M).toEffectiveCore ST R body) _ _ =
        countObservation CT q arity disjoint
          (collection (M).toEffectiveCore CT completeIntegers d) (formula (M).toEffectiveCore CT completeIntegers body) _ _
      rw [count_observed, count_observed]
      exact MeaningTransport.count q disjoint (collection_image h d) (formula_transport h body) ρ t
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp
    all_goals omega

  -- [proof->req~compiler-full-behavioral-correctness~1]
  theorem formula_transport (h : ObservesCompletion v p l τ R objects)
      (e : IR.Behavioral.Expression.Formula k n) :
      MeaningTransport h (formula (M).toEffectiveCore CT completeIntegers e)
        (formula (M).toEffectiveCore ST R e) :=
    match e with
    | .truth => MeaningTransport.truth
    | .atom a => MeaningTransport.atom (atom_image h a)
    | .not a => (formula_transport h a).not
    | .and a b => (formula_transport h a).and (formula_transport h b)
    | .or a b => (formula_transport h a).or (formula_transport h b)
    | .implies a b => (formula_transport h a).implies (formula_transport h b)
    | .iff a b => (formula_transport h a).iff (formula_transport h b)
    | .xor a b => (formula_transport h a).xor (formula_transport h b)
    | .ite c a b => (formula_transport h c).ite (formula_transport h a) (formula_transport h b)
    | .next a => (formula_transport h a).next
    | .eventually a => (formula_transport h a).eventually
    | .always a => (formula_transport h a).always
    | .strongUntil a b => (formula_transport h a).strongUntil (formula_transport h b)
    | .weakUntil a b => (formula_transport h a).weakUntil (formula_transport h b)
    | .initially a => (formula_transport h a).initially
    | .finally a => (formula_transport h a).«finally»
    | .quant q d a => MeaningTransport.quant (SemanticsBridge.Behavioral.quantifier q)
        (collection_image h d) (formula_transport h a)
    | .letSet d a => MeaningTransport.letSet (collection_image h d) (formula_transport h a)
  termination_by sizeOf e
  decreasing_by
    all_goals simp
    all_goals omega

end

end ObservesCompletion
end ClaferCompiler.Correctness.Behavioral.Full
