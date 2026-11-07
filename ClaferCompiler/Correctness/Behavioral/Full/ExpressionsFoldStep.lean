module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFoldDomains
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsOccurrenceValues
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral
namespace FoldStep
variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat} {next : Pass k}

def heads (next : Pass k) (c : Context n) (estimate : Expression.Ranges.CollectionEstimate)
    (op : IR.BehavioralArithmetic.Fold) (body : Expression.Integer k (n + 1))
    (entries : List Rel) : Result (Value Integer) := do
  let values ← entries.mapM fun entry => next.integer (c.push entry (Expression.Ranges.singleton estimate)) body
  return integerFold op values

theorem heads_built (ib : SyntaxBuilt.PassBuilt next) :
    SyntaxBuilt.Success Full.Value.Built (heads next c estimate op body entries) := by
  exact SyntaxBuilt.bind (Q := Full.Value.Built)
    (f := fun values => pure (integerFold op values))
    (SyntaxBuilt.mapM _ entries (fun entry =>
      ib.integer (c.push entry (Expression.Ranges.singleton estimate)) body))
    (fun values hv => SyntaxBuilt.pure (SyntaxBuilt.integerFold op values hv))

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem heads_observation (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.IntegerBound b
      (Expression.Ranges.push c.estimates (Expression.Ranges.singleton estimate)) body range)
    (members : ∀ x ∈ xs, x ∈ S) (inside : S ⊆ observedDomain b.width)
    (bounded : Ranges.CollectionBound completeIntegers estimate S)
    (rows : List.Forall₂ (FoldSelections.HeadRows labels s b.width τ e) entries xs)
    (size : xs.length ≤ estimate.budget)
    (fits : (Expression.Ranges.foldRange op estimate.budget range).fits b.width = true)
    (success : heads next c estimate op body entries = .ok result) :
    IntegerObservation s b.width τ e t
      (IntegerFold.sourceValue op (xs.map fun x =>
        SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers body (ρ.push {x}) t)) result := by
  cases run : entries.mapM (fun entry => next.integer (c.push entry (Expression.Ranges.singleton estimate)) body) with
  | error err => simp [heads, run, bind, Except.bind] at success
  | ok values =>
    have eq : integerFold op values = result := by
      simpa [heads, run, bind, Except.bind, pure, Except.pure] using success
    subst result
    have paired := mapM_ok _ _ _ run
    have observations : List.Forall₂ (IntegerObservation s b.width τ e t)
        (xs.map fun x => SemanticsBridge.Behavioral.Expression.integer
          (Sets.model v) σ completeIntegers body (ρ.push {x}) t) values := by
      clear success run size
      induction rows generalizing values with
      | nil => cases paired; exact .nil
      | @cons entry x entries xs row rest rec =>
        cases paired with
        | cons compiled tail =>
          have capture := hc.push entry _ {x} row.1 row.2
            (by intro y hy; exact (Set.mem_singleton_iff.mp hy).symm ▸ inside (members x (by simp)))
            (bounded.singleton_member (members x (by simp)))
          exact .cons (ih.integer capture t body _ _ bound compiled)
            (rec (fun y hy => members y (by simp [hy])) _ tail)
    apply IntegerFold.observation op observations range estimate.budget (by simpa using size) ?_ fits
    intro source member z value
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp member
    exact Ranges.integer_bound hm.ranges
      (hc.ranges.push (bounded.singleton_member (members x hx))) bound value

theorem sameSource_map (a : Value α) (f : α → Result (Value Integer))
    (ha : Full.Value.Built a)
    (bodies : ∀ x result, f x = .ok result → Full.Value.Built result)
    (observations : ∀ x result, Full.Value.Meaning s w τ e t a x →
      f x = .ok result → IntegerObservation s w τ e t source result)
    (inhabited : ∃ x, Full.Value.Meaning s w τ e t a x)
    (success : valueMapM a f = .ok result) :
    IntegerObservation s w τ e t source result := by
  refine ⟨SyntaxBuilt.valueMapM a f ha bodies _ success, ?_, ?_⟩
  · intro term ht
    obtain ⟨x, value, hx, compiled, meaning⟩ := (valueMapM_meaning a f ha bodies success).mp ht
    exact (observations x value hx compiled).sound term meaning
  · intro z hz
    obtain ⟨x, hx⟩ := inhabited
    obtain ⟨guard, member, holds⟩ := hx
    obtain ⟨value, compiled⟩ := (valueMapM_expansion a f success).2 guard x member
    obtain ⟨term, meaning⟩ := (observations x value ⟨guard, member, holds⟩ compiled).complete z hz
    exact ⟨term, (valueMapM_meaning a f ha bodies success).mpr ⟨x, value, ⟨guard, member, holds⟩, compiled, meaning⟩⟩

theorem enumeration_members {sets : List (Set α)} {lists : List (List α)}
    (represented : List.Forall₂ (fun S xs => xs.Nodup ∧ ∀ x, x ∈ xs ↔ x ∈ S) sets lists) :
    ∀ x ∈ lists.flatten, x ∈ Ranges.unionSets sets := by
  induction represented with
  | nil => simp
  | @cons S xs sets lists head rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨S, by simp, (head.2 x).mp hx⟩
    · obtain ⟨T, ht, hx⟩ := ih x hx
      exact ⟨T, by simp [ht], hx⟩

def relations (next : Pass k) (c : Context n) (estimates : List Expression.Ranges.CollectionEstimate)
    (op : IR.BehavioralArithmetic.Fold) (body : Expression.Integer k (n + 1))
    (rs : List Rel) : Result (Value Integer) :=
  valueMapM (FoldSelections.choices c.lexical.aliases (rs.zip estimates))
    (heads next c (Expression.Ranges.family estimates) op body)

theorem relations_built (ib : SyntaxBuilt.PassBuilt next) :
    SyntaxBuilt.Success Full.Value.Built (relations next c estimates op body rs) :=
  SyntaxBuilt.valueMapM _ _ (FoldSelections.choices_built _ _ (Full.Value.pure_built _))
    (fun _ => heads_built ib)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem relations_observation (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (ib : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.IntegerBound b
      (Expression.Ranges.push c.estimates (Expression.Ranges.singleton (Expression.Ranges.family estimates))) body range)
    (rows : List.Forall₂ (FoldSelections.DomainRows labels s b.width τ e t) (rs.zip estimates) sets)
    (inside : Ranges.unionSets sets ⊆ observedDomain b.width)
    (bounded : List.Forall₂ (Ranges.CollectionBound completeIntegers) estimates sets)
    (fits : (Expression.Ranges.foldRange op (Expression.Ranges.family estimates).budget range).fits b.width = true)
    (success : relations next c estimates op body rs = .ok result) :
    IntegerObservation s b.width τ e t
      ((SemanticsBridge.BehavioralArithmetic.fold op).eval
        (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
        (fun ix => SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers body (ρ.push {ix.2}) t)) result := by
  apply sameSource_map _ _ (FoldSelections.choices_built _ _ (Full.Value.pure_built _))
    (fun _ => heads_built ib) ?_ (FoldSelections.choices_complete hc rows) success
  intro entries result selected compiled
  obtain ⟨lists, represented, singles⟩ := FoldSelections.choices_sources hc rows selected
  rw [Occurrences.fold_occurrences_sourceValue represented op
    (fun x => SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers body (ρ.push {x}) t)]
  exact heads_observation hm ih hc bound (enumeration_members represented) inside
    (Ranges.family_bound bounded) singles (Occurrences.flatten_length_bound represented bounded) fits compiled

theorem collections_map
    (a : Value (List Rel)) (f : List Rel → Result (Value Integer))
    (ha : CollectionsObservation s w τ e t atom source a)
    (bodies : ∀ rs result, f rs = .ok result → Full.Value.Built result)
    (observe : ∀ rs sets result, source = some sets →
      List.Forall₂ (fun r S => r.Term ∧ Mixed.Unary atom S (r.eval s w τ e t)) rs sets →
      f rs = .ok result → IntegerObservation s w τ e t (g sets) result)
    (success : valueMapM a f = .ok result) :
    IntegerObservation s w τ e t (source.bind g) result := by
  refine ⟨SyntaxBuilt.valueMapM a f ha.built bodies _ success, ?_, ?_⟩
  · intro term ht
    obtain ⟨rs, value, hr, compiled, meaning⟩ := (valueMapM_meaning a f ha.built bodies success).mp ht
    obtain ⟨sets, sourceEq, rows⟩ := ha.sound rs hr
    obtain ⟨z, hz, termBuilt, eval⟩ := (observe rs sets value sourceEq rows compiled).sound term meaning
    exact ⟨z, by simp [sourceEq, hz], termBuilt, eval⟩
  · intro z hz
    obtain ⟨sets, sourceEq, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain ⟨rs, hr⟩ := ha.complete sets sourceEq
    have rows := (ha.sound rs hr)
    obtain ⟨actual, actualEq, rows⟩ := rows
    have eq := Option.some.inj (actualEq.symm.trans sourceEq)
    subst actual
    obtain ⟨guard, member, holds⟩ := hr
    obtain ⟨value, compiled⟩ := (valueMapM_expansion a f success).2 guard rs member
    obtain ⟨term, meaning⟩ := (observe rs sets value sourceEq rows compiled).complete z hz
    exact ⟨term, (valueMapM_meaning a f ha.built bodies success).mpr
      ⟨rs, value, ⟨guard, member, holds⟩, compiled, meaning⟩⟩

end FoldStep
variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat} {next : Pass k} {fuel : Nat}

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The actual aggregate branch preserves indexed source occurrences, all
original body domains, and the checked range of every integer prefix. -/
theorem foldStep (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (ib : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.IntegerBound b c.estimates (.fold op ds body) range)
    (success : (lowerStep v b fuel next).integer c (.fold op ds body) = .ok result) :
    IntegerObservation s b.width τ e t
      (SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers (.fold op ds body) ρ t) result := by
  cases bound with
  | fold domains bodyBound fits =>
    rename_i estimates bodyRange
    cases analyzed : (Expression.Ranges.analyzeAt b fuel).collections ds c.estimates with
    | error err => simp [lowerStep, analyzed, bind, Except.bind] at success
    | ok certificate =>
      have same := Expression.Ranges.collections_unique domains certificate.property
      have bodyBound : Expression.Ranges.IntegerBound b
          (Expression.Ranges.push c.estimates (Expression.Ranges.singleton (Expression.Ranges.family certificate.val))) body bodyRange :=
        same ▸ bodyBound
      have fits : (Expression.Ranges.foldRange op (Expression.Ranges.family certificate.val).budget bodyRange).fits b.width = true :=
        same ▸ fits
      cases compiled : next.collections c ds with
      | error err => simp [lowerStep, analyzed, compiled, bind, Except.bind] at success
      | ok domainsValue =>
        have run : valueMapM domainsValue (FoldStep.relations next c certificate.val op body) = .ok result := by
          unfold FoldStep.relations FoldStep.heads FoldSelections.choices FoldSelections.selected
          simpa [lowerStep, analyzed, compiled, bind, Except.bind, pure, Except.pure] using success
        change IntegerObservation s b.width τ e t
          ((SemanticsBridge.Behavioral.Expression.collections (Sets.model v) σ completeIntegers ds ρ t).bind fun sets =>
            (SemanticsBridge.BehavioralArithmetic.fold op).eval (Clafer.Behavioral.PrimitiveExpression.occurrences sets)
              (fun ix => SemanticsBridge.Behavioral.Expression.integer (Sets.model v) σ completeIntegers body (ρ.push {ix.2}) t)) result
        apply FoldStep.collections_map _ _ (ih.collections hc t ds domainsValue _ certificate.property compiled)
          (fun _ => FoldStep.relations_built ib) ?_ run
        intro relations sets value source rows branch
        have domainRows := FoldSelections.domains hm hc certificate.property source rows
        exact FoldStep.relations_observation hm ih ib hc bodyBound domainRows
          (FoldSelections.domains_inside domainRows)
          (Ranges.collections_bound hm.ranges hc.ranges certificate.property source) fits branch

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
