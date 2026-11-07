module

public import ClaferCompiler.SemanticsBridge.Behavioral.Expression
public import ClaferCompiler.SemanticsBridge.Behavioral.Binders

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Expression
open IR.Behavioral
open Clafer.Behavioral (Environment Trace)

/-- Independent admissible next choices: the captured domain minus already
bound identities. Captures are observed at entry, not recomputed at later times. -/
def choices (n bound : Nat) (disjoint : Bool) : Observed U (Set U) (n + 1 + bound) :=
  fun ρ _ => some {x | x ∈ ρ.lookup ⟨bound, by omega⟩ ∧
    (disjoint = true → ∀ i : Fin bound, x ∉ ρ.lookup ⟨i.val, by omega⟩)}

def successiveMeaning (n : Nat) (q : Clafer.Behavioral.Quantifier) (disjoint : Bool) :
    (remaining bound : Nat) → Meaning U (n + 1 + (bound + remaining)) → Meaning U (n + 1 + bound) :=
  Nat.rec (fun _ body => body) (fun remaining next bound body =>
    .quant q (choices n bound disjoint) (next (bound + 1) (cast (congrArg (Meaning U)
      (by omega : n + 1 + (bound + (remaining + 1)) = n + 1 + ((bound + 1) + remaining))) body)))

-- [proof->req~compiler-behavioral-elaboration~1]
theorem choices_interpret (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (n bound : Nat) (disjoint : Bool) :
    collection m τ R (.set (IR.Behavioral.Binders.choices k n bound disjoint)) = choices n bound disjoint := by
  funext ρ t
  rw [collection_set]
  apply congrArg some
  ext x
  exact Binders.choices_mem m τ ρ t x disjoint

private theorem interpret_cast (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) {i j : Nat} (h : i = j) (a : Expression.Formula k i) :
    Generic.interpret (fun {_} => atom m τ R) (fun {_} => collection m τ R)
      (cast (congrArg (Expression.Formula k) h) a) =
      cast (congrArg (Meaning U) h)
        (Generic.interpret (fun {_} => atom m τ R) (fun {_} => collection m τ R) a) := by
  cases h
  rfl

theorem successive_interpret (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (n : Nat) (q : Quantifier) (disjoint : Bool)
    (remaining bound : Nat) (body : Expression.Formula k (n + 1 + (bound + remaining))) :
    Generic.interpret (fun {_} => atom m τ R) (fun {_} => collection m τ R)
      (IR.Behavioral.Binders.successiveWith (fun {_} => Expression.Collection.set) n q disjoint remaining bound body) =
    successiveMeaning n (quantifier q) disjoint remaining bound
      (Generic.interpret (fun {_} => atom m τ R) (fun {_} => collection m τ R) body) := by
  induction remaining generalizing bound with
  | zero => rfl
  | succ remaining ih =>
    simp only [IR.Behavioral.Binders.successiveWith, successiveMeaning, Generic.interpret]
    rw [choices_interpret]
    congr 1
    have shift : n + 1 + (bound + (remaining + 1)) = n + 1 + ((bound + 1) + remaining) := by omega
    have hi := ih (bound + 1) (cast (congrArg (Expression.Formula k) shift) body)
    rw [interpret_cast m τ R shift] at hi
    exact hi

/-- Every complete assignment must have a defined body, independently of truth.
This includes assignments which do not satisfy the counted formula. -/
theorem count_defined_iff (τ : Trace (Fin k) U) (q : Grouped.Count) (arity : Nat)
    (disjoint : Bool) (domain : Observed U (Set U) n) (body : Meaning U (n + arity))
    (ρ : Environment U n) (t : Nat) :
    (∃ p, countObservation τ q arity disjoint domain body ρ t = some p) ↔
      ∃ S, domain ρ t = some S ∧ ∀ a ∈ Grouped.assignments arity disjoint S,
        body.Defined τ observation (Grouped.extend ρ arity a) t := by
  classical
  unfold countObservation
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨p, S, hs, hp⟩
    split at hp
    · exact ⟨S, hs, ‹∀ a ∈ Grouped.assignments arity disjoint S, _›⟩
    · cases hp
  · rintro ⟨S, hs, defined⟩
    refine ⟨(Grouped.count q).eval (Grouped.assignments arity disjoint S)
      (fun a => body.raw τ observation.canonical (Grouped.extend ρ arity a) t), S, hs, ?_⟩
    split
    · rfl
    · contradiction

theorem count_value (τ : Trace (Fin k) U) (q : Grouped.Count) (arity : Nat)
    (disjoint : Bool) (domain : Observed U (Set U) n) (body : Meaning U (n + arity))
    (ρ : Environment U n) (t : Nat) (S : Set U) (domainDefined : domain ρ t = some S)
    (defined : ∀ a ∈ Grouped.assignments arity disjoint S,
      body.Defined τ observation (Grouped.extend ρ arity a) t) :
    countObservation τ q arity disjoint domain body ρ t =
      some ((Grouped.count q).eval (Grouped.assignments arity disjoint S)
        (fun a => body.raw τ observation.canonical (Grouped.extend ρ arity a) t)) := by
  simp only [countObservation, domainDefined, Option.bind_some]
  split
  · rfl
  · contradiction

/-- This independent upstream expansion retains one shared domain capture.
`no` negates the whole existential group. Only `one`/`lone` count raw tuples. -/
def binderMeaning (τ : Trace (Fin k) U) (q : Quantifier) (arity : Nat) (disjoint : Bool)
    (domain : Observed U (Set U) n) (body : Meaning U (n + 1 + arity)) : Meaning U n :=
  .letSet domain (match q with
    | .all => successiveMeaning n .all disjoint arity 0 (cast (congrArg (Meaning U) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body)
    | .some => successiveMeaning n .some disjoint arity 0 (cast (congrArg (Meaning U) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body)
    | .no => .not (successiveMeaning n .some disjoint arity 0 (cast (congrArg (Meaning U) (by omega : n + 1 + arity = n + 1 + (0 + arity))) body))
    | .one => .atom (countObservation τ .one arity disjoint (fun ρ _ => some (ρ.lookup 0)) body)
    | .lone => .atom (countObservation τ .lone arity disjoint (fun ρ _ => some (ρ.lookup 0)) body))

-- [proof->req~compiler-behavioral-elaboration~1]
theorem binders_interpret (m : Clafer.Semantics.EffectiveCore k) (τ : Trace (Fin k) U)
    (R : Clafer.Constraints.IntegerRealization U) (q : Quantifier) (arity : Nat) (disjoint : Bool)
    (domain : Expression.Collection k n) (body : Expression.Formula k (n + 1 + arity)) :
    formula m τ R (Expression.binders q arity disjoint domain body) =
      binderMeaning τ q arity disjoint (collection m τ R domain) (formula m τ R body) := by
  cases q
  all_goals simp only [formula_eq_generic, Expression.binders, binderMeaning, Generic.interpret]
  all_goals first
    | rw [successive_interpret]
      rw [interpret_cast m τ R (show n + 1 + arity = n + 1 + (0 + arity) by omega)]
      rfl
    | change Clafer.Behavioral.Formula.letSet _ (.atom (countObservation τ _ _ _ _ (formula m τ R body))) = _
      rw [formula_eq_generic]
      rfl

end ClaferCompiler.SemanticsBridge.Behavioral.Expression
