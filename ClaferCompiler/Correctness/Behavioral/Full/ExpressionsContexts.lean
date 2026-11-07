module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPreservation
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsTuples

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open IR.Behavioral
namespace LexicalRows
variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {labels : Fin o ↪ Nat}
  {c : Backend.Alloy.Behavioral.Full.Expressions.Context n}
  {ρ : Clafer.Behavioral.Environment (Completion o) n} {e : Environment}

theorem shift (h : LexicalRows b s τ labels c ρ e) (pre : Environment) :
    LexicalRows b s τ labels (c.shift pre.length) ρ (pre ++ e) := by
  refine ⟨⟨shift_term h.context.this_term _, ?_, h.context.this_inside,
    (fun i => shift_term (h.context.lookup_term i) _), ?_, h.context.lookup_inside⟩,
    h.ranges, ?_, ?_⟩
  · intro t
    change Mixed.Unary _ _ ((Backend.Alloy.Behavioral.shift pre.length c.lexical.this).eval _ _ _ _ _)
    rw [shift_eval h.context.this_term]
    exact h.context.this t
  · intro i t
    change Mixed.Unary _ _ ((Backend.Alloy.Behavioral.shift pre.length (c.lexical.lookup i)).eval _ _ _ _ _)
    rw [shift_eval (h.context.lookup_term i)]
    exact h.context.lookup i t
  · intro entry he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    have stable := h.aliases r hr
    refine ⟨shift_term stable.term _, ?_⟩
    intro t u row
    rw [shift_eval stable.term, shift_eval stable.term]
    exact stable.rows t u row
  · intro x hx
    obtain ⟨r, hr, rows⟩ := h.cover x hx
    refine ⟨Backend.Alloy.Behavioral.shift pre.length r,
      List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    intro t
    rw [shift_eval (h.aliases r hr).term]
    exact rows t

theorem push (h : LexicalRows b s τ labels c ρ e) (r : Rel)
    (estimate : Expression.Ranges.CollectionEstimate) (S : Set (Completion o))
    (term : r.Term) (rows : ∀ t, Mixed.Unary (completionAtom labels) S (r.eval s b.width τ e t))
    (inside : S ⊆ observedDomain b.width) (bound : Ranges.CollectionBound completeIntegers estimate S) :
    LexicalRows b s τ labels (c.push r estimate) (ρ.push S) e := by
  refine ⟨⟨h.context.this_term, h.context.this, h.context.this_inside, ?_, ?_, ?_⟩,
    h.ranges.push bound, h.aliases, h.cover⟩
  · intro i
    exact Fin.cases term h.context.lookup_term i
  · intro i t
    refine Fin.cases ?_ (fun j => ?_) i
    · exact rows t
    · exact h.context.lookup j t
  · intro i
    exact Fin.cases inside h.context.lookup_inside i

theorem extend (h : LexicalRows b s τ labels c ρ e)
    (decode : Rel → Completion o) (xs : Vector Rel arity)
    (estimate : Expression.Ranges.CollectionEstimate)
    (terms : ∀ i : Fin arity, (xs[i]).Term)
    (rows : ∀ (i : Fin arity) t, Mixed.Unary (completionAtom labels) {decode xs[i]}
      ((xs[i]).eval s b.width τ e t))
    (inside : ∀ i : Fin arity, decode xs[i] ∈ observedDomain b.width)
    (bound : ∀ i : Fin arity, Ranges.CollectionBound completeIntegers
      (Expression.Ranges.singleton estimate) {decode xs[i]}) :
    LexicalRows b s τ labels (c.extend xs estimate)
      (SemanticsBridge.Behavioral.Grouped.extend ρ arity (Tuples.assignment decode xs)) e := by
  refine ⟨Tuples.context_extend h.context decode xs estimate terms rows inside,
    ⟨h.ranges.this, ?_⟩, h.aliases, h.cover⟩
  intro i
  by_cases hi : i.val < arity
  · have index : arity - (arity - (i.val + 1) + 1) = i.val := by omega
    simpa [Backend.Alloy.Behavioral.Full.Expressions.Context.extend,
      Expression.Ranges.extend, SemanticsBridge.Behavioral.Grouped.extend,
      Tuples.assignment, hi, index] using bound ⟨i.val, hi⟩
  · simpa [Backend.Alloy.Behavioral.Full.Expressions.Context.extend,
      Expression.Ranges.extend, SemanticsBridge.Behavioral.Grouped.extend, hi] using
      h.ranges.lookup (⟨i.val - arity, by omega⟩ : Fin n)

end LexicalRows
end ClaferCompiler.Correctness.Behavioral.Full.Expressions
