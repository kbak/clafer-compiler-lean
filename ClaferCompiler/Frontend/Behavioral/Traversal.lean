module

public import ClaferCompiler.Frontend.Behavioral.ConditionalRules

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Traversal
open ValueRules

/-- Position-preserving list relation using the standard length/zip interface.
The native import contract excludes Batteries, which supplies `List.Forall₂`;
this predicate needs no new inductive traversal or runtime dependency. -/
def Related (R : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  xs.length = ys.length ∧ ∀ a b, (a, b) ∈ xs.zip ys → R a b

theorem Related.nil : Related R [] [] := by simp [Related]

theorem Related.cons (head : R a b) (tail : Related R xs ys) : Related R (a :: xs) (b :: ys) := by
  refine ⟨by simp [tail.1], ?_⟩
  intro x y member
  simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | member
  · exact head
  · exact tail.2 x y member

theorem Related.of_cons (h : Related R (a :: xs) (b :: ys)) : R a b ∧ Related R xs ys := by
  refine ⟨h.2 a b (by simp), by simpa using h.1, ?_⟩
  intro x y member
  exact h.2 x y (by simp [member])

/-- These lemmas retain per-element derivations while reusing the standard
monadic traversals. Failure does not return a truncated list or an absent value. -/
theorem map_success {f : α → β} {x : Except ε α} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp_all [Except.map]

theorem list_relation {R : α → β → Prop} {f : α → Except ε β}
    (sound : ∀ a b, f a = .ok b → R a b) {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) : Related R xs ys := by
  induction xs generalizing ys with
  | nil => cases Except.ok.inj h; exact Related.nil
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_success] at h
    obtain ⟨y, hy, rest, hr, he⟩ := h
    cases Except.ok.inj he
    exact Related.cons (sound x y hy) (ih hr)

theorem option_relation {R : α → β → Prop} {f : α → Except ε β}
    (sound : ∀ a b, f a = .ok b → R a b) {x y} (h : x.mapM f = .ok y) : Option.Rel R x y := by
  cases x with
  | none => cases Except.ok.inj h; exact .none
  | some a =>
    change (f a).map some = .ok y at h
    obtain ⟨b, hb, rfl⟩ := map_success h
    exact .some (sound a b hb)

/-- Proof data is erased; execution remains the standard `List.mapM`. -/
def list {R : α → β → Prop} (f : (a : α) → Except ε {b // R a b}) (xs : List α) :
    Except ε {ys // Related R xs ys} := do
  let result ← MonadAttach.attach (xs.mapM fun a => (f a).map Subtype.val)
  return ⟨result.val, list_relation (fun a b h => by
    obtain ⟨b, _, rfl⟩ := map_success h
    exact b.property) result.property⟩

def option {R : α → β → Prop} (f : (a : α) → Except ε {b // R a b}) (x : Option α) :
    Except ε {y // Option.Rel R x y} := do
  let result ← MonadAttach.attach (x.mapM fun a => (f a).map Subtype.val)
  return ⟨result.val, option_relation (fun a b h => by
    obtain ⟨b, _, rfl⟩ := map_success h
    exact b.property) result.property⟩

end ClaferCompiler.Frontend.Behavioral.Traversal
