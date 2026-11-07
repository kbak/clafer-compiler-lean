module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsObservations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal

/-- Partial collection observations are represented by guarded relational
values. Soundness records rows and syntax only; completeness records the
original source option domain. This is an induction interface, not a premise
of the concrete compiler theorem. -/
structure CollectionObservation (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (t : Nat) (f : U → Atom) (source : Option (Set U))
    (target : Backend.Alloy.Behavioral.Full.Value Rel) : Prop where
  built : Value.Built target
  sound : ∀ r, Value.Meaning s w τ e t target r →
    ∃ S, source = some S ∧ r.Term ∧ Mixed.Unary f S (r.eval s w τ e t)
  complete : ∀ S, source = some S → ∃ r, Value.Meaning s w τ e t target r

namespace CollectionObservation
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {f : U → Atom} {source left right : Option (Set U)}
  {a b : Backend.Alloy.Behavioral.Full.Value Rel} {r : Rel} {S : Set U}

theorem pure (term : r.Term) (rows : Mixed.Unary f S (r.eval s w τ e t)) :
    CollectionObservation s w τ e t f (some S) (.pure r) := by
  refine ⟨Value.pure_built r, ?_, ?_⟩
  · intro other h
    have same := Value.pure_meaning r other |>.mp h
    subst other
    exact ⟨S, rfl, term, rows⟩
  · intro _ _
    exact ⟨r, (Value.pure_meaning r r).mpr rfl⟩

theorem defined (h : CollectionObservation s w τ e t f source a) :
    a.defined.Holds s w τ e t ↔ source.isSome = true := by
  rw [Value.defined_meaning a h.built]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨S, hs, _, _⟩ := h.sound r hr
    simp [hs]
  · intro hs
    obtain ⟨S, hs⟩ := Option.isSome_iff_exists.mp hs
    exact h.complete S hs

theorem lift₂ (ha : CollectionObservation s w τ e t f left a)
    (hb : CollectionObservation s w τ e t f right b)
    (sourceOp : Set U → Set U → Set U) (targetOp : Rel → Rel → Rel)
    (term : ∀ x y, x.Term → y.Term → (targetOp x y).Term)
    (rows : ∀ S T x y, x.Term → y.Term →
      Mixed.Unary f S (x.eval s w τ e t) → Mixed.Unary f T (y.eval s w τ e t) →
      Mixed.Unary f (sourceOp S T) ((targetOp x y).eval s w τ e t)) :
    CollectionObservation s w τ e t f (Clafer.Constraints.lift₂ sourceOp left right)
      ((a.pair b).map (fun pair => targetOp pair.1 pair.2)) := by
  refine ⟨Value.map_built _ _ (Value.pair_built a b ha.built hb.built), ?_, ?_⟩
  · intro result meaning
    obtain ⟨⟨x, y⟩, pair, rfl⟩ := (Value.map_meaning _ _).mp meaning
    obtain ⟨hx, hy⟩ := (Value.pair_meaning a b ha.built hb.built).mp pair
    obtain ⟨S, hs, hxt, hxr⟩ := ha.sound x hx
    obtain ⟨T, ht, hyt, hyr⟩ := hb.sound y hy
    exact ⟨sourceOp S T, by simp [Clafer.Constraints.lift₂, hs, ht],
      term x y hxt hyt, rows S T x y hxt hyt hxr hyr⟩
  · intro S defined
    cases hl : left with
    | none => simp [Clafer.Constraints.lift₂, hl] at defined
    | some L =>
      cases hr : right with
      | none => simp [Clafer.Constraints.lift₂, hr] at defined
      | some R =>
        obtain ⟨x, hx⟩ := ha.complete L hl
        obtain ⟨y, hy⟩ := hb.complete R hr
        refine ⟨targetOp x y, (Value.map_meaning _ _).mpr ?_⟩
        exact ⟨(x, y), (Value.pair_meaning a b ha.built hb.built).mpr ⟨hx, hy⟩, rfl⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem union (ha : CollectionObservation s w τ e t f left a)
    (hb : CollectionObservation s w τ e t f right b) :
    CollectionObservation s w τ e t f (Clafer.Constraints.lift₂ (· ∪ ·) left right)
      (Backend.Alloy.Behavioral.Full.collectionUnion a b) :=
  lift₂ ha hb _ _ (fun _ _ hx hy => .union hx hy)
    (fun _ _ _ _ hx hy hs ht => Mixed.unary_union hx hy hs ht)

theorem inter (hf : Function.Injective f)
    (ha : CollectionObservation s w τ e t f left a)
    (hb : CollectionObservation s w τ e t f right b) :
    CollectionObservation s w τ e t f (Clafer.Constraints.lift₂ (· ∩ ·) left right)
      (Backend.Alloy.Behavioral.Full.collectionInter a b) :=
  lift₂ ha hb _ _ (fun _ _ hx hy => .inter hx hy)
    (fun _ _ _ _ hx hy hs ht => Mixed.unary_inter hf hx hy hs ht)

theorem diff (hf : Function.Injective f)
    (ha : CollectionObservation s w τ e t f left a)
    (hb : CollectionObservation s w τ e t f right b) :
    CollectionObservation s w τ e t f (Clafer.Constraints.lift₂ (· \ ·) left right)
      (Backend.Alloy.Behavioral.Full.collectionDiff a b) :=
  lift₂ ha hb _ _ (fun _ _ hx hy => .diff hx hy)
    (fun _ _ _ _ hx hy hs ht => Mixed.unary_diff hf hx hy hs ht)

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem map (ha : CollectionObservation s w τ e t f source a)
    (sourceOp : Set U → Set U) (targetOp : Rel → Rel)
    (term : ∀ x, x.Term → (targetOp x).Term)
    (rows : ∀ S x, source = some S → x.Term →
      Mixed.Unary f S (x.eval s w τ e t) →
      Mixed.Unary f (sourceOp S) ((targetOp x).eval s w τ e t)) :
    CollectionObservation s w τ e t f (source.map sourceOp) (a.map targetOp) := by
  refine ⟨Value.map_built _ _ ha.built, ?_, ?_⟩
  · intro result meaning
    obtain ⟨x, hx, rfl⟩ := (Value.map_meaning _ _).mp meaning
    obtain ⟨S, hs, ht, hr⟩ := ha.sound x hx
    exact ⟨sourceOp S, by simp [hs], term x ht, rows S x hs ht hr⟩
  · intro S hs
    obtain ⟨T, ht, _⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨x, hx⟩ := ha.complete T ht
    exact ⟨_, (Value.map_meaning _ _).mpr ⟨x, hx, rfl⟩⟩

theorem literal (labels : Fin o ↪ Nat) (z : Int) (fits : Backend.Alloy.fitsInt w z = true) :
    CollectionObservation s w τ e t (completionAtom labels) (some {Sum.inr z})
      (.pure (.integer z)) :=
  pure (.integer z) (by
    simpa [Rel.eval, Rel.integer, Rel.fold, RelAlgebra.step, relationAlgebra, fits] using
      Mixed.unary_singleton (f := completionAtom labels) (Sum.inr z))

end CollectionObservation
end ClaferCompiler.Correctness.Behavioral.Full
