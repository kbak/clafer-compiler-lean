module

public import ClaferCompiler.Frontend.Constraints
public import ClaferCompiler.SemanticsBridge.Expr

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Constraints
open Frontend Frontend.Constraints IR.Expr

/-- Declarative source denotation uses the independent inference rules and the
pinned partial typed meaning. Neither the executable elaborator nor target
satisfaction occurs in this definition. Undefined is retained as `none`. -/
def Meaning (c : IR.Structural.Core n) (s : Support n m) (e : Frontend.Expr)
    {U : Type} (model : Clafer.Constraints.IntegerBinding (Expr.support s) U)
    (env : Clafer.Constraints.Environment (Expr.support s) U [])
    (v : Option (Clafer.Constraints.Value (s := Expr.support s) U .boolean)) : Prop :=
  ∃ (raw : Syntax n m) (typed : raw.Typed s [] .boolean),
    Elaborates c s [] none true e .boolean raw ∧
    (Expr.interpret s raw typed).denote model env = v

/-- Success establishes source correspondence, typing and finite-observation
admission, without a source-satisfaction or numeric-definedness premise. -/
theorem body_sound (body : Body c s e) :
    Elaborates c s [] none true e .boolean body.checked.term.raw ∧
    body.checked.term.Typed s [] .boolean ∧ body.checked.term.Observed s :=
  ⟨body.derivation, body.checked.typed, body.checked.observed⟩

theorem denote_sound (body : Body c s e) {U : Type}
    (model : Clafer.Constraints.IntegerBinding (Expr.support s) U)
    (env : Clafer.Constraints.Environment (Expr.support s) U []) :
    Meaning c s e model env (Expr.denote body.checked model env) :=
  ⟨body.checked.term.raw, body.checked.typed, body.derivation, rfl⟩

theorem success (doc : Document) (c : IR.Structural.Core n) (s : Support n m)
    (e : Frontend.Expr) (body : Body c s e) (_h : elaborateBody doc c s e = .ok body) :
    Elaborates c s [] none true e .boolean body.checked.term.raw ∧
    body.checked.term.Typed s [] .boolean ∧ body.checked.term.Observed s := body_sound body

theorem attached_owner (doc : Document) (c : Resolution.Candidate n) (o : Occurrence doc c) (a : Attached doc c o) : a.layout.support.context = o.owner := a.layout.context

theorem attached_maps (doc : Document) (c : Resolution.Candidate n) (o : Occurrence doc c) (a : Attached doc c o) (i : Fin a.layout.count) :
    MapResolved c.core a.layout.support.maps[i] := a.layout.resolved.2.2 i

/-- Every original body position is enumerated, including repeated names and
multiple constraints on the same declaration. -/
theorem occurrence_coverage (doc : Document) (c : Resolution.Candidate n)
    (o : Occurrence doc c) : o ∈ occurrences doc c := by
  cases o with
  | mk owner group position =>
    simp only [occurrences, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨owner, group, position, rfl⟩

/-- Standard-library traversal retains the tag of each dependent result. -/
theorem mapM_tags {α : Type} {β : α → Type} {ε : Type}
    (f : (a : α) → Except ε (β a)) (xs : List α) (out : List ((a : α) × β a))
    (h : xs.mapM (fun a => do return (⟨a, ← f a⟩ : Sigma β)) = .ok out) : out.map Sigma.fst = xs := by
  induction xs generalizing out with
  | nil => simp only [List.mapM_nil, pure] at h; cases h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | error err =>
      simp only [hx, bind, Except.bind] at h
      cases h
    | ok value =>
      simp only [hx, bind, pure, Except.bind, Except.pure] at h
      cases ht : xs.mapM (fun a => do return (⟨a, ← f a⟩ : Sigma β)) with
      | error err =>
        simp only [bind, pure, Except.bind, Except.pure] at ht
        rw [ht] at h
        cases h
      | ok tail =>
        have hi := ih tail ht
        simp only [bind, pure, Except.bind, Except.pure] at ht
        rw [ht] at h
        cases h
        simp [hi]

theorem attachments_preserved (doc : Document) (e : Resolution.Elaborated doc) (out)
    (h : elaborate doc e = .ok out) : out.map Sigma.fst = occurrences doc e.candidate :=
  mapM_tags (elaborateOccurrence doc e.candidate) _ _ h

/-- Boolean coercion cannot silently dereference before counting heads. -/
theorem boolean_coercion (h : Coerces s t a .boolean b) :
    (t = .boolean ∧ b = a) ∨
      ∃ k, t = .collection k ∧ b = .less (.integer 0) (.cardinality k a) := by
  cases h with
  | same => exact Or.inl ⟨rfl, rfl⟩
  | some => exact Or.inr ⟨_, rfl, rfl⟩
  | trans _ _ h => exact (h rfl).elim

/-- Presence is strict finite cardinality, using the existing independent
constructor theorem; it is not a short-circuit truth test. -/
theorem implicit_some {s : Support n m} {Γ : List (Local n)} {k : Collection n}
    (a : Syntax n m) (ha : a.Typed s Γ (.collection k)) {U : Type}
    (model : Clafer.Constraints.IntegerBinding (Expr.support s) U)
    (env : Clafer.Constraints.Environment (Expr.support s) U (Γ.map (Expr.binder s)))
    (S : Set ((Expr.collection s k).Carrier U))
    (hv : (Expr.interpret s a ha).denote model env = some S) (hf : S.Finite) :
    (Expr.interpret s (.less (.integer 0) (.cardinality k a))
      (show Syntax.Typed s Γ .boolean _ from ⟨rfl, rfl, rfl, ha⟩)).denote model env =
      some ⟨S.Nonempty⟩ :=
  Clafer.Constraints.denotes_some model env (Expr.interpret s a ha) S hv hf

end ClaferCompiler.SemanticsBridge.Constraints
