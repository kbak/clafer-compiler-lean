module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsFormulaMap
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsTuples
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsIntegers
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersExtraction
public import ClaferCompiler.Correctness.Behavioral.Full.IntegersValues
public import ClaferCompiler.Correctness.Behavioral.Partial

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

namespace SyntaxBuilt

def Success (P : α → Prop) (a : Expressions.Result α) : Prop :=
  ∀ result, a = .ok result → P result

theorem pure (h : P x) : Success P (pure x) := by
  intro result eq
  cases eq
  exact h

theorem bind {a : Expressions.Result α} {f : α → Expressions.Result β}
    (ha : Success P a) (hf : ∀ x, P x → Success Q (f x)) : Success Q (a >>= f) := by
  cases he : a with
  | error err => intro result eq; cases eq
  | ok x => exact hf x (ha x he)

theorem bind_any {a : Expressions.Result α} {f : α → Expressions.Result β}
    (hf : ∀ x, Success Q (f x)) : Success Q (a >>= f) :=
  bind (P := fun _ => True) (fun _ _ => trivial) (fun x _ => hf x)

theorem predicate (a : Backend.Alloy.Behavioral.Full.Value α) (p : α → Formula)
    (ha : Value.Built a) (hp : ∀ x, (p x).Built) : Partial.Built (a.predicate p) :=
  Partial.atom_built (Value.use_built a _ ha (fun _ => .truth)) (Value.use_built a p ha hp)

theorem extreme (op : IR.Behavioral.Primitive.Extreme) (r : IR.Expr.Interval)
    (a : Backend.Alloy.Behavioral.Full.Value Rel) (ha : Value.Built a) :
    Value.Built (collectionExtreme op r a) := by
  apply Value.bind_built _ _ ha
  intro value g result member
  simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨z, _, eq, _⟩
  · exact .equal _ _
  · rw [← eq]
    exact .binary .conj (.subset _ _) (.binary .conj (.subset _ _) (.equal _ _))

theorem integerBinary (op : IR.BehavioralArithmetic.Binary)
    (a b : Backend.Alloy.Behavioral.Full.Value Integer) (ha : Value.Built a) (hb : Value.Built b) :
    Value.Built (Backend.Alloy.Behavioral.Full.integerBinary op a b) :=
  Value.map_built _ _ (Value.pair_built _ _ ha hb)

theorem integerFold (op : IR.BehavioralArithmetic.Fold)
    (values : List (Backend.Alloy.Behavioral.Full.Value Integer))
    (hv : ∀ a ∈ values, Value.Built a) : Value.Built (Backend.Alloy.Behavioral.Full.integerFold op values) := by
  have fold (initial : Backend.Alloy.Behavioral.Full.Value Integer) (hi : Value.Built initial) :
      Value.Built (values.foldl (fun r a => Backend.Alloy.Behavioral.Full.integerBinary
        (if op == .sum then .add else .multiply) r a) initial) := by
    induction values generalizing initial with
    | nil => exact hi
    | cons a values ih =>
      exact ih (fun v h => hv v (List.mem_cons_of_mem _ h)) _
        (integerBinary _ _ _ hi (hv a List.mem_cons_self))
  exact fold _ (Value.pure_built _)

theorem all (ps : List Formula) (h : ∀ p ∈ ps, p.Built) : (Expressions.all ps).Built := by
  induction ps with
  | nil => exact .truth
  | cons p ps ih =>
    exact .binary .conj (h p List.mem_cons_self)
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem countTruth (q : IR.Behavioral.Grouped.Count) (ps : List Formula)
    (h : ∀ p ∈ ps, p.Built) : (Expressions.countTruth q ps).Built := by
  have fold (initial : Formula × Formula) (hi : initial.1.Built ∧ initial.2.Built) :
      (ps.foldl countStep initial).1.Built ∧ (ps.foldl countStep initial).2.Built := by
    induction ps generalizing initial with
    | nil => exact hi
    | cons p ps ih =>
      have hp := h p List.mem_cons_self
      exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) _
        ⟨.binary .conj hi.1 (.unary .neg hp),
          .binary .disj (.binary .conj hi.2 (.unary .neg hp)) (.binary .conj hi.1 hp)⟩
  have h := fold (.truth, .falsity) ⟨.truth, .falsity⟩
  cases q with
  | one => exact h.2
  | lone => exact .binary .disj h.1 h.2

/-- Every generated guard is a well-formed postfix formula, even in a branch
whose guard is false or whose corresponding source observation is undefined. -/
structure PassBuilt (next : Expressions.Pass k) : Prop where
  collection : ∀ {n} (c : Expressions.Context n) a, Success Value.Built (next.collection c a)
  integer : ∀ {n} (c : Expressions.Context n) a, Success Value.Built (next.integer c a)
  collections : ∀ {n} (c : Expressions.Context n) a, Success Value.Built (next.collections c a)
  predicate : ∀ {n} (c : Expressions.Context n) a, Success Partial.Built (next.predicate c a)
  atom : ∀ {n} (c : Expressions.Context n) a, Success Partial.Built (next.atom c a)
  formula : ∀ {n} (c : Expressions.Context n) a, Success Partial.Built (next.formula c a)

theorem mapM {α β : Type} {P : β → Prop} (f : α → Expressions.Result β) (xs : List α)
    (hf : ∀ x, Success P (f x)) : Success (fun ys => ∀ y ∈ ys, P y) (xs.mapM f) := by
  intro ys success
  have paired := Expressions.mapM_ok f xs ys success
  clear success
  induction paired with
  | nil => simp
  | @cons x y xs ys hxy paired ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hf x _ hxy
    · exact ih z hz

theorem valueMapM {α β : Type} (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Expressions.Result (Backend.Alloy.Behavioral.Full.Value β))
    (ha : Value.Built a) (hf : ∀ x, Success Value.Built (f x)) :
    Success Value.Built (Expressions.valueMapM a f) := by
  rcases a with ⟨inputs⟩
  intro result success
  unfold Expressions.valueMapM at success
  cases hm : inputs.mapM (fun input =>
      (fun output : Backend.Alloy.Behavioral.Full.Value β => output.cases.map
        (fun pair => (Formula.binary .conj input.1 pair.1, pair.2))) <$> f input.2) with
  | error error => simp [hm] at success
  | ok choices =>
    have eq : result = ⟨choices.flatten⟩ := by simpa [hm] using success.symm
    subst result
    have paired := Expressions.mapM_ok _ _ _ hm
    clear success hm
    have all : ∀ g x, (g, x) ∈ choices.flatten → g.Built := by
      induction paired with
      | nil => simp
      | @cons input output inputs outputs hxy paired ih =>
        cases ho : f input.2 with
        | error error => simp [ho] at hxy
        | ok value =>
          have eq : value.cases.map (fun (h, y) => (Formula.binary .conj input.1 h, y)) = output := by
            simpa [ho] using hxy
          subst output
          intro g x member
          simp only [List.flatten_cons, List.mem_append] at member
          rcases member with member | member
          · obtain ⟨⟨h, y⟩, hy, eq⟩ := List.mem_map.mp member
            cases eq
            exact .binary .conj (ha _ _ List.mem_cons_self) (hf input.2 value ho h _ hy)
          · exact ih (fun g x hx => ha g x (List.mem_cons_of_mem _ hx)) g x member
    exact all

theorem selectionChecked (aliases : List Rel) (domain : Rel) (budget : Nat) :
    Value.Built ((Value.selections aliases domain budget).bind fun heads =>
      ⟨[(Formula.equal domain (Backend.Alloy.Behavioral.Full.union heads), heads)]⟩) := by
  apply Value.bind_built _ _ (Value.selections_built aliases domain budget)
  intro heads g x member
  have eq : g = Formula.equal domain (union heads) := congrArg Prod.fst (List.mem_singleton.mp member)
  rw [eq]
  exact .equal _ _

theorem occurrenceChoices (aliases : List Rel)
    (domains : List (Rel × IR.Behavioral.Expression.Ranges.CollectionEstimate))
    (initial : Backend.Alloy.Behavioral.Full.Value (List Rel)) (hi : Value.Built initial) :
    Value.Built (domains.foldl (fun choices (relation, estimate) =>
      (choices.pair ((Value.selections aliases relation estimate.budget).bind fun heads =>
        ⟨[(Formula.equal relation (Backend.Alloy.Behavioral.Full.union heads), heads)]⟩)).map
          (fun (before, now) => before ++ now)) initial) := by
  induction domains generalizing initial with
  | nil => exact hi
  | cons pair domains ih =>
    exact ih _ (Value.map_built _ _ (Value.pair_built _ _ hi (selectionChecked aliases pair.1 pair.2.budget)))

theorem partialMapM (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Expressions.Result Backend.Alloy.Behavioral.Partial.Translation)
    (ha : Value.Built a) (hf : ∀ x, Success Partial.Built (f x)) :
    Success Partial.Built (Expressions.partialMapM a f) :=
  fun result success => Expressions.partialMapM_built a f result ha
    (fun _ x body _ hb => hf x body hb) success

theorem quantify (q : IR.Behavioral.Quantifier) (domain : Rel)
    (one two : Backend.Alloy.Behavioral.Partial.Translation)
    (h₁ : Partial.Built one) (h₂ : Partial.Built two) :
    Partial.Built (Backend.Alloy.Behavioral.Partial.quantify q domain .truth one two) := by
  have defined : (Formula.binary .conj .truth (.all domain one.defined)).Built :=
    .binary .conj .truth (.all _ h₁.defined)
  cases q with
  | all => exact ⟨⟨.all _ h₁.truth.raw, .all _ h₁.truth.positive, .exists_ _ h₁.truth.negative⟩, defined⟩
  | some => exact ⟨⟨.exists_ _ h₁.truth.raw, .exists_ _ h₁.truth.positive, .all _ h₁.truth.negative⟩, defined⟩
  | no => exact ⟨⟨.all _ (.unary .neg h₁.truth.raw), .all _ h₁.truth.negative, .exists_ _ h₁.truth.positive⟩, defined⟩
  | one => exact ⟨Encoding.atomic_built (.exists_ _ (.binary .conj h₁.truth.raw
      (.all _ (.binary .implies h₂.truth.raw (.equal _ _))))), defined⟩
  | lone => exact ⟨Encoding.atomic_built (.all _ (.binary .implies h₁.truth.raw
      (.all _ (.binary .implies h₂.truth.raw (.equal _ _))))), defined⟩

variable {next : Expressions.Pass k} (ih : PassBuilt next)
  (v : IR.BehavioralStructural.Validated k) (b : IR.Behavioral.Expression.Ranges.Inputs k) (fuel : Nat)
include ih

theorem lowerStep_collection (c : Expressions.Context n) (a : IR.Behavioral.Expression.Collection k n) :
    Success Value.Built ((Expressions.lowerStep v b fuel next).collection c a) := by
  cases a with
  | set a => exact bind_any (fun r => pure (Value.pure_built r))
  | literal z => exact pure (Value.pure_built _)
  | integer a =>
    exact bind_any (fun range => bind (ih.integer c a) (fun value built =>
      pure (Value.bind_built _ _ built (CollectionObservation.conversionBody_built range))))
  | extreme op a =>
    exact bind_any (fun range => bind (ih.collection c a) (fun value built => pure (extreme op range.values value built)))
  | union a d | inter a d | diff a d =>
    exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (Value.map_built _ _ (Value.pair_built left right hl hr))))
  | step st a =>
    exact bind_any (fun _ => bind (ih.collection c a) (fun value built => pure (Value.map_built value _ built)))
  | ofType d a => exact bind (ih.collection c a) (fun value built => pure (Value.map_built value _ built))
  | ite cond a d =>
    exact bind (ih.formula c cond) (fun cond hc => bind (ih.collection c a)
      (fun left hl => bind (ih.collection c d) (fun right hr =>
        pure (Value.conditional_built left right hl hr hc.defined hc.truth.raw))))

theorem lowerStep_collections (c : Expressions.Context n) (a : IR.Behavioral.Expression.Collections k n) :
    Success Value.Built ((Expressions.lowerStep v b fuel next).collections c a) := by
  cases a with
  | nil => exact pure (Value.pure_built _)
  | cons a ds => exact bind (ih.collection c a) (fun left hl => bind (ih.collections c ds)
      (fun right hr => pure (Value.map_built _ _ (Value.pair_built left right hl hr))))

theorem lowerStep_predicate (c : Expressions.Context n) (a : IR.Behavioral.Expression.Predicate k n) :
    Success Partial.Built ((Expressions.lowerStep v b fuel next).predicate c a) := by
  cases a with
  | inhabited a => exact bind (ih.collection c a) (fun value built => pure (predicate value _ built (fun _ => .mult _ _)))
  | equal a d => exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (predicate _ _ (Value.pair_built left right hl hr) (fun _ => .equal _ _))))
  | subset a d => exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (predicate _ _ (Value.pair_built left right hl hr) (fun _ => .subset _ _))))
  | integerEqual a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (predicate _ _ (Value.pair_built left right hl hr) (fun _ => .compare _ _ _))))
  | less a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (predicate _ _ (Value.pair_built left right hl hr) (fun _ => .compare _ _ _))))

theorem lowerStep_integer (c : Expressions.Context n) (a : IR.Behavioral.Expression.Integer k n) :
    Success Value.Built ((Expressions.lowerStep v b fuel next).integer c a) := by
  cases a with
  | literal z => exact pure (Value.pure_built _)
  | coerce a =>
    apply bind_any (Q := Value.Built)
    intro estimate
    apply bind (Q := Value.Built) (ih.collection c a)
    intro value built
    apply pure (P := Value.Built)
    apply Value.bind_built _ _ built
    intro relation
    apply Value.bind_built _ _ (Value.selections_built _ _ _)
    intro heads
    apply Value.guard_built _ _ (.binary .conj (.subset _ _) (.equal _ _))
    apply integerFold
    intro entry member
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
    exact Value.pure_built _
  | extract a => exact bind_any (fun range => bind (ih.collection c a) (fun value built =>
      pure (Value.bind_built _ _ built (IntegerObservation.extractionBody_built range.values))))
  | cardinality a => exact bind_any (fun range => bind (ih.collection c a) (fun value built =>
      pure (Value.bind_built _ _ built (IntegerObservation.cardinalityBody_built c.lexical.aliases range.budget))))
  | binary op a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (integerBinary op left right hl hr)))
  | negate a => exact bind (ih.integer c a) (fun value built => pure (Value.map_built value _ built))
  | fold op ds body =>
    apply bind_any (Q := Value.Built)
    intro estimates
    apply bind (Q := Value.Built) (ih.collections c ds)
    intro domains hd
    apply valueMapM _ _ hd
    intro relations
    apply valueMapM _ _ (occurrenceChoices c.lexical.aliases _ _ (Value.pure_built _))
    intro occurrences
    apply bind (Q := Value.Built) (mapM _ occurrences (fun _ => ih.integer _ body))
    intro values hv
    exact pure (integerFold op values hv)
  | ite cond a d => exact bind (ih.formula c cond) (fun cond hc => bind (ih.integer c a)
      (fun left hl => bind (ih.integer c d) (fun right hr =>
        pure (Value.conditional_built left right hl hr hc.defined hc.truth.raw))))

theorem lowerStep_atom (c : Expressions.Context n) (a : IR.Behavioral.Expression.Atom k n) :
    Success Partial.Built ((Expressions.lowerStep v b fuel next).atom c a) := by
  cases a with
  | primitive a => exact ih.predicate c a
  | equalClosed left right =>
    apply bind_any (Q := Partial.Built)
    intro left
    apply bind (Q := Partial.Built) (ih.collection _ right)
    intro right hr
    exact pure (predicate right _ hr (fun _ => .equal _ _))
  | inContext domain body =>
    apply bind_any (Q := Partial.Built)
    intro domain
    apply bind (Q := Partial.Built) (ih.formula _ body)
    intro body hb
    exact pure (Partial.atom_built (.all domain hb.defined) (.all domain hb.truth.raw))
  | count q arity disjoint domain body =>
    apply bind_any (Q := Partial.Built)
    intro estimate
    apply bind (Q := Partial.Built) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    apply partialMapM _ _ (selectionChecked c.lexical.aliases relation estimate.budget)
    intro heads
    apply bind (Q := Partial.Built) (mapM _ (Expressions.tuples heads disjoint arity) (fun _ => ih.formula _ body))
    intro bodies hb
    apply pure (P := Partial.Built)
    apply Partial.atom_built
    · apply all
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (hb a ha).defined
    · apply countTruth
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (hb a ha).truth.raw

theorem lowerStep_formula (c : Expressions.Context n) (a : IR.Behavioral.Expression.Formula k n) :
    Success Partial.Built ((Expressions.lowerStep v b fuel next).formula c a) := by
  have parent : (Expressions.parentPresent v c).Built := .binary .disj (.subset _ _) (.mult _ _)
  have present : (Expressions.present v c).Built := .mult _ _
  cases a with
  | truth => exact pure (Partial.atom_built .truth .truth)
  | atom a => exact ih.atom c a
  | not a => exact bind (ih.formula c a) (fun _ h => pure (Partial.negation_built h))
  | and a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (Partial.conjunction_built ha hd)))
  | or a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (Partial.disjunction_built ha hd)))
  | implies a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (Partial.disjunction_built (Partial.negation_built ha) hd)))
  | iff a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure ⟨Encoding.equivalence_built ha.truth hd.truth, .binary .conj ha.defined hd.defined⟩))
  | xor a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (Partial.negation_built
        ⟨Encoding.equivalence_built ha.truth hd.truth, .binary .conj ha.defined hd.defined⟩)))
  | ite cond a d => exact bind (ih.formula c cond) (fun _ hc => bind (ih.formula c a)
      (fun _ ha => bind (ih.formula c d) (fun _ hd => pure (Partial.conditional_built hc ha hd))))
  | next a => exact bind (ih.formula c a) (fun _ h => pure (Partial.next_built parent h))
  | eventually a => exact bind (ih.formula c a) (fun _ h => pure (Partial.eventually_built parent h))
  | always a => exact bind (ih.formula c a) (fun _ h => pure (Partial.always_built parent h))
  | strongUntil a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure ⟨⟨Encoding.until_built parent ha.truth.raw hd.truth.raw,
        Encoding.until_built parent ha.truth.positive hd.truth.positive,
        Encoding.weakUntil_built parent hd.truth.negative (.binary .conj ha.truth.negative hd.truth.negative)⟩,
        Partial.totalAlways_built parent (.binary .conj ha.defined hd.defined)⟩))
  | weakUntil a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure ⟨⟨Encoding.weakUntil_built parent ha.truth.raw hd.truth.raw,
        Encoding.weakUntil_built parent ha.truth.positive hd.truth.positive,
        Encoding.until_built parent hd.truth.negative (.binary .conj ha.truth.negative hd.truth.negative)⟩,
        Partial.totalAlways_built parent (.binary .conj ha.defined hd.defined)⟩))
  | initially a => exact bind (ih.formula c a) (fun _ h => pure
      ⟨⟨Encoding.initially_built present h.truth.raw, Encoding.initially_built present h.truth.positive,
        Encoding.initially_built present h.truth.negative⟩, Encoding.initially_built present h.defined⟩)
  | «finally» a => exact bind (ih.formula c a) (fun _ h => pure
      ⟨⟨Encoding.atEnd_built present h.truth.raw, Encoding.atEnd_built present h.truth.positive,
        Encoding.atEnd_built present h.truth.negative⟩, Encoding.atEnd_built present h.defined⟩)
  | quant q domain body =>
    apply bind_any (Q := Partial.Built)
    intro estimate
    apply bind (Q := Partial.Built) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    exact bind (ih.formula _ body) (fun one h₁ => bind (ih.formula _ body)
      (fun two h₂ => pure (quantify q relation one two h₁ h₂)))
  | letSet domain body =>
    apply bind_any (Q := Partial.Built)
    intro estimate
    apply bind (Q := Partial.Built) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    apply partialMapM _ _ (Value.capture_built _ _ _)
    intro frozen
    exact ih.formula _ body

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem lowerStep : PassBuilt (Expressions.lowerStep v b fuel next) :=
  ⟨lowerStep_collection ih v b fuel, lowerStep_integer ih v b fuel,
    lowerStep_collections ih v b fuel, lowerStep_predicate ih v b fuel,
    lowerStep_atom ih v b fuel, lowerStep_formula ih v b fuel⟩

omit ih in
-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem lowerAt (depth : Nat) : PassBuilt (Expressions.lowerAt v b fuel depth) := by
  induction depth with
  | zero => constructor <;> intro n c a result h <;> cases h
  | succ depth ih => exact lowerStep ih v b fuel

end SyntaxBuilt
end ClaferCompiler.Correctness.Behavioral.Full
