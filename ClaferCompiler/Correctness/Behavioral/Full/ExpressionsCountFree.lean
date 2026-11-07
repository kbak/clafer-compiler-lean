module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsDefinedPartial
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full
open TargetDefined
namespace CountFree

/-- Every emitted alternative, including inactive alternatives, has pure
arithmetic guards and payloads. No source truth premise selects a branch. -/
def ValuePure (P : α → Prop) (a : Backend.Alloy.Behavioral.Full.Value α) : Prop :=
  ∀ g x, (g, x) ∈ a.cases → FormulaPure g ∧ P x

abbrev GuardPure (a : Backend.Alloy.Behavioral.Full.Value α) := ValuePure (fun _ => True) a

namespace ValuePure

theorem pure (x : α) (h : P x) : ValuePure P (Value.pure x) := by
  intro g y member
  have eq := List.mem_singleton.mp member
  cases eq
  exact ⟨pure_truth, h⟩

theorem map (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → β)
    (ha : ValuePure P a) (hf : ∀ x, P x → Q (f x)) : ValuePure Q (a.map f) := by
  intro g y member
  obtain ⟨⟨h, x⟩, hx, eq⟩ := List.mem_map.mp member
  cases eq
  exact ⟨(ha _ _ hx).1, hf x (ha _ _ hx).2⟩

theorem bind (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Backend.Alloy.Behavioral.Full.Value β)
    (ha : ValuePure P a) (hf : ∀ x, P x → ValuePure Q (f x)) : ValuePure Q (a.bind f) := by
  intro g y member
  obtain ⟨⟨h, x⟩, hx, member⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨guard, value⟩, hv, eq⟩ := List.mem_map.mp member
  cases eq
  obtain ⟨hp, px⟩ := ha _ _ hx
  obtain ⟨gp, qy⟩ := hf x px _ _ hv
  exact ⟨(pure_binary _ _ _).mpr ⟨hp, gp⟩, qy⟩

theorem pair (a : Backend.Alloy.Behavioral.Full.Value α) (b : Backend.Alloy.Behavioral.Full.Value β)
    (ha : ValuePure P a) (hb : ValuePure Q b) : ValuePure (fun xy => P xy.1 ∧ Q xy.2) (a.pair b) :=
  bind a _ ha fun _ hx => map b _ hb fun _ hy => ⟨hx, hy⟩

theorem guard (a : Backend.Alloy.Behavioral.Full.Value α) (p : Formula)
    (ha : ValuePure P a) (hp : FormulaPure p) : ValuePure P (Value.guard p a) := by
  intro g y member
  obtain ⟨⟨h, x⟩, hx, eq⟩ := List.mem_map.mp member
  cases eq
  exact ⟨(pure_binary _ _ _).mpr ⟨hp, (ha _ _ hx).1⟩, (ha _ _ hx).2⟩

theorem weaken (ha : ValuePure P a) (h : ∀ x, P x → Q x) : ValuePure Q a :=
  fun g x member => ⟨(ha g x member).1, h x (ha g x member).2⟩

theorem use (a : Backend.Alloy.Behavioral.Full.Value α) (f : α → Formula)
    (ha : ValuePure P a) (hf : ∀ x, P x → FormulaPure (f x)) : FormulaPure (a.use f) := by
  rcases a with ⟨xs⟩
  induction xs with
  | nil => exact pure_falsity
  | cons pair xs ih =>
    obtain ⟨guard, payload⟩ := pair
    have h := ha guard payload List.mem_cons_self
    exact (pure_binary _ _ _).mpr ⟨(pure_binary _ _ _).mpr ⟨h.1, hf payload h.2⟩,
      ih (fun g x hx => ha g x (List.mem_cons_of_mem _ hx))⟩

theorem selections (aliases : List Rel) (domain : Rel) (budget : Nat) :
    GuardPure (Value.selections aliases domain budget) := by
  have fold (initial : Backend.Alloy.Behavioral.Full.Value (List Rel × Rel)) (hi : GuardPure initial) :
      GuardPure (aliases.foldl (fun values entry => values.bind fun (chosen, seen) =>
        let member := Formula.binary .conj (.mult .one entry)
          (.binary .conj (.subset entry domain) (.unary .neg (.subset entry seen)))
        ⟨if chosen.length < budget then
          [(member, (entry :: chosen, .union seen entry)), (.unary .neg member, (chosen, seen))]
         else [(.unary .neg member, (chosen, seen))]⟩) initial) := by
    induction aliases generalizing initial with
    | nil => exact hi
    | cons entry aliases ih =>
      apply ih
      apply bind _ _ hi
      rintro ⟨chosen, seen⟩ _ g x member
      dsimp only at member
      split at member
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
        rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by simp, trivial⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at member
        rcases member with ⟨rfl, _⟩
        exact ⟨by simp, trivial⟩
  exact map _ _ (fold _ (pure _ trivial)) (fun _ _ => trivial)

theorem capture (aliases : List Rel) (domain : Rel) (budget : Nat) :
    GuardPure (Value.capture aliases domain budget) := by
  apply bind _ _ (selections aliases domain budget)
  intro selected _ g x member
  cases List.mem_singleton.mp member
  exact ⟨pure_equal _ _, trivial⟩

theorem conditional (a b : Backend.Alloy.Behavioral.Full.Value α)
    (ha : ValuePure P a) (hb : ValuePure P b) (hd : FormulaPure c.defined) (hr : FormulaPure c.truth.raw) :
    ValuePure P (Value.conditional c a b) := by
  apply bind _ _ (pair a b ha hb)
  intro pair h g x member
  rcases List.mem_cons.mp member with eq | member
  · cases eq
    exact ⟨(pure_binary _ _ _).mpr ⟨hd, hr⟩, h.1⟩
  · cases List.mem_singleton.mp member
    exact ⟨by simpa using And.intro hd hr, h.2⟩

end ValuePure

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem integerBinary (op : IR.BehavioralArithmetic.Binary)
    (ha : ValuePure IntegerPure a) (hb : ValuePure IntegerPure b) :
    ValuePure IntegerPure (Backend.Alloy.Behavioral.Full.integerBinary op a b) :=
  ValuePure.map _ _ (ValuePure.pair _ _ ha hb) (fun _ h => .binary op h.1 h.2)

theorem integerFold (op : IR.BehavioralArithmetic.Fold)
    (values : List (Backend.Alloy.Behavioral.Full.Value Integer))
    (hv : ∀ a ∈ values, ValuePure IntegerPure a) :
    ValuePure IntegerPure (Backend.Alloy.Behavioral.Full.integerFold op values) := by
  have fold (initial : Backend.Alloy.Behavioral.Full.Value Integer) (hi : ValuePure IntegerPure initial) :
      ValuePure IntegerPure (values.foldl (fun r a => Backend.Alloy.Behavioral.Full.integerBinary
        (if op == .sum then .add else .multiply) r a) initial) := by
    induction values generalizing initial with
    | nil => exact hi
    | cons a values ih =>
      exact ih (fun v h => hv v (List.mem_cons_of_mem _ h)) _
        (integerBinary _ hi (hv a List.mem_cons_self))
  exact fold _ (ValuePure.pure _ (.literal _))

theorem extreme (op : IR.Behavioral.Primitive.Extreme) (r : IR.Expr.Interval)
    (ha : GuardPure a) : GuardPure (collectionExtreme op r a) := by
  apply ValuePure.bind _ _ ha
  intro value _ g result member
  simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨z, _, eq, _⟩
  · exact ⟨pure_equal _ _, trivial⟩
  · rw [← eq]
    exact ⟨by simp, trivial⟩

open SyntaxBuilt (Success)

theorem predicate (a : Backend.Alloy.Behavioral.Full.Value α) (ha : ValuePure P a) (f : α → Formula)
    (hf : ∀ x, P x → FormulaPure (f x)) : PartialPure (Value.predicate a f) :=
  partial_atom (ValuePure.use _ _ ha (fun _ _ => pure_truth)) (ValuePure.use _ _ ha hf)

theorem all (ps : List Formula) (h : ∀ p ∈ ps, FormulaPure p) : FormulaPure (Expressions.all ps) := by
  induction ps with
  | nil => exact pure_truth
  | cons p ps ih =>
    exact (pure_binary _ _ _).mpr
      ⟨h _ List.mem_cons_self, ih (fun _ member => h _ (List.mem_cons_of_mem _ member))⟩

theorem countTruth (q : IR.Behavioral.Grouped.Count) (ps : List Formula)
    (h : ∀ p ∈ ps, FormulaPure p) : FormulaPure (Expressions.countTruth q ps) := by
  have fold (initial : Formula × Formula) (hi : FormulaPure initial.1 ∧ FormulaPure initial.2) :
      FormulaPure (ps.foldl countStep initial).1 ∧ FormulaPure (ps.foldl countStep initial).2 := by
    induction ps generalizing initial with
    | nil => exact hi
    | cons p ps ih =>
      have hp := h p List.mem_cons_self
      apply ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      simpa only [countStep, pure_binary, pure_unary] using
        And.intro (And.intro hi.1 hp) (And.intro (And.intro hi.2 hp) (And.intro hi.1 hp))
  have h := fold (.truth, .falsity) ⟨pure_truth, pure_falsity⟩
  cases q with
  | one => exact h.2
  | lone => exact (pure_binary _ _ _).mpr h

theorem valueMapM (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Expressions.Result (Backend.Alloy.Behavioral.Full.Value β))
    (ha : GuardPure a) (hf : ∀ x, Success (ValuePure P) (f x)) :
    Success (ValuePure P) (Expressions.valueMapM a f) := by
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
    have all : ∀ g x, (g, x) ∈ choices.flatten → FormulaPure g ∧ P x := by
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
            exact ⟨(pure_binary _ _ _).mpr ⟨(ha _ _ List.mem_cons_self).1,
              (hf input.2 value ho h _ hy).1⟩, (hf input.2 value ho h _ hy).2⟩
          · exact ih (fun g x hx => ha g x (List.mem_cons_of_mem _ hx)) g x member
    exact all

theorem partialMapM (a : Backend.Alloy.Behavioral.Full.Value α)
    (f : α → Expressions.Result Backend.Alloy.Behavioral.Partial.Translation)
    (ha : GuardPure a) (hf : ∀ x, Success PartialPure (f x)) :
    Success PartialPure (Expressions.partialMapM a f) := by
  intro result success
  obtain ⟨choices, paired, eq⟩ := Expressions.partialMapM_cases a f result success
  have hc : ValuePure PartialPure (Value.mk choices) := by
    intro guard body member
    obtain ⟨x, input, value⟩ := (Expressions.partial_cases_member f paired guard body).mp member
    exact ⟨(ha guard x input).1, hf x body value⟩
  subst result
  exact ⟨ValuePure.use _ _ hc (fun _ h => h.1),
    ValuePure.use _ _ hc (fun _ h => h.2.1),
    ValuePure.use _ _ hc (fun _ h => h.2.2.1),
    ValuePure.use _ _ hc (fun _ h => h.2.2.2)⟩

theorem selectionChecked (aliases : List Rel) (domain : Rel) (budget : Nat) :
    GuardPure ((Value.selections aliases domain budget).bind fun heads =>
      ⟨[(Formula.equal domain (union heads), heads)]⟩) := by
  apply ValuePure.bind _ _ (ValuePure.selections aliases domain budget)
  intro heads _ g x member
  cases List.mem_singleton.mp member
  exact ⟨pure_equal _ _, trivial⟩

theorem occurrenceChoices (aliases : List Rel)
    (domains : List (Rel × IR.Behavioral.Expression.Ranges.CollectionEstimate))
    (initial : Backend.Alloy.Behavioral.Full.Value (List Rel)) (hi : GuardPure initial) :
    GuardPure (domains.foldl (fun choices (relation, estimate) =>
      (choices.pair ((Value.selections aliases relation estimate.budget).bind fun heads =>
        ⟨[(Formula.equal relation (union heads), heads)]⟩)).map
          (fun (before, now) => before ++ now)) initial) := by
  induction domains generalizing initial with
  | nil => exact hi
  | cons pair domains ih =>
    exact ih _ (ValuePure.map _ _ (ValuePure.pair _ _ hi
      (selectionChecked aliases pair.1 pair.2.budget)) (fun _ _ => trivial))

/-- Constructor invariant for all emitted alternatives, independent of source
values or guards that happen to hold in a particular state. -/
structure PassPure (next : Expressions.Pass k) : Prop where
  collection : ∀ {n} (c : Expressions.Context n) a, Success GuardPure (next.collection c a)
  integer : ∀ {n} (c : Expressions.Context n) a, Success (ValuePure IntegerPure) (next.integer c a)
  collections : ∀ {n} (c : Expressions.Context n) a, Success GuardPure (next.collections c a)
  predicate : ∀ {n} (c : Expressions.Context n) a, Success PartialPure (next.predicate c a)
  atom : ∀ {n} (c : Expressions.Context n) a, Success PartialPure (next.atom c a)
  formula : ∀ {n} (c : Expressions.Context n) a, Success PartialPure (next.formula c a)

open SyntaxBuilt (bind bind_any pure mapM)
variable {next : Expressions.Pass k} (ih : PassPure next)
  (v : IR.BehavioralStructural.Validated k) (b : IR.Behavioral.Expression.Ranges.Inputs k) (fuel : Nat)
include ih

theorem lowerStep_collection (c : Expressions.Context n) (a : IR.Behavioral.Expression.Collection k n) :
    Success GuardPure ((Expressions.lowerStep v b fuel next).collection c a) := by
  cases a with
  | set a => exact bind_any (fun r => pure (ValuePure.pure r trivial))
  | literal z => exact pure (ValuePure.pure _ trivial)
  | integer a =>
    apply bind_any (Q := GuardPure)
    intro range
    apply bind (Q := GuardPure) (ih.integer c a)
    intro value hv
    apply SyntaxBuilt.pure
    apply ValuePure.bind _ _ hv
    intro term ht g result member
    obtain ⟨z, _, eq⟩ := List.mem_map.mp member
    cases eq
    exact ⟨(pure_compare _ _ _).mpr ⟨ht, .literal z⟩, trivial⟩
  | extreme op a =>
    exact bind_any (fun range => bind (ih.collection c a) (fun value hv => pure (extreme op range.values hv)))
  | union a d | inter a d | diff a d =>
    exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (ValuePure.map _ _ (ValuePure.pair left right hl hr) (fun _ _ => trivial))))
  | step st a =>
    exact bind_any (fun _ => bind (ih.collection c a) (fun value hv =>
      pure (ValuePure.map value _ hv (fun _ _ => trivial))))
  | ofType d a => exact bind (ih.collection c a) (fun value hv =>
      pure (ValuePure.map value _ hv (fun _ _ => trivial)))
  | ite cond a d =>
    exact bind (ih.formula c cond) (fun cond hc => bind (ih.collection c a)
      (fun left hl => bind (ih.collection c d) (fun right hr =>
        pure (ValuePure.conditional left right hl hr hc.2.2.2 hc.1))))

theorem lowerStep_collections (c : Expressions.Context n) (a : IR.Behavioral.Expression.Collections k n) :
    Success GuardPure ((Expressions.lowerStep v b fuel next).collections c a) := by
  cases a with
  | nil => exact pure (ValuePure.pure _ trivial)
  | cons a ds => exact bind (ih.collection c a) (fun left hl => bind (ih.collections c ds)
      (fun right hr => pure (ValuePure.map _ _ (ValuePure.pair left right hl hr) (fun _ _ => trivial))))

theorem lowerStep_predicate (c : Expressions.Context n) (a : IR.Behavioral.Expression.Predicate k n) :
    Success PartialPure ((Expressions.lowerStep v b fuel next).predicate c a) := by
  cases a with
  | inhabited a => exact bind (ih.collection c a) (fun value hv =>
      pure (predicate value hv _ (fun _ _ => pure_mult _ _)))
  | equal a d => exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (predicate _ (ValuePure.pair left right hl hr) _ (fun _ _ => pure_equal _ _))))
  | subset a d => exact bind (ih.collection c a) (fun left hl => bind (ih.collection c d)
      (fun right hr => pure (predicate _ (ValuePure.pair left right hl hr) _ (fun _ _ => pure_subset _ _))))
  | integerEqual a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (predicate _ (ValuePure.pair left right hl hr) _
        (fun _ h => (pure_compare _ _ _).mpr h))))
  | less a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (predicate _ (ValuePure.pair left right hl hr) _
        (fun _ h => (pure_compare _ _ _).mpr h))))

theorem lowerStep_integer (c : Expressions.Context n) (a : IR.Behavioral.Expression.Integer k n) :
    Success (ValuePure IntegerPure) ((Expressions.lowerStep v b fuel next).integer c a) := by
  cases a with
  | literal z => exact pure (ValuePure.pure _ (.literal z))
  | coerce a =>
    apply bind_any (Q := ValuePure IntegerPure)
    intro estimate
    apply bind (Q := ValuePure IntegerPure) (ih.collection c a)
    intro value hv
    apply SyntaxBuilt.pure
    apply ValuePure.bind _ _ hv
    intro relation _
    apply ValuePure.bind _ _ (ValuePure.selections _ _ _)
    intro heads _
    apply ValuePure.guard _ _ _ (by simp)
    apply integerFold
    intro entry member
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
    exact ValuePure.pure _ (.scalar _ _ _)
  | extract a =>
    apply bind_any (Q := ValuePure IntegerPure)
    intro range
    apply bind (Q := ValuePure IntegerPure) (ih.collection c a)
    intro value hv
    apply SyntaxBuilt.pure
    apply ValuePure.bind _ _ hv
    intro relation _ g result member
    cases List.mem_singleton.mp member
    exact ⟨by simp, .scalar _ _ _⟩
  | cardinality a =>
    apply bind_any (Q := ValuePure IntegerPure)
    intro range
    apply bind (Q := ValuePure IntegerPure) (ih.collection c a)
    intro value hv
    apply SyntaxBuilt.pure
    apply ValuePure.bind _ _ hv
    intro relation _
    apply ValuePure.bind _ _ (ValuePure.selections _ _ _)
    intro heads _ g result member
    cases List.mem_singleton.mp member
    exact ⟨pure_equal _ _, .literal _⟩
  | binary op a d => exact bind (ih.integer c a) (fun left hl => bind (ih.integer c d)
      (fun right hr => pure (integerBinary op hl hr)))
  | negate a => exact bind (ih.integer c a) (fun value hv =>
      pure (ValuePure.map value _ hv (fun _ h => .binary .subtract (.literal 0) h)))
  | fold op ds body =>
    apply bind_any (Q := ValuePure IntegerPure)
    intro estimates
    apply bind (Q := ValuePure IntegerPure) (ih.collections c ds)
    intro domains hd
    apply valueMapM _ _ hd
    intro relations
    apply valueMapM _ _ (occurrenceChoices c.lexical.aliases _ _ (ValuePure.pure _ trivial))
    intro occurrences
    apply bind (Q := ValuePure IntegerPure) (mapM _ occurrences (fun _ => ih.integer _ body))
    intro values hv
    exact pure (integerFold op values hv)
  | ite cond a d => exact bind (ih.formula c cond) (fun cond hc => bind (ih.integer c a)
      (fun left hl => bind (ih.integer c d) (fun right hr =>
        pure (ValuePure.conditional left right hl hr hc.2.2.2 hc.1))))

theorem lowerStep_atom (c : Expressions.Context n) (a : IR.Behavioral.Expression.Atom k n) :
    Success PartialPure ((Expressions.lowerStep v b fuel next).atom c a) := by
  cases a with
  | primitive a => exact ih.predicate c a
  | count q arity disjoint domain body =>
    apply bind_any (Q := PartialPure)
    intro estimate
    apply bind (Q := PartialPure) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    apply partialMapM _ _ (selectionChecked c.lexical.aliases relation estimate.budget)
    intro heads
    apply bind (Q := PartialPure) (mapM _ (Expressions.tuples heads disjoint arity) (fun _ => ih.formula _ body))
    intro bodies hb
    apply SyntaxBuilt.pure
    apply partial_atom
    · apply all
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (hb a ha).2.2.2
    · apply countTruth
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (hb a ha).1

theorem lowerStep_formula (c : Expressions.Context n) (a : IR.Behavioral.Expression.Formula k n) :
    Success PartialPure ((Expressions.lowerStep v b fuel next).formula c a) := by
  have parent : FormulaPure (Expressions.parentPresent v c) := by simp [Expressions.parentPresent]
  have present : FormulaPure (Expressions.present v c) := by simp [Expressions.present]
  cases a with
  | truth => exact pure partial_truth
  | atom a => exact ih.atom c a
  | not a => exact bind (ih.formula c a) (fun _ h => pure (partial_negation h))
  | and a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_conjunction ha hd)))
  | or a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_disjunction ha hd)))
  | implies a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_implication ha hd)))
  | iff a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_equivalence ha hd)))
  | xor a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_exclusiveOr ha hd)))
  | ite cond a d => exact bind (ih.formula c cond) (fun _ hc => bind (ih.formula c a)
      (fun _ ha => bind (ih.formula c d) (fun _ hd => pure (partial_conditional hc ha hd))))
  | next a => exact bind (ih.formula c a) (fun _ h => pure (partial_next parent h))
  | eventually a => exact bind (ih.formula c a) (fun _ h => pure (partial_eventually parent h))
  | always a => exact bind (ih.formula c a) (fun _ h => pure (partial_always parent h))
  | strongUntil a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_strongUntil parent ha hd)))
  | weakUntil a d => exact bind (ih.formula c a) (fun _ ha => bind (ih.formula c d)
      (fun _ hd => pure (partial_weakUntil parent ha hd)))
  | initially a => exact bind (ih.formula c a) (fun _ h => pure (partial_initially present h))
  | «finally» a => exact bind (ih.formula c a) (fun _ h => pure (partial_finally present h))
  | quant q domain body =>
    apply bind_any (Q := PartialPure)
    intro estimate
    apply bind (Q := PartialPure) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    exact bind (ih.formula _ body) (fun one h₁ => bind (ih.formula _ body)
      (fun two h₂ => pure (partial_quantify q relation pure_truth h₁ h₂)))
  | letSet domain body =>
    apply bind_any (Q := PartialPure)
    intro estimate
    apply bind (Q := PartialPure) (ih.collection c domain)
    intro domain hd
    apply partialMapM _ _ hd
    intro relation
    apply partialMapM _ _ (ValuePure.capture _ _ _)
    intro frozen
    exact ih.formula _ body

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem lowerStep : PassPure (Expressions.lowerStep v b fuel next) :=
  ⟨lowerStep_collection ih v b fuel, lowerStep_integer ih v b fuel,
    lowerStep_collections ih v b fuel, lowerStep_predicate ih v b fuel,
    lowerStep_atom ih v b fuel, lowerStep_formula ih v b fuel⟩

omit ih in
-- [proof->req~compiler-full-behavioral-correctness~1]
theorem lowerAt (depth : Nat) : PassPure (Expressions.lowerAt v b fuel depth) := by
  induction depth with
  | zero => constructor <;> intro n c a result h <;> cases h
  | succ depth ih => exact lowerStep ih v b fuel

end CountFree
end ClaferCompiler.Correctness.Behavioral.Full
