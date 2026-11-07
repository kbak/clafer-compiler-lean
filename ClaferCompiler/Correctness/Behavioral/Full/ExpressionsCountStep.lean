module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsRangeBridge
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsPredicates
public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsBuilt

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.Expressions
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full
open Backend.Alloy.Behavioral.Full.Expressions
open IR.Behavioral

namespace CountStep

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem all_meaning (ps : List Formula) (built : ∀ p ∈ ps, p.Built) :
    (all ps).Holds s w τ e t ↔ ∀ p ∈ ps, p.Holds s w τ e t := by
  induction ps with
  | nil => simp [all]
  | cons p ps ih =>
    change (Formula.binary .conj p (all ps)).Holds s w τ e t ↔ _
    rw [Encoding.holds_and (built p List.mem_cons_self)
      (SyntaxBuilt.all ps (fun q hq => built q (List.mem_cons_of_mem _ hq))),
      ih (fun q hq => built q (List.mem_cons_of_mem _ hq))]
    simp only [List.mem_cons, forall_eq_or_imp]

def compiled (f : α → Result Translation) (x : α) : Translation :=
  match f x with | .ok p => p | .error _ => Backend.Alloy.Behavioral.Partial.truth

theorem compiled_success (h : f x = .ok p) : compiled f x = p := by simp [compiled, h]

theorem mapM_compiled {α : Type} (f : α → Result Translation) (xs : List α) (ys : List Translation)
    (success : xs.mapM f = .ok ys) :
    ys = xs.map (compiled f) ∧ ∀ x ∈ xs, f x = .ok (compiled f x) := by
  have paired := mapM_ok f xs ys success
  clear success
  induction paired with
  | nil => simp
  | @cons x y xs ys hxy paired ih =>
    refine ⟨by simp [compiled_success hxy, ih.1], ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simpa only [compiled_success hxy] using hxy
    · exact ih.2 z hz

def choices (c : Context n) (r : Rel) (budget : Nat) : Value (List Rel) :=
  (Value.selections c.lexical.aliases r budget).bind fun heads =>
    ⟨[(.equal r (Backend.Alloy.Behavioral.Full.union heads), heads)]⟩

theorem choices_built (c : Context n) (r : Rel) (budget : Nat) :
    Full.Value.Built (choices c r budget) := SyntaxBuilt.selectionChecked c.lexical.aliases r budget

theorem choices_selected (h : Full.Value.Meaning s w τ e t (choices c r budget) heads) :
    Full.Value.Meaning s w τ e t (Value.selections c.lexical.aliases r budget) heads := by
  obtain ⟨xs, hx, g, hg, _⟩ := (Full.Value.bind_meaning _ _
    (Full.Value.selections_built _ _ _) (fun _ _ _ h => by
      simp only [List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .equal _ _)).mp h
  simp only [List.mem_singleton, Prod.mk.injEq] at hg
  exact hg.2 ▸ hx

def body (next : Pass k) (c : Context n) (estimate : Expression.Ranges.CollectionEstimate)
    (q : Grouped.Count) (arity : Nat) (disjoint : Bool) (a : Expression.Formula k (n + arity))
    (heads : List Rel) : Result Translation := do
  let bodies ← (tuples heads disjoint arity).mapM fun tuple => next.formula (c.extend tuple estimate) a
  return Backend.Alloy.Behavioral.Partial.atom (all (bodies.map (·.defined)))
    (countTruth q (bodies.map (·.truth.raw)))

theorem body_built {next : Pass k} (ib : SyntaxBuilt.PassBuilt next) (c : Context n)
    (estimate : Expression.Ranges.CollectionEstimate) (q : Grouped.Count)
    (arity : Nat) (disjoint : Bool) (a : Expression.Formula k (n + arity)) (heads : List Rel) :
    SyntaxBuilt.Success Partial.Built (body next c estimate q arity disjoint a heads) := by
  unfold body
  apply SyntaxBuilt.bind (Q := Partial.Built) (SyntaxBuilt.mapM _ _ (fun xs => ib.formula _ _))
  intro bodies built
  apply SyntaxBuilt.pure
  exact Partial.atom_built
    (SyntaxBuilt.all _ (by intro p hp; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp; exact (built b hb).defined))
    (SyntaxBuilt.countTruth q _ (by intro p hp; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp; exact (built b hb).truth.raw))

variable {v : IR.BehavioralStructural.Validated k} {b : Expression.Ranges.Inputs k}
  {s : Schema} {τ : Trace} {σ : Clafer.Behavioral.Trace (Fin k) (Completion o)}
  {labels : Fin o ↪ Nat} {c : Context n} {ρ : Clafer.Behavioral.Environment (Completion o) n}
  {e : Environment} {t : Nat} {next : Pass k}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem body_observation (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (hc : LexicalRows b s τ labels c ρ e)
    (q : Grouped.Count) (arity : Nat) (disjoint : Bool)
    (d : Expression.Collection k n) (a : Expression.Formula k (n + arity))
    (estimate : Expression.Ranges.CollectionEstimate)
    (domainBound : Expression.Ranges.CollectionBound b c.estimates d estimate)
    (bodyBound : Expression.Ranges.FormulaBound b (Expression.Ranges.extend c.estimates arity estimate) a)
    (domainValue : SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d ρ t = some S)
    (r : Rel) (rows : Mixed.Unary (completionAtom labels) S (r.eval s b.width τ e t))
    (heads : List Rel) (selected : Full.Value.Meaning s b.width τ e t
      (Value.selections c.lexical.aliases r estimate.budget) heads)
    (success : body next c estimate q arity disjoint a heads = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (.atom (SemanticsBridge.Behavioral.Expression.countObservation σ q arity disjoint
        (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d)
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a))) result := by
  classical
  have semantic := Ranges.collection_bound hm.ranges hc.ranges domainBound domainValue
  have inside := collection_inside hm hc domainBound domainValue
  obtain ⟨decode, headRows, distinct, members⟩ := Selection.source_heads (Sum.inr 0)
    (completionAtom labels).injective rows (fun entry he => (hc.aliases entry he).term)
    (fun x hx => by obtain ⟨entry, he, rows⟩ := hc.cover x (inside hx); exact ⟨entry, he, rows t⟩)
    semantic.card selected
  have nodup : heads.Nodup := distinct.of_map decode
  have injective : Set.InjOn decode {r | r ∈ heads} := (List.nodup_map_iff_inj_on nodup).mp distinct
  have represented : ∀ x, x ∈ S ↔ ∃ r ∈ heads, decode r = x := by
    intro x; simpa only [List.mem_map] using (members x).symm
  have decoded (r : Rel) (hr : r ∈ heads) : decode r ∈ S :=
    (members _).mp (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have lexical (xs : Vector Rel arity) (hx : xs ∈ tuples heads disjoint arity) :
      LexicalRows b s τ labels (c.extend xs estimate)
        (SemanticsBridge.Behavioral.Grouped.extend ρ arity (Tuples.assignment decode xs)) e := by
    have entries := (Tuples.mem_tuples heads disjoint xs).mp hx
    apply hc.extend decode xs estimate
    · intro i; exact (headRows _ (entries.1 i)).1
    · intro i time row
      rw [← (hc.aliases _ (Selection.selections_members _ _ _ selected _ (entries.1 i))).rows t time row]
      exact (headRows _ (entries.1 i)).2 row
    · intro i; exact inside (decoded _ (entries.1 i))
    · intro i; exact semantic.singleton_member (decoded _ (entries.1 i))
  let f := fun tuple : Vector Rel arity => next.formula (c.extend tuple estimate) a
  cases run : (tuples heads disjoint arity).mapM f with
  | error error => simp [body, f, run] at success
  | ok bodies =>
    have resultEq : result = Backend.Alloy.Behavioral.Partial.atom
        (all (bodies.map (·.defined))) (countTruth q (bodies.map (·.truth.raw))) := by
      simpa only [body, ← show f = (fun tuple => next.formula (c.extend tuple estimate) a) from rfl,
        run, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using success.symm
    subst result
    obtain ⟨rfl, successBody⟩ := mapM_compiled f _ _ run
    have observed xs hx := ih.formula (lexical xs hx) t a (compiled f xs) bodyBound (successBody xs hx)
    have builtDefined : ∀ p ∈ (tuples heads disjoint arity).map (fun xs => (compiled f xs).defined), p.Built := by
      intro p hp; obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hp; exact (observed xs hx).built.defined
    have builtTruth : ∀ p ∈ (tuples heads disjoint arity).map (fun xs => (compiled f xs).truth.raw), p.Built := by
      intro p hp; obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hp; exact (observed xs hx).built.truth.raw
    simp only [List.map_map]
    apply FormulaObservation.atom (SyntaxBuilt.all _ builtDefined) (SyntaxBuilt.countTruth q _ builtTruth)
    · change (all _).Holds s b.width τ e t ↔
        (SemanticsBridge.Behavioral.Expression.countObservation σ q arity disjoint
          (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d)
          (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) ρ t).isSome = true
      rw [all_meaning _ builtDefined]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      have domains : (∀ xs ∈ tuples heads disjoint arity, (compiled f xs).defined.Holds s b.width τ e t) ↔
          ∀ assignment ∈ SemanticsBridge.Behavioral.Grouped.assignments arity disjoint S,
            (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a).Defined σ
              SemanticsBridge.Behavioral.Expression.observation (SemanticsBridge.Behavioral.Grouped.extend ρ arity assignment) t := by
        rw [← Tuples.assignment_image decode heads injective S represented disjoint arity]
        simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        exact forall₂_congr fun xs hx => (observed xs hx).defined
      rw [domains]
      simp only [SemanticsBridge.Behavioral.Expression.countObservation, domainValue, Option.bind_some]
      split <;> simp_all
    · intro P hP
      change SemanticsBridge.Behavioral.Expression.countObservation σ q arity disjoint
        (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d)
        (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a) ρ t = some P at hP
      simp only [SemanticsBridge.Behavioral.Expression.countObservation, domainValue, Option.bind_some] at hP
      split at hP
      · next defined =>
        have eq := Option.some.inj hP
        rw [← eq]
        apply Tuples.countTruth_assignments decode heads nodup injective S represented disjoint arity q
          (fun xs => (compiled f xs).truth.raw) _ s b.width τ e t
        · intro xs hx; exact (observed xs hx).built.truth.raw
        · intro xs hx
          apply (observed xs hx).raw
          apply defined
          rw [← Tuples.assignment_image decode heads injective S represented disjoint arity]
          exact ⟨xs, hx, rfl⟩
      · contradiction

theorem choices_complete (hc : LexicalRows b s τ labels c ρ e)
    (rows : Mixed.Unary (completionAtom labels) S (r.eval s b.width τ e t))
    (inside : S ⊆ observedDomain b.width) (bound : S.ncard ≤ budget) :
    ∃ heads, Full.Value.Meaning s b.width τ e t (choices c r budget) heads := by
  obtain ⟨heads, selected, _, _, equal⟩ := Selection.selections_complete c.lexical.aliases r budget
    (fun entry he => (hc.aliases entry he).term) (fun row hr => by
      obtain ⟨x, hx, rfl⟩ := (rows row).mp hr
      obtain ⟨entry, he, single⟩ := hc.cover x (inside hx)
      exact ⟨entry, he, Mixed.unary_singleton_rows (single t)⟩)
    (by rwa [Mixed.unary_card (completionAtom labels).injective rows])
  refine ⟨heads, (Full.Value.bind_meaning _ _ (Full.Value.selections_built _ _ _)
    (fun _ _ _ h => by
      simp only [List.mem_singleton, Prod.mk.injEq] at h; rw [h.1]; exact .equal _ _)).mpr ?_⟩
  exact ⟨heads, selected, .equal r (Backend.Alloy.Behavioral.Full.union heads),
    List.mem_singleton_self _, fun row => (equal row).symm⟩

theorem defined_domain (σ : Clafer.Behavioral.Trace (Fin k) U)
    (q : Grouped.Count) (arity : Nat) (disjoint : Bool)
    (d : SemanticsBridge.Behavioral.Expression.Observed U (Set U) n)
    (a : SemanticsBridge.Behavioral.Expression.Meaning U (n + arity))
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat)
    (h : (Clafer.Behavioral.Formula.atom
      (SemanticsBridge.Behavioral.Expression.countObservation σ q arity disjoint d a)).Defined
        σ SemanticsBridge.Behavioral.Expression.observation ρ t) :
    ∃ S, d ρ t = some S := by
  obtain ⟨P, hP⟩ := h
  change (d ρ t).bind _ = some P at hP
  obtain ⟨S, hS, _⟩ := Option.bind_eq_some_iff.mp hP
  exact ⟨S, hS⟩

end CountStep

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- Concrete grouped counting includes all ordered tuples and checks every
original body domain before counting its raw truth. -/
theorem countStep (hm : ModelRows v b s τ σ labels)
    (ih : PassObservation v b s τ σ labels next) (ib : SyntaxBuilt.PassBuilt next)
    (hc : LexicalRows b s τ labels c ρ e)
    (bound : Expression.Ranges.AtomBound b c.estimates (.count q arity disjoint d a))
    (success : (lowerStep v b fuel next).atom c (.count q arity disjoint d a) = .ok result) :
    FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
      (.atom (SemanticsBridge.Behavioral.Expression.atom (Sets.model v) σ completeIntegers
        (.count q arity disjoint d a))) result := by
  cases bound with
  | count domainBound bodyBound =>
    change (do
      let estimate ← collectionEstimate b fuel c d
      let domain ← next.collection c d
      partialMapM domain fun relation =>
        partialMapM (CountStep.choices c relation estimate.budget)
          (CountStep.body next c estimate q arity disjoint a)) = .ok result at success
    cases he : collectionEstimate b fuel c d with
    | error error => rw [he] at success; contradiction
    | ok estimate =>
      have same := Expression.Ranges.collection_unique domainBound (collectionEstimate_certificate he)
      have bodyBound : Expression.Ranges.FormulaBound b (Expression.Ranges.extend c.estimates arity estimate) a := same ▸ bodyBound
      have domainBound := collectionEstimate_certificate he
      cases hd : next.collection c d with
      | error error => rw [he, hd] at success; contradiction
      | ok domain =>
        rw [he, hd] at success
        change partialMapM domain (fun relation => partialMapM
          (CountStep.choices c relation estimate.budget)
          (CountStep.body next c estimate q arity disjoint a)) = .ok result at success
        have ha := ih.collection hc t d domain estimate domainBound hd
        change FormulaObservation s b.width τ e t σ SemanticsBridge.Behavioral.Expression.observation ρ
          (.atom (SemanticsBridge.Behavioral.Expression.countObservation σ q arity disjoint
            (SemanticsBridge.Behavioral.Expression.collection (Sets.model v) σ completeIntegers d)
            (SemanticsBridge.Behavioral.Expression.formula (Sets.model v) σ completeIntegers a))) result
        apply partialMapM_observation domain _ result ha.built ?_ success ?_ ?_
        · intro g relation output _ houtput
          exact SyntaxBuilt.partialMapM _ _ (CountStep.choices_built c relation estimate.budget)
            (fun heads => CountStep.body_built ib c estimate q arity disjoint a heads) output houtput
        · intro hdefined
          obtain ⟨S, hS⟩ := CountStep.defined_domain σ q arity disjoint _ _ ρ t hdefined
          exact ha.complete S hS
        · intro relation output hrelation houtput
          obtain ⟨S, hS, _, rows⟩ := ha.sound relation hrelation
          have semantic := Ranges.collection_bound hm.ranges hc.ranges domainBound hS
          have inside := collection_inside hm hc domainBound hS
          apply partialMapM_observation (CountStep.choices c relation estimate.budget)
            (CountStep.body next c estimate q arity disjoint a) output
            (CountStep.choices_built c relation estimate.budget) ?_ houtput ?_ ?_
          · intro g heads result _ hresult
            exact CountStep.body_built ib c estimate q arity disjoint a heads result hresult
          · intro _
            exact CountStep.choices_complete hc rows inside semantic.card
          · intro heads result hheads hresult
            exact CountStep.body_observation hm ih hc q arity disjoint d a estimate domainBound bodyBound
              hS relation rows heads (CountStep.choices_selected hheads) hresult

end ClaferCompiler.Correctness.Behavioral.Full.Expressions
