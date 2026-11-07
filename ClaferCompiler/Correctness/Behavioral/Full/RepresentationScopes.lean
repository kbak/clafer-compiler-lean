module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureBoundedCompleteness
public import ClaferCompiler.Correctness.Behavioral.Full.RangesStructure
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSyntax

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

/-- Budgets observe fixed ancestor pools, including temporarily absent heads.
Exact declarations constrain these pools; signed fits cover emitted counts. -/
structure SourceBoundsFits (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps) (b : Bounds) : Prop where
  objects : o ≤ b.objects
  pools : ∀ d, integerDeclaration v d = false →
    let count := {x : Fin o | d ∈ v.analysis.ancestors[source.objects.identities.directType[x]]}.ncard
    fitsInt b.bitwidth count = true ∧ fitsInt b.bitwidth (declaredScope v b d).size = true ∧
      if (declaredScope v b d).exact then count = (declaredScope v b d).size else count ≤ (declaredScope v b d).size
  values : ∀ t (x : Fin o), (integerRange b).Contains (source.valuesAt t)[x]

variable {v : IR.BehavioralStructural.Validated k} {source : ObservedLasso k o steps} {b : Bounds}

theorem SourceBoundsFits.upper (fit : SourceBoundsFits v source b) (d : Fin k)
    (ordinary : integerDeclaration v d = false) :
    {x : Fin o | d ∈ v.analysis.ancestors[source.objects.identities.directType[x]]}.ncard ≤
      (declaredScope v b d).size := by
  have h := (fit.pools d ordinary).2.2
  split at h
  · exact Nat.le_of_eq h
  · exact h

theorem finiteFilter_card (pred : Fin o → Bool) :
    ((List.finRange o).filter pred).length = {x | pred x = true}.ncard := by
  classical
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange o).filter pred)]
  simp [Set.ncard_eq_toFinset_card', List.toFinset_filter]

theorem lower_foldl_min (values : List Nat) (bound initial : Nat)
    (start : bound ≤ initial) (members : ∀ value ∈ values, bound ≤ value) :
    bound ≤ values.foldl min initial := by
  induction values generalizing initial with
  | nil => exact start
  | cons value values ih =>
    exact ih _ (le_min start (members value List.mem_cons_self))
      (fun x hx => members x (List.mem_cons_of_mem _ hx))

theorem directScope_bound (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps) (b : Bounds) (fits : SourceBoundsFits v source b)
    (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (concrete : ∀ x : Fin o, v.core.authoredAbstract[source.objects.identities.directType[x]] = false)
    (d : Fin k) :
    ((List.finRange o).filter fun x => source.objects.identities.directType[x] == d).length ≤
      (directScope v b d).size := by
  by_cases occupied : ∃ x, x ∈ ((List.finRange o).filter fun x => source.objects.identities.directType[x] == d)
  · obtain ⟨occupiedObject, occupiedMember⟩ := occupied
    have occupiedType : source.objects.identities.directType[occupiedObject] = d :=
      beq_iff_eq.mp (List.mem_filter.mp occupiedMember).2
    have occupiedOrdinary : integerDeclaration v d = false := occupiedType ▸ ordinary occupiedObject
    have occupiedConcrete : v.core.authoredAbstract[d] = false := by
      simpa only [← occupiedType] using concrete occupiedObject
    simp only [directScope, occupiedOrdinary, occupiedConcrete, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    apply lower_foldl_min
    · exact (List.length_filter_le _ _).trans (by simpa using fits.objects)
    · intro value member
      obtain ⟨a, ancestor, rfl⟩ := List.mem_map.mp member
      have ordinaryA : integerDeclaration v a = false := by
        apply Bool.eq_false_iff.mpr
        intro hi
        have primitive : (v.core.structural.get a).origin = .integer := by simpa [integerDeclaration] using hi
        have da := (ancestor_primitive v a d primitive shape).mp ((ancestor_iff v d a).mp ancestor)
        rw [← da, occupiedOrdinary] at hi
        contradiction
      rw [finiteFilter_card]
      apply (Set.ncard_le_ncard ?_).trans (fits.upper a ordinaryA)
      intro x hx
      have eq : source.objects.identities.directType[x] = d := beq_iff_eq.mp hx
      change a ∈ v.analysis.ancestors[source.objects.identities.directType[x]]
      simpa only [eq] using ancestor
  · have empty : ((List.finRange o).filter fun x => source.objects.identities.directType[x] == d) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr (fun x hx => occupied ⟨x, hx⟩)
    rw [empty]
    exact Nat.zero_le _

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem encode_scopes (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps) (b : Bounds) (fits : SourceBoundsFits v source b)
    (shape : PrimitiveShape v)
    (unique : ∀ x y : Fin o, source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (concrete : ∀ x : Fin o, v.core.authoredAbstract[source.objects.identities.directType[x]] = false) :
    (encode source).unfold.InScope (scopes v b) := by
  intro i sc member
  cases i with
  | zero =>
    have eq : sc = ⟨b.objects, false⟩ := by simpa [scopes] using member.symm
    subst sc
    refine ⟨source.objects.identities.ids.toList, labels_nodup _ unique, ?_, ?_⟩
    · intro x
      simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some]
      exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
    · simpa using fits.objects
  | succ i =>
    have hi : i < k := by
      have := (List.getElem?_eq_some_iff.mp member).1
      simp only [scopes, List.length_cons, List.length_map, List.length_finRange] at this
      omega
    let d : Fin k := ⟨i, hi⟩
    have eq : sc = directScope v b d := by simpa [scopes, hi, d] using member.symm
    subst sc
    let objects := (List.finRange o).filter fun x => source.objects.identities.directType[x] == d
    refine ⟨objects.map (fun x => source.objects.identities.ids[x]),
      ((List.nodup_finRange o).filter _).map unique, ?_, ?_⟩
    · intro x
      have index : i + 1 = signatureId d := by simp [signatureId, d, Nat.add_comm]
      simp only [encode_unfold, index, encode_direct]
      exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
    · have exactness : (directScope v b d).exact = false := by unfold directScope; split <;> rfl
      rw [exactness]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_map]
      exact directScope_bound v source b fits shape ordinary concrete d

theorem scopeFact_complete (sc : Scope) (r : Temporal.Rel)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (e : Temporal.Environment) (t : Nat)
    (countFits : fitsInt w (r.eval s w τ e t).eraseDups.length = true)
    (boundFits : fitsInt w sc.size = true)
    (bound : if sc.exact then (r.eval s w τ e t).eraseDups.length = sc.size
      else (r.eval s w τ e t).eraseDups.length ≤ sc.size) :
    (scopeFact sc r).Holds s w τ e t := by
  have countValue : boundedInt w (r.eval s w τ e t).eraseDups.length =
      some (r.eval s w τ e t).eraseDups.length := by simp [boundedInt, countFits]
  have boundValue : boundedInt w sc.size = some sc.size := by simp [boundedInt, boundFits]
  cases exactness : sc.exact with
  | false =>
    simp only [scopeFact, exactness, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, _, countValue, boundValue, ?_⟩
    simp only [exactness, Bool.false_eq_true, ↓reduceIte] at bound
    simp only [Comparison.holds, decide_eq_true_eq]
    omega
  | true =>
    simp only [scopeFact, exactness, ↓reduceIte]
    refine ⟨_, _, countValue, boundValue, ?_⟩
    simp only [exactness, ↓reduceIte] at bound
    simpa only [Comparison.holds, beq_iff_eq, Int.ofNat_eq_natCast, Int.natCast_inj] using bound

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Temporal.Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem boundFacts_complete (rep : TraceRep v source target) (b : Bounds)
    (fits : SourceBoundsFits v source b)
    (scalarFits : ∀ t (x : Fin o), fitsInt b.bitwidth (source.valuesAt t)[x] = true) :
    ∀ fact ∈ boundFacts v b, fact.Holds (schema v) b.bitwidth target.unfold [] 0 := by
  intro fact member
  rcases List.mem_cons.mp member with rfl | member
  · intro t _ row member
    obtain ⟨x, y, ⟨a, rfl, rfl⟩, rfl⟩ := (rep.values_completed b.bitwidth [] t row).mp member
    have terms : (union ((integerCandidates (integerRange b)).map Temporal.Rel.integer)).Term := by
      apply union_term _ ?_ _ (.empty _)
      intro r hr
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr
      exact .integer _
    rw [Temporal.Rel.eval_product (.sig 0) terms]
    apply List.mem_eraseDups.mpr
    apply List.mem_flatMap.mpr
    refine ⟨[.object (rep.label a)], (rep.objects_meaning b.bitwidth [] t _).mpr ⟨a, Set.mem_univ _, rfl⟩, ?_⟩
    apply List.mem_map.mpr
    refine ⟨[.integer (source.valuesAt t)[a]], ?_, rfl⟩
    unfold union
    rw [union_rows _ (by intro r hr; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr; exact .integer _) _ (.empty _)]
    apply Or.inr
    refine ⟨.integer (source.valuesAt t)[a], List.mem_map.mpr
      ⟨_, (Ranges.integerCandidates_member _ _).mpr (fits.values t a), rfl⟩, ?_⟩
    change [Atom.integer (source.valuesAt t)[a]] ∈ (if fitsInt b.bitwidth (source.valuesAt t)[a] then _ else [])
    rw [scalarFits t a]
    exact List.mem_singleton_self _
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp member
    have ordinary : integerDeclaration v d = false := by
      simpa only [List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true'] using hd
    have card := unary_card (fun x : Fin o => d ∈ v.analysis.ancestors[source.objects.identities.directType[x]])
      rep.label rep.label_injective _ (rep.pool_meaning b.bitwidth [] 0 d ordinary)
    have card : ((pool v d).eval (schema v) b.bitwidth target.unfold [] 0).eraseDups.length =
        {x : Fin o | d ∈ v.analysis.ancestors[source.objects.identities.directType[x]]}.ncard := by
      simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter, Fintype.card_subtype] using card
    apply scopeFact_complete
    · exact card ▸ (fits.pools d ordinary).1
    · exact (fits.pools d ordinary).2.1
    · exact card ▸ (fits.pools d ordinary).2.2

end TraceRep
-- [proof->req~compiler-full-behavioral-correctness~1]
/-- All generated structural and budget clauses hold for the concrete encoded
lasso. This is the structural component consumed by full compile completeness. -/
theorem encode_full_structure (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (source : ObservedLasso k o steps) (b : Bounds)
    (structuralFits : StructuralFits v p source b.bitwidth b.objects)
    (scopeFits : SourceBoundsFits v source b)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    (encode source).unfold.Declarations (schema v) ∧
    (encode source).unfold.InScope (scopes v b) ∧
    (∀ t, ((encode source).unfold.state t).scalarFields b.bitwidth (schema v).declarations = true) ∧
    (∀ fact ∈ identityFacts v ++ boundFacts v b ++
      (stateFacts v ++ [reachabilityFact v b.objects]).map (Formula.unary .always),
      fact.Holds (schema v) b.bitwidth (encode source).unfold [] 0) := by
  obtain ⟨declarations, scalars, identity, states, reach⟩ :=
    encode_structural_complete v p primitive shape source b.bitwidth b.objects structuralFits valid
  have ids := completeIdentities_restrict v p source valid.identities
  let rep := encode_rep v source structuralFits.unique ids.root_type ids.root_only
  refine ⟨declarations, encode_scopes v source b scopeFits shape structuralFits.unique
    structuralFits.ordinary ids.concrete, scalars, ?_⟩
  intro fact member
  simp only [List.mem_append] at member
  rcases member with (hi | hb) | hs
  · exact identity fact hi
  · exact rep.boundFacts_complete b scopeFits structuralFits.scalars fact hb
  · obtain ⟨inner, member, rfl⟩ := List.mem_map.mp hs
    rcases List.mem_append.mp member with state | boundedReach
    · rw [always_holds (stateFacts_built v inner state)]
      exact fun t _ => states t inner state
    · have eq := List.mem_singleton.mp boundedReach
      subst inner
      rw [always_holds (show (reachabilityFact v b.objects).Built from .subset _ _)]
      exact fun t _ => reach t


end ClaferCompiler.Correctness.Behavioral.Full
