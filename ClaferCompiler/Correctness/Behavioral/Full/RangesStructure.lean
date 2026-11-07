module

public import ClaferCompiler.Correctness.Behavioral.Full.RangesSets
public import ClaferCompiler.Correctness.Behavioral.Full.StructureCardinality
public import ClaferCompiler.Correctness.Behavioral.Full.StructureSteps
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Behavioral.Full

namespace Ranges

/-- Trace-wide capacities and scalar observations. These are finite table data,
not assumptions about the values or truth of compound source expressions. -/
structure StructureBounds (v : IR.BehavioralStructural.Validated k)
    (l : ObservedLasso k o steps) (b : Bounds) : Prop where
  objects : o ≤ b.objects
  pools : ∀ d, integerDeclaration v d = false →
    ({x : Fin o | d ∈ v.analysis.ancestors[l.objects.identities.directType[x]]}).ncard ≤
      (declaredScope v b d).size
  values : ∀ (t : Nat) (x : Fin o), (integerRange b).Contains (l.valuesAt t)[x]

variable {v : IR.BehavioralStructural.Validated k} {p : Fin k}
  {l : ObservedLasso k o steps} {b : Bounds}
local notation "M" => SemanticsBridge.BehavioralStructural.interpret v.core
local notation "CT" => completeTrace v p l
local notation "ST" => Clafer.Behavioral.Structural.observed M CT

/-- A finite occurrence set has no mathematical integer members, so its value
interval is immaterial, including when the declared value interval omits zero. -/
theorem objects_bound (capacity : o ≤ budget) (r : IR.Expr.Interval) :
    CollectionBound (completeIntegers (o := o)) ⟨budget, r⟩ (Set.range Sum.inl) := by
  refine ⟨Set.finite_range _, ?_, ?_⟩
  · simpa only [Set.ncard_range_of_injective Sum.inl_injective,
      Nat.card_fin] using capacity
  · rintro x ⟨y, rfl⟩ hx
    simp only [completeIntegers_domain, reduceCtorEq, exists_false] at hx

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem StructureBounds.head (bounds : StructureBounds v l b)
    (primitive : (v.core.structural.get p).origin = .integer)
    (d : Fin k) (ordinary : integerDeclaration v d = false) (t : Nat) :
    CollectionBound completeIntegers
      ⟨min b.objects (declaredScope v b d).size, ⟨0, 0⟩⟩
      (((ST).raw (M).toEffectiveCore t).head d) := by
  let P : Set (Fin o) := {x | d ∈ v.analysis.ancestors[l.objects.identities.directType[x]]}
  have sub : ((ST).raw (M).toEffectiveCore t).head d ⊆ Sum.inl '' P := by
    intro x hx
    cases x with
    | inl x => exact ⟨x, (ancestor_iff v _ _).mpr hx.2, rfl⟩
    | inr z =>
      have eq := (completeHead_integer v p primitive l t d z).mp hx
      have hi := (integerDeclaration_eq v p primitive d).mpr eq.symm
      rw [ordinary] at hi
      contradiction
  have hf : (Sum.inl '' P : Set (Completion o)).Finite := (Set.toFinite P).image _
  refine ⟨hf.subset sub, ?_, ?_⟩
  · have card := Set.ncard_le_ncard sub hf
    rw [Set.ncard_image_of_injective P Sum.inl_injective] at card
    exact card.trans (le_min ((Set.ncard_le_ncard (Set.subset_univ P)).trans (by simpa using bounds.objects))
      (bounds.pools d ordinary))
  · intro x hx integer
    obtain ⟨y, _, rfl⟩ := sub hx
    simp only [completeIntegers_domain, reduceCtorEq, exists_false] at integer

/-- The image of a functional relation cannot contain more distinct targets
than its finite set of heads. No injectivity of references is required. -/
theorem functional_image_bound {A B : Type} {H : Set A} (finite : H.Finite)
    (R : A → B → Prop) (total : ∀ x ∈ H, ∃! y, R x y)
    (S : Set A) (heads : ∀ x y, R x y → x ∈ H) :
    {y | ∃ x ∈ S, R x y}.Finite ∧ {y | ∃ x ∈ S, R x y}.ncard ≤ H.ncard := by
  classical
  let f : H → B := fun x => (total x x.property).choose
  have sub : {y | ∃ x ∈ S, R x y} ⊆ Set.range f := by
    rintro y ⟨x, _, hxy⟩
    exact ⟨⟨x, heads x y hxy⟩, ((total x (heads x y hxy)).choose_spec.2 y hxy).symm⟩
  let : Fintype H := finite.fintype
  have hf : (Set.range f).Finite := Set.finite_range _
  refine ⟨hf.subset sub, (Set.ncard_le_ncard sub hf).trans ?_⟩
  calc
    (Set.range f).ncard = (f '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set H).ncard := Set.ncard_image_le
    _ = H.ncard := by simp [Set.ncard_univ]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem StructureBounds.inputs (bounds : StructureBounds v l b)
    (primitive : (v.core.structural.get p).origin = .integer)
    (valid : Clafer.Behavioral.Structural.Valid M CT) :
    InputsBound v (estimates v b) ST completeIntegers := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.finite_singleton _, by simp [estimates], ?_⟩
    rintro x hx integer
    obtain rfl := Set.mem_singleton_iff.mp hx
    simp only [Clafer.Behavioral.Structural.observed, completeTrace, completeIdentities,
      completeIntegers_domain, reduceCtorEq, exists_false] at integer
  · intro d allowed t
    have ordinary : integerDeclaration v d = false := by
      simpa [estimates] using allowed
    simpa [estimates, ordinary] using bounds.head primitive d ordinary t
  · intro st allowed t S
    cases st with
    | parent =>
      apply (objects_bound bounds.objects ⟨0, 0⟩).subset
      rintro y ⟨x, _, hxy⟩
      cases y with
      | inl y => exact ⟨y, rfl⟩
      | inr z =>
        have hp := hxy.1
        cases x <;> simp [Clafer.Behavioral.Structural.observed, completeTrace,
          completeIdentities, Option.map_eq_some_iff] at hp
    | child d =>
      have ordinary : integerDeclaration v d = false := by
        simpa [estimates] using allowed
      exact (bounds.head primitive d ordinary t).subset (fun _ ⟨_, _, hy⟩ => ⟨hy.1.2.1, hy.2.1⟩)
    | deref d =>
      cases lookup : v.analysis.referenceOwners[d] with
      | none =>
        have empty : ((SemanticsBridge.Behavioral.step (.deref d)).image
            (M).toEffectiveCore ST t S) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro y ⟨x, _, _, _, ⟨owner, ho, _, _⟩⟩
          have found := SemanticsBridge.BehavioralStructural.owner_complete v.checked.2.1 ho
          rw [lookup] at found
          contradiction
        simpa only [estimates, lookup, empty] using
          (CollectionBound.empty (R := completeIntegers (o := o)))
      | some owner =>
        have ho := SemanticsBridge.BehavioralStructural.owner_sound
          v.checked.2.1 v.checked.1.2.2.2.2.1 lookup
        have ordinary := owner_ordinary v p primitive d owner lookup
        have heads := bounds.head primitive d ordinary t
        have range := functional_image_bound heads.finite
          (Clafer.Behavioral.InheritedReference.deref (M).family ((CT).raw (M).toEffectiveCore t) d)
          (fun _ hx => valid.inherited_reference ho hx) S (fun _ _ h => h.choose_spec.2.1)
        have eq : (SemanticsBridge.Behavioral.step (.deref d)).image (M).toEffectiveCore ST t S =
            {y | ∃ x ∈ S, Clafer.Behavioral.InheritedReference.deref
              (M).family ((CT).raw (M).toEffectiveCore t) d x y} := by
          ext y
          simp only [Clafer.Behavioral.Step.image, SemanticsBridge.Behavioral.step,
            Set.mem_ofPred_eq, Clafer.Behavioral.Structural.observed_deref M CT valid]
        cases target : (v.core.structural.get owner).reference.target with
        | none =>
          obtain ⟨c, hc⟩ := ho.target
          have hc : (v.core.structural.get owner).reference.target = some c := by
            simpa [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret] using hc
          rw [target] at hc
          contradiction
        | some c =>
          refine ⟨eq.symm ▸ range.1, ?_, ?_⟩
          · simpa only [estimates, lookup, target, eq] using range.2.trans heads.card
          · rintro y hy integer
            rw [eq] at hy
            obtain ⟨x, _, hxy⟩ := hy
            obtain ⟨z, rfl⟩ := completeIntegers_domain _ |>.mp integer
            cases x with
            | inr q =>
              have raw := ((Clafer.Behavioral.InheritedReference.deref_owner ho _ _).mp hxy).2
              exact raw.elim
            | inl x =>
              have raw := ((Clafer.Behavioral.InheritedReference.deref_owner ho _ _).mp hxy).2
              have cp : c = p := Option.some.inj (target.symm.trans raw.1)
              subst c
              simpa only [estimates, lookup, target, (integerDeclaration_eq v p primitive p).mpr rfl,
                ↓reduceIte, completeIntegers_decode, ← raw.2.2.2] using bounds.values t x

open Backend.Alloy.Temporal

/-- The finite interval enumeration used by scalar facts has its literal
mathematical membership, independently of whether its bounds fit a bitwidth. -/
theorem integerCandidates_member (r : IR.Expr.Interval) (z : Int) :
    z ∈ integerCandidates r ↔ r.Contains z := by
  simp only [integerCandidates, List.mem_map, List.mem_range, IR.Expr.Interval.Contains, Int.ofNat_eq_natCast]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · rintro ⟨lo, hi⟩
    refine ⟨(z - r.lower).toNat, ?_, ?_⟩ <;> omega

theorem boundedInt_value {w : Nat} {a b : Int}
    (h : Backend.Alloy.boundedInt w a = some b) : a = b := by
  unfold Backend.Alloy.boundedInt at h
  split at h
  · exact Option.some.inj h
  · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem scopeFact_upper (sc : Backend.Alloy.Scope) (r : Rel)
    (s : Schema) (w : Nat) (τ : Trace) (e : Environment) (t : Nat)
    (h : (scopeFact sc r).Holds s w τ e t) :
    (r.eval s w τ e t).eraseDups.length ≤ sc.size := by
  unfold scopeFact at h
  split at h <;>
    change (∃ a b, Backend.Alloy.boundedInt w (Int.ofNat (r.eval s w τ e t).eraseDups.length) = some a ∧
      Backend.Alloy.boundedInt w (Int.ofNat sc.size) = some b ∧ _) at h <;>
    obtain ⟨a, b, ha, hb, hab⟩ := h <;>
    obtain rfl := boundedInt_value ha <;>
    obtain rfl := boundedInt_value hb <;>
    simp only [Backend.Alloy.Comparison.holds, beq_iff_eq, decide_eq_true_eq,
      Int.ofNat_eq_natCast] at hab <;> omega

/-- Scalar range facts constrain all stored observations, including absent
heads whose scalar is later used by a captured identity. -/
theorem scalarFact_value (rep : TraceRep v l target) (b : Bounds) (t : Nat) (x : Fin o)
    (fact : Formula.Holds (schema v) b.bitwidth target.unfold [] 0
      (.unary .always (.subset (.values 0)
        (.product (.sig 0) (union ((integerCandidates (integerRange b)).map Rel.integer)))))) :
    (integerRange b).Contains (l.valuesAt t)[x] := by
  have subset : ∀ u, 0 ≤ u → (Rel.values 0).eval (schema v) b.bitwidth target.unfold [] u ⊆
      (Rel.product (.sig 0) (union ((integerCandidates (integerRange b)).map Rel.integer))).eval
        (schema v) b.bitwidth target.unfold [] u := fact
  have row := subset t (Nat.zero_le _) ((rep.values_completed b.bitwidth [] t _).mpr
    ⟨Sum.inl x, Sum.inr (l.valuesAt t)[x], ⟨x, rfl, rfl⟩, rfl⟩)
  have term : (union ((integerCandidates (integerRange b)).map Rel.integer)).Term := by
    apply union_term _ ?_ _ (.empty _)
    intro r hr
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr
    exact .integer _
  rw [Rel.eval_product (.sig 0) term] at row
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map] at row
  obtain ⟨left, hl, right, hr, eq⟩ := row
  obtain ⟨a, _, he⟩ := (rep.objects_meaning b.bitwidth [] t left).mp hl
  subst left
  have eq : right = [Atom.integer (l.valuesAt t)[x]] := by
    exact (List.cons.inj eq).2
  subst right
  unfold union at hr
  rw [union_rows _ (by intro r hr; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hr; exact .integer _) _ (.empty _)] at hr
  rcases hr with impossible | ⟨r, hr, row⟩
  · exact List.not_mem_nil impossible |>.elim
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
    change [Atom.integer (l.valuesAt t)[x]] ∈ (if Backend.Alloy.fitsInt b.bitwidth z then [[Atom.integer z]] else []) at row
    split at row
    · have eq : (l.valuesAt t)[x] = z := by simpa using row
      exact integerCandidates_member (integerRange b) _ |>.mp (eq.symm ▸ hz)
    · contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Actual emitted scope and scalar facts discharge the structural input
budgets used by the full source range induction. -/
theorem structureBounds_of_facts (rep : TraceRep v l target) (b : Bounds)
    (capacity : o ≤ b.objects)
    (facts : ∀ f ∈ boundFacts v b, f.Holds (schema v) b.bitwidth target.unfold [] 0) :
    StructureBounds v l b := by
  classical
  refine ⟨capacity, ?_, ?_⟩
  · intro d ordinary
    have fact := facts (scopeFact (declaredScope v b d) (pool v d)) (by
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨d, by simp [ordinary], rfl⟩)
    have bound := scopeFact_upper _ _ _ _ _ _ _ fact
    rw [unary_card _ rep.label rep.label_injective _ (rep.pool_meaning b.bitwidth [] 0 d ordinary)] at bound
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter,
      Fintype.card_subtype] using bound
  · intro t x
    exact scalarFact_value rep b t x (facts _ List.mem_cons_self)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem inputs_of_facts (rep : TraceRep v l target) (b : Bounds)
    (primitive : (v.core.structural.get p).origin = .integer)
    (capacity : o ≤ b.objects)
    (facts : ∀ f ∈ boundFacts v b, f.Holds (schema v) b.bitwidth target.unfold [] 0)
    (valid : Clafer.Behavioral.Structural.Valid M CT) :
    InputsBound v (estimates v b) ST completeIntegers :=
  (structureBounds_of_facts rep b capacity facts).inputs primitive valid

end Ranges
end ClaferCompiler.Correctness.Behavioral.Full
