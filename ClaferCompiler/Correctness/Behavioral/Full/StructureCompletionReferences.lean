module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionMixed

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem object_typing_of_valid (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (t : Nat) (valid : Clafer.Behavioral.Structural.StateValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t)
    (d : Fin k) (x y : Fin o) (h : (d, x, y) ∈ (source.objects.at t).references) :
    ∃ c, (v.core.structural.get d).reference.target = some c ∧ integerDeclaration v c = false := by
  obtain ⟨_, c, target, head⟩ := valid.typed.2 d (Sum.inl x) (Sum.inl y) h
  have target : (v.core.structural.get d).reference.target = some c := by
    simpa only [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret,
      SemanticsBridge.Structural.reference_target] using target
  refine ⟨c, target, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hi
  have cp := (integerDeclaration_eq v p primitive c).mp hi
  subst c
  have primitiveHead := completeHead_primitive v p primitive shape source (fun x hx => by
    have ho := ordinary x
    rw [hx, (integerDeclaration_eq v p primitive p).mpr rfl] at ho
    contradiction) t
  rw [primitiveHead] at head
  simp only [completeIntegers_domain, reduceCtorEq, exists_false] at head

theorem bounded_head_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat) (d : Fin k) :
    Mixed.Unary rep.atoms
      (((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ∩ observedDomain w)
      ((head v d).eval (schema v) w target.unfold e t) := by
  cases hd : integerDeclaration v d with
  | false =>
    apply Mixed.unary_congr (rep.head_completed p primitive w e t d hd)
    intro x
    exact ⟨fun h => ⟨h, head_inside p primitive w t d hd h⟩, And.left⟩
  | true =>
    have dp := (integerDeclaration_eq v p primitive d).mp hd
    subst d
    have primitiveHead := completeHead_primitive v p primitive shape source (fun x hx => by
      have ho := ordinary x
      rw [hx, hd] at ho
      contradiction) t
    simp only [head, hd, ↓reduceIte, primitiveHead]
    apply Mixed.unary_congr (rep.ints_completed w positive small e t)
    intro x
    cases x <;> simp [observedDomain]

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem referenceFacts_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (valid : Clafer.Behavioral.Structural.StateValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t)
    (d : Fin k) : ∀ fact ∈ referenceFacts v d, fact.Holds (schema v) w target.unfold [] t := by
  have typed := object_typing_of_valid p primitive shape ordinary t valid
  have empty (none : (v.core.structural.get d).reference.target = none ∨
      (v.core.structural.get d).reference.target = some p) :
      (Formula.equal (rawDeref d) (.empty .binary)).Holds (schema v) w target.unfold [] t := by
    intro row
    constructor
    · intro hr
      obtain ⟨x, y, ref, _⟩ := (rep.rawDeref_meaning w [] t d row).mp hr
      obtain ⟨c, hc, ho⟩ := typed d x y ref
      rcases none with none | int
      · rw [none] at hc
        contradiction
      · have cp : c = p := Option.some.inj (hc.symm.trans int)
        subst c
        rw [(integerDeclaration_eq v p primitive p).mpr rfl] at ho
        contradiction
    · exact fun h => (List.not_mem_nil h).elim
  intro fact member
  cases target : (v.core.structural.get d).reference.target with
  | none =>
    simp only [referenceFacts, target, List.mem_singleton] at member
    subst fact
    exact empty (Or.inl target)
  | some c =>
    have sourceTarget : ((SemanticsBridge.BehavioralStructural.interpret v.core).family.reference d).target = some c := by
      simpa only [SemanticsBridge.BehavioralStructural.interpret, SemanticsBridge.Structural.interpret,
        SemanticsBridge.Structural.reference_target] using target
    simp only [referenceFacts, target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with member | rfl | rfl
    · cases ci : integerDeclaration v c with
      | false => simp only [ci, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at member
      | true =>
        simp only [ci, ↓reduceIte, List.mem_singleton] at member
        subst fact
        exact empty (Or.inr ((integerDeclaration_eq v p primitive c).mp ci ▸ target))
    · apply (Mixed.binary_subset rep.atoms.injective
        (rep.declaredDeref_completed_of_object_typing p primitive w positive small [] t fits typed d)
        (Mixed.binary_product (head_term v d) (head_term v c)
          (rep.bounded_head_completed p primitive shape ordinary w positive small [] t d)
          (rep.bounded_head_completed p primitive shape ordinary w positive small [] t c))).mpr
      intro x y h
      obtain ⟨hx, c', target', hy⟩ := valid.typed.2 d x y h
      have eq : c' = c := Option.some.inj (target'.symm.trans sourceTarget)
      subst c'
      have inside : x ∈ observedDomain w ∧ y ∈ observedDomain w := by
        cases x with
        | inr z => exact h.elim
        | inl x =>
          refine ⟨trivial, ?_⟩
          cases y with
          | inl y => trivial
          | inr z => exact h.2.2.2 ▸ fits x
      exact ⟨⟨hx, inside.1⟩, hy, inside.2⟩
    · rw [Mixed.all_unary_complete (.mult _ _) (rep.bounded_head_completed p primitive shape ordinary w positive small [] t d)]
      intro x hx
      apply Mixed.unary_one_of_unique (Mixed.unary_image rep.atoms.injective (.var 0)
        (declaredDeref_term v d) (Mixed.unary_singleton (f := rep.atoms) x)
        (rep.declaredDeref_completed_of_object_typing p primitive w positive small [rep.atoms x] t fits typed d))
      simpa only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left, Clafer.Behavioral.Trace.raw] using
        valid.references d c sourceTarget x hx.1

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem coherentFacts_complete (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (shape : PrimitiveShape v)
    (ordinary : ∀ x : Fin o, integerDeclaration v source.objects.identities.directType[x] = false)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (valid : Clafer.Behavioral.Structural.StateValid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source) t) :
    ∀ fact ∈ coherentFacts v, fact.Holds (schema v) w target.unfold [] t := by
  intro fact member
  simp only [coherentFacts, List.mem_singleton] at member
  subst fact
  rw [Mixed.all_unary_complete (.mult _ _) (Mixed.of_objects_unary (labels := rep.labels) (rep.objects_meaning w [] t))]
  intro x hx
  let refs := ((List.finRange k).map (declaredDeref v)).foldl Rel.union (.empty .binary)
  have terms : refs.Term := union_term _ (by
    intro r hr
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
    exact declaredDeref_term v d) _ (.empty _)
  apply Mixed.unary_lone (Mixed.unary_image rep.atoms.injective (.var 0) terms
    (Mixed.unary_singleton (f := rep.atoms) x)
    (rep.allDeref_completed_of_object_typing p primitive w positive small [rep.atoms x] t fits
      (object_typing_of_valid p primitive shape ordinary t valid)))
  rintro y ⟨z, hz, d, hy⟩ q ⟨a, ha, c, hq⟩
  have hz : z = x := hz
  have ha : a = x := ha
  subst z a
  exact valid.coherent d c x y q hy hq

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
