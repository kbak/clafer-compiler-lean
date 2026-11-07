module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureMixed

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace Mixed

theorem of_objects_unary {labels : Fin o ↪ Nat} {A : Set (Fin o)} {rows : Relation}
    (h : Relations.Unary labels A rows) :
    Unary (completionAtom labels) (Sum.inl '' A) rows := by
  intro row
  rw [h row]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨Sum.inl x, ⟨x, hx, rfl⟩, he⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, he⟩
    exact ⟨x, hx, he⟩

theorem unary_congr {f : U → Atom} {A B : Set U} {rows : Relation}
    (h : Unary f A rows) (he : ∀ x, x ∈ A ↔ x ∈ B) : Unary f B rows := by
  intro row
  rw [h row]
  simp only [he]

end Mixed

theorem declaredDeref_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) :
    (declaredDeref v d).Term := by
  unfold declaredDeref
  split
  · split
    · exact .inter (.values 0) (.product (head_term v d) .ints)
    · exact .field _
  · exact .field _

theorem deref_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) :
    (deref v d).Term := by
  unfold deref
  split
  · exact .empty _
  · exact .inter (declaredDeref_term v _) (.product (head_term v d) (.union (.sig _) .ints))

theorem owner_ordinary (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (d owner : Fin k)
    (lookup : v.analysis.referenceOwners[d] = some owner) : integerDeclaration v d = false := by
  apply Bool.eq_false_iff.mpr
  intro hd
  have dp := (integerDeclaration_eq v p primitive d).mp hd
  subst d
  have hp := v.checked.2.1.2 p
  have primitiveShape := v.checked.2.2.2.2.2.1 p primitive
  simp only [primitiveShape.2.1, ↓reduceIte, primitiveShape.2.2, Option.bind_none] at hp
  rw [hp] at lookup
  contradiction

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

def labels (rep : TraceRep v source target) : Fin o ↪ Nat :=
  ⟨rep.label, rep.label_injective⟩

def atoms (rep : TraceRep v source target) : Completion o ↪ Atom := completionAtom rep.labels

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem head_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (w : Nat)
    (e : Environment) (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Mixed.Unary rep.atoms
      (((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d)
      ((head v d).eval (schema v) w target.unfold e t) := by
  apply Mixed.unary_congr (Mixed.of_objects_unary (rep.head_source w e t d ordinary))
  intro x
  cases x with
  | inl x => simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right]; rfl
  | inr z =>
    have nonprimitive : d ≠ p := by
      intro eq
      subst d
      have hi := (integerDeclaration_eq v p primitive p).mpr rfl
      rw [ordinary] at hi
      contradiction
    simp only [Set.mem_image, reduceCtorEq, and_false, exists_false,
      completeHead_integer v p primitive, Ne.symm nonprimitive]

theorem ints_completed (rep : TraceRep v source target) (w : Nat) (positive : 0 < w)
    (small : w ≤ 16) (e : Environment) (t : Nat) :
    Mixed.Unary rep.atoms {x | ∃ z, x = Sum.inr z ∧ Backend.Alloy.fitsInt w z = true}
      (Rel.ints.eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (integerAtoms w).map (fun a => [a]) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact ⟨Sum.inr _, ⟨_, rfl, (integerAtoms_fits w positive small _).mp ha⟩, rfl⟩
  · rintro ⟨x, ⟨z, rfl, fits⟩, rfl⟩
    exact ⟨.integer z, (integerAtoms_fits w positive small z).mpr fits, rfl⟩

theorem values_completed (rep : TraceRep v source target) (w : Nat)
    (e : Environment) (t : Nat) :
    Mixed.Binary rep.atoms (fun x y => ∃ a : Fin o,
      x = Sum.inl a ∧ y = Sum.inr (source.valuesAt t)[a])
      ((Rel.values 0).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).values[0]?.getD []).map
    fun r => [Atom.object r.1, Atom.integer r.2]) ↔ _
  simp only [List.mem_map, rep.values]
  constructor
  · rintro ⟨r, ⟨a, rfl⟩, he⟩
    exact ⟨Sum.inl a, Sum.inr (source.valuesAt t)[a], ⟨a, rfl, rfl⟩, he.symm⟩
  · rintro ⟨x, y, ⟨a, rfl, rfl⟩, he⟩
    exact ⟨(rep.label a, (source.valuesAt t)[a]), ⟨a, rfl⟩, he.symm⟩

theorem universe_completed (rep : TraceRep v source target) (w : Nat)
    (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat) :
    Mixed.Unary rep.atoms
      ((Sum.inl '' (Set.univ : Set (Fin o))) ∪
        {x | ∃ z, x = Sum.inr z ∧ Backend.Alloy.fitsInt w z = true})
      ((Rel.union (.sig 0) .ints).eval (schema v) w target.unfold e t) :=
  Mixed.unary_union (.sig 0) .ints (Mixed.of_objects_unary (rep.objects_meaning w e t))
    (rep.ints_completed w positive small e t)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem contains_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer) (w : Nat)
    (e : Environment) (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Mixed.Binary rep.atoms
      (((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d)
      ((contains v d).eval (schema v) w target.unfold e t) := by
  have nonprimitive : p ≠ d := by
    intro eq
    have hi := (integerDeclaration_eq v p primitive d).mpr eq.symm
    rw [ordinary] at hi
    contradiction
  intro row
  rw [rep.contains_source w e t d ordinary row]
  constructor
  · rintro ⟨x, y, h, he⟩
    exact ⟨Sum.inl x, Sum.inl y, (completeContains_objects v p source t d x y).mpr h, he⟩
  · rintro ⟨x, y, h, he⟩
    cases y with
    | inr z => exact (nonprimitive ((completeContains_integer v p primitive source t d x z).mp h).2.2).elim
    | inl y =>
      cases x with
      | inl x => exact ⟨x, y, (completeContains_objects v p source t d x y).mp h, he⟩
      | inr z =>
        have parent := h.1.2.2
        change source.objects.identities.parent[y].map Sum.inl = some (Sum.inr z) at parent
        cases hp : source.objects.identities.parent[y] <;> simp only [hp, Option.map_none,
          Option.map_some, reduceCtorEq, Option.some.injEq] at parent

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Exact declared references on the completed source. Integer observations
have an explicit signed-range premise; the primitive carrier remains infinite. -/
theorem declaredDeref_completed_of_object_typing (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (typed : ∀ d (x y : Fin o), (d, x, y) ∈ (source.objects.at t).references →
      ∃ c, (v.core.structural.get d).reference.target = some c ∧ integerDeclaration v c = false)
    (d : Fin k) :
    Mixed.Binary rep.atoms ((completeTrace v p source).deref t d)
      ((declaredDeref v d).eval (schema v) w target.unfold e t) := by
  by_cases integerTarget : (v.core.structural.get d).reference.target = some p
  · have primitiveBool := (integerDeclaration_eq v p primitive p).mpr rfl
    simp only [declaredDeref, integerTarget, primitiveBool, ↓reduceIte]
    have rows := Mixed.binary_inter rep.atoms.injective (.values 0)
      (.product (head_term v d) .ints) (rep.values_completed w e t)
      (Mixed.binary_product (head_term v d) .ints
        (rep.head_completed p primitive w e t d (reference_ordinary v d p integerTarget))
        (rep.ints_completed w positive small e t))
    apply Mixed.binary_congr rows
    intro x y
    cases x with
    | inr z => simp [completeTrace]
    | inl x =>
      cases y with
      | inl y =>
        have noObject : (d, x, y) ∉ (source.objects.at t).references := by
          intro h
          obtain ⟨c, target, ordinary⟩ := typed d x y h
          have eq : c = p := Option.some.inj (target.symm.trans integerTarget)
          subst c
          rw [primitiveBool] at ordinary
          contradiction
        simp [completeTrace, noObject]
      | inr z =>
        change ((∃ a, Sum.inl x = Sum.inl a ∧ Sum.inr z = Sum.inr (source.valuesAt t)[a]) ∧
          ((_ ∧ _) ∧ ∃ z', Sum.inr z = Sum.inr z' ∧ Backend.Alloy.fitsInt w z' = true)) ↔ _
        simp only [Sum.inl.injEq, Sum.inr.injEq, completeTrace, integerTarget,
          true_and]
        constructor
        · rintro ⟨⟨a, ea, eq⟩, ⟨live, ancestor⟩, _⟩
          subst a
          exact ⟨live, ancestor, eq.symm⟩
        · rintro ⟨live, ancestor, eq⟩
          exact ⟨⟨x, rfl, eq.symm⟩, ⟨live, ancestor⟩, ⟨z, rfl, eq ▸ fits x⟩⟩
  · have targetEq : declaredDeref v d = rawDeref d := by
      unfold declaredDeref
      cases hr : (v.core.structural.get d).reference.target with
      | none => rfl
      | some c =>
        have ordinary : integerDeclaration v c = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          exact integerTarget ((integerDeclaration_eq v p primitive c).mp h ▸ hr)
        simp [ordinary]
    rw [targetEq]
    intro row
    rw [rep.rawDeref_meaning w e t d row]
    constructor
    · rintro ⟨x, y, h, he⟩
      exact ⟨Sum.inl x, Sum.inl y, h, he⟩
    · rintro ⟨x, y, h, he⟩
      cases x with
      | inr z => exact h.elim
      | inl x =>
        cases y with
        | inl y => exact ⟨x, y, h, he⟩
        | inr z => exact (integerTarget h.1).elim

theorem declaredDeref_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) (d : Fin k) :
    Mixed.Binary rep.atoms ((completeTrace v p source).deref t d)
      ((declaredDeref v d).eval (schema v) w target.unfold e t) :=
  rep.declaredDeref_completed_of_object_typing p primitive w positive small e t fits
    (fun d x y h => by
      obtain ⟨c, hc, hi, _, _⟩ := rep.object_reference_typed w t facts d x y h
      exact ⟨c, hc, hi⟩) d

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Nearest-owner views preserve the same object/scalar link on each inherited
head. The target finite Int extent is used only to bound observed values. -/
theorem deref_completed_of_object_typing (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (typed : ∀ d (x y : Fin o), (d, x, y) ∈ (source.objects.at t).references →
      ∃ c, (v.core.structural.get d).reference.target = some c ∧ integerDeclaration v c = false)
    (d : Fin k) :
    Mixed.Binary rep.atoms
      (Clafer.Behavioral.InheritedReference.deref
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d)
      ((deref v d).eval (schema v) w target.unfold e t) := by
  cases lookup : v.analysis.referenceOwners[d] with
  | none =>
    simp only [deref, lookup]
    intro row
    change row ∈ [] ↔ _
    constructor
    · exact fun h => (List.not_mem_nil h).elim
    · rintro ⟨x, y, ⟨owner, howner, _, _⟩, _⟩
      have found := SemanticsBridge.BehavioralStructural.owner_complete v.checked.2.1 howner
      rw [lookup] at found
      contradiction
  | some owner =>
    have howner := SemanticsBridge.BehavioralStructural.owner_sound
      v.checked.2.1 v.checked.1.2.2.2.2.1 lookup
    have ordinary := owner_ordinary v p primitive d owner lookup
    simp only [deref, lookup]
    have rows := Mixed.binary_inter rep.atoms.injective (declaredDeref_term v owner)
      (.product (head_term v d) (.union (.sig 0) .ints))
      (rep.declaredDeref_completed_of_object_typing p primitive w positive small e t fits typed owner)
      (Mixed.binary_product (head_term v d) (.union (.sig 0) .ints)
        (rep.head_completed p primitive w e t d ordinary)
        (rep.universe_completed w positive small e t))
    apply Mixed.binary_congr rows
    intro x y
    rw [Clafer.Behavioral.InheritedReference.deref_owner howner]
    constructor
    · rintro ⟨ref, head, _⟩
      exact ⟨head, ref⟩
    · rintro ⟨head, ref⟩
      refine ⟨ref, head, ?_⟩
      cases y with
      | inl y => exact Or.inl ⟨y, Set.mem_univ _, rfl⟩
      | inr z =>
        cases x with
        | inr value => exact (completeDeref_integer_source v p source t owner value (Sum.inr z) ref).elim
        | inl x => exact Or.inr ⟨z, rfl, ref.2.2.2 ▸ fits x⟩

theorem deref_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) (d : Fin k) :
    Mixed.Binary rep.atoms
      (Clafer.Behavioral.InheritedReference.deref
        (SemanticsBridge.BehavioralStructural.interpret v.core).family
        ((completeTrace v p source).raw
          (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t) d)
      ((deref v d).eval (schema v) w target.unfold e t) :=
  rep.deref_completed_of_object_typing p primitive w positive small e t fits
    (fun d x y h => by
      obtain ⟨c, hc, hi, _, _⟩ := rep.object_reference_typed w t facts d x y h
      exact ⟨c, hc, hi⟩) d

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
