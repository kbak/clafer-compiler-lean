module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureObservations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem lone_rows {r : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
    (h : (Formula.mult .lone r).Holds s w τ e t) {a b : List Atom}
    (ha : a ∈ r.eval s w τ e t) (hb : b ∈ r.eval s w τ e t) : a = b := by
  have length : (r.eval s w τ e t).eraseDups.length ≤ 1 := by
    simpa [Formula.Holds, Formula.mult, Formula.fold, FormulaAlgebra.step,
      formulaAlgebra, Backend.Alloy.Multiplicity.holds] using h
  have ha := List.mem_eraseDups.mpr ha
  have hb := List.mem_eraseDups.mpr hb
  cases he : (r.eval s w τ e t).eraseDups with
  | nil => simp only [he, List.not_mem_nil] at ha
  | cons c cs =>
    have empty : cs = [] := List.length_eq_zero_iff.mp (by simp only [he, List.length_cons] at length; omega)
    rw [he, empty, List.mem_singleton] at ha hb
    exact ha.trans hb.symm

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

theorem allDeref_completed_of_object_typing (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (typed : ∀ d (x y : Fin o), (d, x, y) ∈ (source.objects.at t).references →
      ∃ c, (v.core.structural.get d).reference.target = some c ∧ integerDeclaration v c = false) :
    Mixed.Binary rep.atoms (fun x y => ∃ d, (completeTrace v p source).deref t d x y)
      ((((List.finRange k).map (declaredDeref v)).foldl Rel.union (.empty .binary)).eval
        (schema v) w target.unfold e t) := by
  intro row
  rw [union_rows _ (by
    intro r hr
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
    exact declaredDeref_term v d) _ (.empty _)]
  have empty : (Rel.empty .binary).eval (schema v) w target.unfold e t = [] := rfl
  rw [empty]
  simp only [List.not_mem_nil, false_or, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨r, ⟨d, rfl⟩, hr⟩
    obtain ⟨x, y, h, he⟩ := (rep.declaredDeref_completed_of_object_typing p primitive w positive small e t fits typed d row).mp hr
    exact ⟨x, y, ⟨d, h⟩, he⟩
  · rintro ⟨x, y, ⟨d, h⟩, he⟩
    exact ⟨declaredDeref v d, ⟨d, rfl⟩,
      (rep.declaredDeref_completed_of_object_typing p primitive w positive small e t fits typed d row).mpr ⟨x, y, h, he⟩⟩

theorem allDeref_completed (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    Mixed.Binary rep.atoms (fun x y => ∃ d, (completeTrace v p source).deref t d x y)
      ((((List.finRange k).map (declaredDeref v)).foldl Rel.union (.empty .binary)).eval
        (schema v) w target.unfold e t) :=
  rep.allDeref_completed_of_object_typing p primitive w positive small e t fits
    (fun d x y h => by
      obtain ⟨c, hc, hi, _, _⟩ := rep.object_reference_typed w t facts d x y h
      exact ⟨c, hc, hi⟩)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- One emitted mixed union enforces reference coherence across every declared
owner, including object/integer refinements of the same occurrence. -/
theorem coherent (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    Clafer.Behavioral.Structural.ReferenceCoherent (completeTrace v p source) t := by
  intro d e x y z hy hz
  cases x with
  | inr value => exact (completeDeref_integer_source v p source t d value y hy).elim
  | inl x =>
    let refs := ((List.finRange k).map (declaredDeref v)).foldl Rel.union (.empty .binary)
    have refTerm : refs.Term := union_term _ (by
      intro r hr
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
      exact declaredDeref_term v d) _ (.empty _)
    have generated := facts (.all (.sig 0) (.mult .lone (.join (.var 0) refs)))
      (by simp [stateFacts, coherentFacts, refs])
    change ∀ atom, [atom] ∈ (Rel.sig 0).eval (schema v) w target.unfold [] t → _ at generated
    have body := generated (.object (rep.label x))
      ((rep.objects_meaning w [] t _).mpr ⟨x, Set.mem_univ _, rfl⟩)
    have image := Mixed.unary_image rep.atoms.injective (.var 0) refTerm
      (Mixed.unary_singleton (f := rep.atoms) (Sum.inl x))
      (rep.allDeref_completed p primitive w positive small [rep.atoms (Sum.inl x)] t fits facts)
    have hey := (image [rep.atoms y]).mpr ⟨y, ⟨Sum.inl x, rfl, d, hy⟩, rfl⟩
    have hez := (image [rep.atoms z]).mpr ⟨z, ⟨Sum.inl x, rfl, e, hz⟩, rfl⟩
    exact rep.atoms.injective (List.singleton_inj.mp (lone_rows body hey hez))

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
