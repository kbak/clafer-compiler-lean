module

public import ClaferCompiler.Correctness.Behavioral.Full.Structure

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem declaration_mem (v : IR.BehavioralStructural.Validated k) (d : Fin k)
    (f : Formula) (h : f ∈ declarationFacts v d) : f ∈ stateFacts v := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨d, List.mem_finRange _, h⟩

theorem reference_mem (v : IR.BehavioralStructural.Validated k) (d : Fin k)
    (f : Formula) (h : f ∈ referenceFacts v d) : f ∈ stateFacts v :=
  declaration_mem v d f (List.mem_append_left _ (List.mem_append_left _ h))

theorem reference_ordinary (v : IR.BehavioralStructural.Validated k) (d c : Fin k)
    (reference : (v.core.structural.get d).reference.target = some c) :
    integerDeclaration v d = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have primitive : (v.core.structural.get d).origin = .integer := by simpa [integerDeclaration] using h
  have basic := (v.checked.2.2.2.2.2.1 d primitive).2.1
  rw [basic] at reference
  cases reference

theorem unary_one_sound {U : Type} {f : U → Nat} (injective : Function.Injective f)
    {A : Set U} {r : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
    (meaning : Relations.Unary f A (r.eval s w τ e t))
    (one : (Formula.mult .one r).Holds s w τ e t) : ∃! x, x ∈ A := by
  have length : (r.eval s w τ e t).eraseDups.length = 1 := by
    simpa [Formula.Holds, Formula.mult, Formula.fold, FormulaAlgebra.step,
      formulaAlgebra, Backend.Alloy.Multiplicity.holds] using one
  obtain ⟨row, rows⟩ := List.length_eq_one_iff.mp length
  have member : row ∈ r.eval s w τ e t := List.mem_eraseDups.mp (by simp [rows])
  obtain ⟨x, hx, he⟩ := (meaning row).mp member
  refine ⟨x, hx, ?_⟩
  intro y hy
  have member : [.object (f y)] ∈ (r.eval s w τ e t).eraseDups :=
    List.mem_eraseDups.mpr ((meaning _).mpr ⟨y, hy, rfl⟩)
  have eq : [Atom.object (f y)] = [Atom.object (f x)] := by simpa [rows, he] using member
  exact injective (by simpa using eq)

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every raw object row is typed by its declared target. In particular an
integer reference cannot smuggle an object row past scalar projection. -/
theorem object_reference_typed (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (x y : Fin o) (h : (d, x, y) ∈ (source.objects.at t).references) :
    ∃ c, (v.core.structural.get d).reference.target = some c ∧
      integerDeclaration v c = false ∧
      x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d ∧
      y ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head c := by
  have row := (rep.rawDeref_meaning w [] t d _).mpr ⟨x, y, h, rfl⟩
  cases hr : (v.core.structural.get d).reference.target with
  | none =>
    have empty := facts (.equal (rawDeref d) (.empty .binary))
      (reference_mem v d _ (by simp [referenceFacts, hr]))
    exact (List.not_mem_nil ((empty _).mp row)).elim
  | some c =>
    cases hc : integerDeclaration v c with
    | true =>
      have empty := facts (.equal (rawDeref d) (.empty .binary))
        (reference_mem v d _ (by simp [referenceFacts, hr, hc]))
      exact (List.not_mem_nil ((empty _).mp row)).elim
    | false =>
      have typed := facts (.subset (rawDeref d) (.product (head v d) (head v c)))
        (reference_mem v d _ (by simp [referenceFacts, declaredDeref, hr, hc]))
      have product := Relations.binary_product (head_term v d) (head_term v c)
        (rep.head_source w [] t d (reference_ordinary v d c hr)) (rep.head_source w [] t c hc)
      obtain ⟨a, b, hab, he⟩ := (product _).mp (typed _ row)
      have hx : x = a := rep.label_injective (by simpa using (List.cons.inj he).1)
      have hy : y = b := rep.label_injective (by simpa using (List.cons.inj (List.cons.inj he).2).1)
      exact ⟨c, rfl, hc, hx ▸ hab.1, hy ▸ hab.2⟩

theorem object_references (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d c : Fin k) (hr : (v.core.structural.get d).reference.target = some c)
    (ordinary : integerDeclaration v c = false) (x : Fin o)
    (hx : x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d) :
    ∃! y, (d, x, y) ∈ (source.objects.at t).references := by
  have generated := facts (.all (head v d) (.mult .one (.join (.var 0) (rawDeref d))))
    (reference_mem v d _ (by simp [referenceFacts, declaredDeref, hr, ordinary]))
  have one : (Formula.mult .one (.join (.var 0) (rawDeref d))).Holds (schema v) w
      target.unfold [.object (rep.label x)] t := by
    change ∀ atom, [atom] ∈ (head v d).eval (schema v) w target.unfold [] t → _ at generated
    exact generated _ ((rep.head_source w [] t d (reference_ordinary v d c hr) _).mpr ⟨x, hx, rfl⟩)
  have image := Relations.unary_image rep.label_injective (.var 0) (.field _)
    (Relations.unary_singleton (f := rep.label) x)
    (rep.rawDeref_meaning w [.object (rep.label x)] t d)
  simpa only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left] using
    unary_one_sound rep.label_injective image one

theorem object_parents (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d c : Fin k) (hp : (v.core.structural.get d).parent = some c)
    (ordinary : integerDeclaration v d = false) (x : Fin o)
    (hx : x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d) :
    ∃! p, ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d p x := by
  have generated := facts (.all (head v d) (.mult .one (.join (.var 0) (.transpose (contains v d)))))
    (declaration_mem v d _ (by simp [declarationFacts, hp]))
  have one : (Formula.mult .one (.join (.var 0) (.transpose (contains v d)))).Holds (schema v) w
      target.unfold [.object (rep.label x)] t := by
    change ∀ atom, [atom] ∈ (head v d).eval (schema v) w target.unfold [] t → _ at generated
    exact generated _ ((rep.head_source w [] t d ordinary _).mpr ⟨x, hx, rfl⟩)
  have inverse := Relations.binary_transpose (contains_term v d)
    (rep.contains_source w [.object (rep.label x)] t d ordinary)
  have image := Relations.unary_image rep.label_injective (.var 0) (.transpose (contains_term v d))
    (Relations.unary_singleton (f := rep.label) x) inverse
  simpa only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left] using
    unary_one_sound rep.label_injective image one

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
