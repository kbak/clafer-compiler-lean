module

public import ClaferCompiler.Correctness.Behavioral.Full.CompilerCorrectness
public import Clafer.Behavioral.AbsentReference

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-trace-representation~1]
/-- The scalar table is total storage. Changing only values at absent identities
does not change the completed source trace, including inherited observations.
This does not equate target tables or erase them from checked decoding. -/
theorem completeTrace_absent_values (v : IR.BehavioralStructural.Validated k) (p : Fin k)
    (objects : IR.Behavioral.Lasso k o steps)
    (a b : Vector (Vector Int o) steps)
    (same : ∀ (t : Nat) (x : Fin o), (objects.at t).live[x] = true →
      (ObservedLasso.valuesAt ⟨objects, a⟩ t)[x] =
        (ObservedLasso.valuesAt ⟨objects, b⟩ t)[x]) :
    completeTrace v p ⟨objects, a⟩ = completeTrace v p ⟨objects, b⟩ := by
  have hd : ∀ t d x y,
      (completeTrace v p ⟨objects, a⟩).deref t d x y ↔
        (completeTrace v p ⟨objects, b⟩).deref t d x y := by
    intro t d x y
    cases x with
    | inr z => rfl
    | inl x =>
      cases y with
      | inl y => rfl
      | inr z =>
        change (_ ∧ (objects.at t).live[x] = true ∧ _ ∧ _ = z) ↔
          (_ ∧ (objects.at t).live[x] = true ∧ _ ∧ _ = z)
        constructor <;> rintro ⟨target, live, ancestor, value⟩
        · exact ⟨target, live, ancestor, (same t x live).symm.trans value⟩
        · exact ⟨target, live, ancestor, (same t x live).trans value⟩
  have he := funext fun t => funext fun d => funext fun x => funext fun y => propext (hd t d x y)
  exact congrArg (fun refs => (⟨completeIdentities p ⟨objects, a⟩,
    (completeTrace v p ⟨objects, a⟩).live, refs⟩ :
      Clafer.Behavioral.Trace (Fin k) (Completion o))) he

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-behavioral-encoding~1]
/-- Generated state facts reject absent-head object tuples before any projection.
Successful decoding alone deliberately makes no source-validity claim. -/
theorem absent_object_row (rep : TraceRep v source target) (w t : Nat)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (x y : Fin o) (absent : (source.objects.at t).live[x] = false) :
    (d, x, y) ∉ (source.objects.at t).references := by
  intro row
  obtain ⟨_, _, _, head, _⟩ := rep.object_reference_typed w t facts d x y row
  have live : (source.objects.at t).live[x] = true := head.1
  rw [absent] at live
  contradiction

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The actual target dereference image is empty for an absent occurrence,
including inherited/refined views and scalar references. Frozen captures retain
the occurrence identity, not its old reference value. -/
theorem absent_deref (rep : TraceRep v source target) (p : Fin k)
    (primitive : (v.core.structural.get p).origin = .integer)
    (w : Nat) (positive : 0 < w) (small : w ≤ 16) (e : Environment) (t : Nat)
    (fits : ∀ x : Fin o, Backend.Alloy.fitsInt w (source.valuesAt t)[x] = true)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (d : Fin k) (x : Fin o) (absent : (source.objects.at t).live[x] = false) (y : Atom) :
    [rep.atoms (.inl x), y] ∉ (deref v d).eval (schema v) w target.unfold e t := by
  intro row
  obtain ⟨a, b, link, eq⟩ :=
    (rep.deref_completed p primitive w positive small e t fits facts d _).mp row
  have same : Sum.inl x = a := rep.atoms.injective (List.cons.inj eq).1
  subst a
  have empty := Clafer.Behavioral.AbsentReference.inherited_empty
    (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore
    (completeTrace v p source) (t := t) (x := Sum.inl x)
    (by simp [absent]) d
  exact (empty ▸ link : b ∈ (∅ : Set (Completion o)))

end TraceRep

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Successful compilation and target satisfaction supply the decoder result and
the typedness needed by the upstream absence theorem. No source validity or
decoder success is assumed. The source formula proofs continue to preserve both
polarities and partial domains through the existing `compiled_sound` theorem. -/
theorem compiled_absent_references (r : Request k) (b : Bounds) (fuel : Nat) (c : Compiled)
    (success : compile r b fuel = .ok c)
    (p : Fin k) (primitive : (r.model.structural.core.structural.get p).origin = .integer)
    (target : Lasso) (sat : Satisfies c.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode r.model.structural target = .ok decoded ∧
      SourceResult r completeIntegers (completeTrace r.model.structural p decoded.2.2) ∧
      ∀ t x, x ∉ (completeTrace r.model.structural p decoded.2.2).live t →
        ∀ d, {y | (completeTrace r.model.structural p decoded.2.2).deref t d x y} = ∅ := by
  obtain ⟨decoded, read, result⟩ := compiled_sound r b fuel c success p primitive target sat
  obtain ⟨other, otherRead, valid⟩ := compiled_structural_sound r b fuel c success p primitive target sat
  have eq : other = decoded := Except.ok.inj (otherRead.symm.trans read)
  subst other
  refine ⟨decoded, read, result, ?_⟩
  intro t x absent d
  exact Clafer.Behavioral.AbsentReference.raw_empty
    (SemanticsBridge.BehavioralStructural.interpret r.model.structural.core).toEffectiveCore
    (completeTrace r.model.structural p decoded.2.2) (valid.states t).typed absent d

end ClaferCompiler.Correctness.Behavioral.Full
