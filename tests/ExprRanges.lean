module

public import tests.Expr
public import ClaferCompiler.Correctness.ExprIntermediateRanges

@[expose] public section
namespace ClaferCompiler.Tests.ExpressionRanges
open IR.Expr SemanticsBridge.Expr Correctness.Expressions
open ClaferCompiler.Tests.Expressions

/-! Concrete witnesses use the executable analyzer and independent meanings.
These do not assert source-to-Alloy or attachment preservation.
[utest->req~compiler-arithmetic~1] -/

theorem fits_observation : observed.withinBounds s bounds = true := by decide

theorem recorded_env : RecordedEnvironment observed env := by
  refine ⟨by simp [env, atomSet, observed, s, Clafer.Constraints.Environment.closed], ?_⟩
  intro x v
  exact (Clafer.Constraints.Var.closed.false v).elim

/-- A reusable fixture constructor retains the real type/observation and analysis
proofs; the success check below also exercises the public admission function. -/
def boundedTerm (t : Ty 3) (e : Term 3 3) (est : Estimate)
    (ht : e.Typed s [] t) (ho : e.Observed s) (ha : analyze s bounds e = .ok est) :
    Admitted s bounds [] t := ⟨⟨e, ht, ho⟩, est, by decide, ha⟩

def extracted : Admitted s bounds [] .integer :=
  boundedTerm .integer (.integerOf 2 values) (.number ⟨-4, 7⟩) (by decide) (by decide) (by rfl)

theorem extraction_admitted : (validateBounds s bounds [] .integer (.integerOf 2 values)).isOk = true := by decide

theorem extraction_range : Interval.Contains ⟨-4, 7⟩ 3 := by
  have h := admitted_sound extracted observed_valid fits_observation env recorded_env
  exact h.2 ⟨3⟩ integer_extraction

def minus : Admitted s bounds [] .integer :=
  boundedTerm .integer (.arithmetic .subtract (.integer 2) (.integerOf 2 values))
    (.number ⟨-5, 6⟩) (by decide) (by decide) (by rfl)

theorem subtraction_value : denote minus.checked model env = some ⟨-1⟩ := by
  change Clafer.Constraints.lift₂ (fun a b : ULift Int => (⟨a.down - b.down⟩ : ULift Int))
    (some ⟨2⟩) (meaning .integer (.integerOf 2 values) (by decide)) = _
  rw [integer_extraction]
  rfl

theorem subtraction_range : Interval.Contains ⟨-5, 6⟩ (-1) :=
  (admitted_sound minus observed_valid fits_observation env recorded_env).2 ⟨-1⟩ subtraction_value

def countedJoin : Admitted s bounds [] .integer :=
  boundedTerm .integer (.cardinality (.relation 0 2) (.join 0 1 2 (.map 0) (.map 1)))
    (.number ⟨0, 4⟩) (by decide) (by decide) (by rfl)

theorem join_count_range : EstimateSound s bounds.width .integer countedJoin.estimate
    (denote countedJoin.checked model env) :=
  admitted_sound countedJoin observed_valid fits_observation env recorded_env

theorem join_count_is_one : denote countedJoin.checked model env = some ⟨1⟩ := by
  have hj : Clafer.Constraints.relationalJoin (observedRelation observed.links[0])
      (observedRelation observed.links[1]) = {(Atom.object 0, Atom.integer 3)} := by
    ext p
    simp [Clafer.Constraints.relationalJoin, observedRelation, observed, Prod.ext_iff]
    aesop
  change (Clafer.Constraints.lift₂ Clafer.Constraints.relationalJoin
    (some (Clafer.Constraints.ambientRelation (model.model.map ((support s).arrow 0))))
    (some (Clafer.Constraints.ambientRelation (model.model.map ((support s).arrow 1))))).bind
      Clafer.Constraints.finiteCard = _
  simp only [model, extend_map, Clafer.Constraints.lift₂, Option.bind_some, Option.map_some]
  simp [Clafer.Constraints.finiteCard]
  exact ⟨hj.symm ▸ Set.finite_singleton _, _, _, hj⟩

def undefinedNumber : Admitted s bounds [] .integer :=
  boundedTerm .integer (.integerOf 2 emptyValues) (.number ⟨-4, 7⟩)
    (by decide) (by decide) (by rfl)

theorem range_does_not_establish_definedness :
    EstimateSound s bounds.width .integer undefinedNumber.estimate
      (denote undefinedNumber.checked model env) ∧
      denote undefinedNumber.checked model env = none :=
  ⟨admitted_sound undefinedNumber observed_valid fits_observation env recorded_env, empty_extraction⟩

def integerLocal : Local 3 := ⟨9, "i", 2⟩
def quantified : Term 3 3 := .all integerLocal values
  (.and (.boolean false) (.less (.arithmetic .add (.integerOf 2 (.var 0)) (.integer 1)) (.integer 8)))
def quantifiedAdmitted : Admitted s bounds [] .boolean :=
  boundedTerm .boolean quantified .truth (by decide) (by decide) (by rfl)

theorem quantified_all_intermediates :
    AllNumbersFit bounds.width model
      (interpret s quantified.raw quantifiedAdmitted.checked.typed) env :=
  admitted_all_numbers_fit quantifiedAdmitted observed_valid fits_observation env recorded_env

theorem executable_environment_discharges :
    AllNumbersFit bounds.width model
      (interpret s quantified.raw quantifiedAdmitted.checked.typed)
      (environment s [] ⟨.object 0, []⟩) :=
  (bounded_environment_sound quantifiedAdmitted observed_valid ⟨.object 0, []⟩ (by decide)).2

/-- The actual integer binder is recorded even though its full source class
contains all integers. A false sibling does not remove the numeric obligation. -/
theorem quantified_body_intermediate : (signedRange bounds.width).Contains 4 := by
  have h := quantified_all_intermediates
  change ∀ S, meaning (.collection (.objects 2)) values (by decide) = some S →
    ∀ x ∈ S, True ∧
      (AllNumbersFit bounds.width model
        (.arithmetic .add (.integerOf (by decide) (.var .here)) (.integer 1))
        (env.push (binder s integerLocal) x) ∧ (signedRange bounds.width).Contains 8) at h
  have hi := (h {Atom.integer 3} values_meaning (.integer 3) (Set.mem_singleton _)).2.1.2.2
  apply hi ⟨4⟩
  change ((integers.extract {Atom.integer 3}).map ULift.up).bind
    (fun x => some (⟨x.down + 1⟩ : ULift Int)) = some ⟨4⟩
  rw [show integers.extract {Atom.integer 3} = some 3 from integers.extract_encoded 3]
  rfl

/-- No truncation of the ambient integer model occurs in the public theorem. -/
theorem extension_range
    (full : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hfull : ExtendsObservation s observed observed_valid full) :
    EstimateSound s bounds.width .integer extracted.estimate (denote extracted.checked full env) :=
  admitted_extension_sound extracted observed_valid fits_observation full hfull env recorded_env

theorem source_integer_fits_target : Backend.Alloy.boundedInt bounds.width 3 = some 3 :=
  admitted_integer_target extracted observed_valid fits_observation model
    (extend_realizes observed_valid) env recorded_env integer_extraction

theorem unsafe_intermediate_rejected :
    (validateBounds s bounds [] .integer
      (.arithmetic .subtract (.arithmetic .add (.integer 15) (.integer 1)) (.integer 1))).isOk = false := by decide

theorem unrecorded_integer_rejected :
    Environment.valid s observed [integerLocal] ⟨.object 0, [.integer 100]⟩ = true ∧
    Environment.bounded s bounds observed [integerLocal] ⟨.object 0, [.integer 100]⟩ = false := by decide

end ClaferCompiler.Tests.ExpressionRanges
