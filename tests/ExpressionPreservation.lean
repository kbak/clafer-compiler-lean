module

public import tests.ExprRanges
public import ClaferCompiler.Correctness.ExpressionScalarFacts

@[expose] public section
namespace ClaferCompiler.Tests.ExpressionPreservation
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open Correctness.ExpressionRelations Correctness.ExpressionConstruction Correctness.ExpressionMeaning
open ClaferCompiler.Tests.Expressions ClaferCompiler.Tests.ExpressionRanges

/-! Concrete representation and preservation witnesses. The source uses the
full mathematical integer binding, with a genuinely nonempty owner/domain.
[utest->req~compiler-expression-encoding~1] -/

def atomCode : Atom → Nat
  | .object n => 4 * n
  | .integer (.ofNat n) => 4 * n + 1
  | .integer (.negSucc n) => 4 * n + 3

theorem atomCode_injective : Function.Injective atomCode := by
  intro a b h
  cases a with
  | object a =>
    cases b with
    | object b => simp only [atomCode] at h; congr 1; omega
    | integer b => cases b <;> simp only [atomCode] at h <;> omega
  | integer a =>
    cases b with
    | object b => cases a <;> simp only [atomCode] at h <;> omega
    | integer b => cases a <;> cases b <;> simp_all [atomCode] <;> omega

def layout : Layout 3 3 := ⟨#v[.sig 0, .sig 1, .sig 2], #v[.field 0, .field 1, .field 1], #v[0, 1, 2]⟩
def candidate : Instance := ⟨[[0], [4, 8], [13]], [[[0, 4], [0, 8]], [[4, 13], [8, 13]]],
  [[], [], [(13, 3)]]⟩

theorem layout_built : LayoutBuilt layout := by
  constructor <;> intro x <;> fin_cases x <;> first | exact .sig _ | exact .field _

theorem leaves : LayoutRep s layout observed candidate atomCode := by
  refine ⟨atomCode_injective, ?_, ?_, ?_, ?_⟩
  · intro x env
    fin_cases x <;> simp [Unary, layout, candidate,
      atomSet, observed, atomCode]
  · intro e env
    fin_cases e <;> simp [Binary, layout, candidate,
      observedRelation, observed, or_and_right, exists_or, atomCode]
  · intro x hx env
    fin_cases x <;> simp_all [s]
    simp [Unary, layout, candidate,
      atomSet, observed, atomCode]
  · intro x hx row
    fin_cases x <;> simp_all [s]
    simp [layout, candidate, observed, atomCode]

def equation : Admitted s bounds [] .boolean := boundedTerm .boolean
  (.equal .integer minus.checked.term (.integer (-1))) .truth (by decide) (by decide) (by rfl)

theorem closed_environment : EnvironmentRep s (Γ := []) atomCode env [0] := by
  refine ⟨rfl, ?_⟩
  intro x v
  exact (Clafer.Constraints.Var.closed.false v).elim

theorem constructor_agreement : Agrees s atomCode bounds.width candidate [0]
    (denote equation.checked model env) (encode layout equation) :=
  admitted_agrees equation observed_valid fits_observation leaves layout_built env recorded_env [0] closed_environment

theorem source_equation_true : denote equation.checked model env = some ⟨True⟩ := by
  change Clafer.Constraints.lift₂ (fun a b : ULift Int => (⟨a = b⟩ : ULift Prop))
    (denote minus.checked model env) (some ⟨-1⟩) = _
  rw [subtraction_value]
  simp [Clafer.Constraints.lift₂]

theorem compiled_equation_true : (encode layout equation).holds.eval bounds.width candidate [0] = some true :=
  (agrees_holds constructor_agreement
    (encodeAt_built s layout bounds layout_built _ _ _ equation.checked.typed)).mpr source_equation_true

theorem actual_target_evaluation : (encode layout equation).holds.eval 5 candidate [0] = some true := by decide

def undefinedNegation : Admitted s bounds [] .boolean := boundedTerm .boolean
  (.not (.equal .integer undefinedNumber.checked.term (.integer 0))) .truth
  (by decide) (by decide) (by rfl)

theorem undefined_negation_source : denote undefinedNegation.checked model env = none := by
  change (Clafer.Constraints.lift₂ (fun a b : ULift Int => (⟨a = b⟩ : ULift Prop))
    (denote undefinedNumber.checked model env) (some ⟨0⟩)).map (fun p : ULift Prop => (⟨¬p.down⟩ : ULift Prop)) = _
  rw [range_does_not_establish_definedness.2]
  rfl

theorem undefined_negation_rejected : (encode layout undefinedNegation).holds.eval 5 candidate [0] ≠ some true := by
  have h := admitted_agrees undefinedNegation observed_valid fits_observation leaves layout_built
    env recorded_env [0] closed_environment
  change (encode layout undefinedNegation).holds.eval bounds.width candidate [0] ≠ some true
  intro ht
  have hs := (agrees_holds h
    (encodeAt_built s layout bounds layout_built _ _ _ undefinedNegation.checked.typed)).mp ht
  rw [undefined_negation_source] at hs
  contradiction

theorem attached_equation : (attach (.sig 0) (encode layout equation)).eval 5 candidate [] = some true ↔
    ∀ owner ∈ atomSet observed.objects[s.context],
      denote equation.checked model (Clafer.Constraints.Environment.closed owner) = some ⟨True⟩ :=
  attachment_iff equation observed_valid fits_observation leaves layout_built model
    (extend_realizes observed_valid) (.sig 0) (leaves.extents s.context [])

end ClaferCompiler.Tests.ExpressionPreservation
