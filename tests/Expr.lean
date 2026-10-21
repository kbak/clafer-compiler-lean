module

public import tests.ExprNative
public import ClaferCompiler.SemanticsBridge.ExprFinite

@[expose] public section
namespace ClaferCompiler.Tests.Expressions
open IR.Expr SemanticsBridge.Expr
open Clafer.Constraints (ambientRelation relationalImage relationalJoin)

theorem observed_valid : ObservationValid s observed where
  same_id := by
    intro x y he
    have hxy : x = y := by fin_cases x <;> fin_cases y <;> simp_all [s]
    subst y; rfl
  endpoints := by
    intro e l hl
    fin_cases e <;>
      simp [observed, s, fullExtent, atomSet] at hl ⊢ <;>
      rcases hl with rfl | rfl <;> simp [integers, FormalCD.IntegerRealization.domain]
    all_goals exact ⟨3, rfl⟩
  link_ids := by intro e; fin_cases e <;> decide
  repeated := by intro e f ho hk; fin_cases e <;> fin_cases f <;> simp_all [s, observed]
  inclusion_one := by intro e he; fin_cases e <;> cases he
  inclusion_same := by intro e he; fin_cases e <;> cases he

noncomputable abbrev model := extend s observed observed_valid
noncomputable abbrev env : Clafer.Constraints.Environment (support s) Atom [] := .closed (.object 0)

noncomputable abbrev meaning (t : Ty 3) (e : Term 3 3) (h : e.Typed s [] t) :=
  (interpret s e.raw h).denote model env

/-!
[utest->req~compiler-expressions~1]
[utest->req~compiler-arithmetic~1]
-/
theorem heads_meaning : meaning (.collection (.objects 1)) heads (by decide) =
    some ({.object 1, .object 2} : Set Atom) := by
  simp only [meaning, heads, interpret, Clafer.Constraints.Expr.denote,
    Clafer.Constraints.lift₂, Option.bind_some, Option.map_some, model, extend_map]
  congr 1
  ext a
  simp [relationalImage, observedRelation, observed, env, Clafer.Constraints.Environment.closed]
  exact or_congr eq_comm eq_comm

theorem values_meaning : meaning (.collection (.objects 2)) values (by decide) =
    some ({.integer 3} : Set Atom) := by
  change Clafer.Constraints.lift₂ relationalImage (meaning (.collection (.objects 1)) heads (by decide))
    (some (ambientRelation (model.model.map ((support s).arrow 1)))) = some ({Atom.integer 3} : Set Atom)
  rw [heads_meaning]
  simp only [model, extend_map, Clafer.Constraints.lift₂, Option.bind_some, Option.map_some]
  congr 1
  ext a
  simp [relationalImage, observedRelation, observed]

theorem head_count : meaning .integer (.cardinality (.objects 1) heads) (by decide) = some ⟨2⟩ := by
  change (meaning (.collection (.objects 1)) heads (by decide)).bind Clafer.Constraints.finiteCard = _
  rw [heads_meaning]
  simp [Clafer.Constraints.finiteCard]

theorem target_count : meaning .integer (.cardinality (.objects 2) values) (by decide) = some ⟨1⟩ := by
  change (meaning (.collection (.objects 2)) values (by decide)).bind Clafer.Constraints.finiteCard = _
  rw [values_meaning]
  simp [Clafer.Constraints.finiteCard]

theorem integer_extraction : meaning .integer (.integerOf 2 values) (by decide) = some ⟨3⟩ := by
  change (meaning (.collection (.objects 2)) values (by decide)).bind (fun S => (integers.extract S).map ULift.up) = _
  rw [values_meaning]
  exact congrArg (fun x : Option Int => x.map ULift.up) (integers.extract_encoded 3)

def emptyValues : Term 3 3 := .setOp .difference (.objects 2) values values

theorem empty_meaning : meaning (.collection (.objects 2)) emptyValues (by decide) = some ∅ := by
  change Clafer.Constraints.lift₂ (Clafer.Constraints.collectionOp .difference)
    (meaning (.collection (.objects 2)) values (by decide)) (meaning (.collection (.objects 2)) values (by decide)) = _
  rw [values_meaning]
  simp [Clafer.Constraints.lift₂, Clafer.Constraints.collectionOp]

theorem empty_extraction : meaning .integer (.integerOf 2 emptyValues) (by decide) = none := by
  change (meaning (.collection (.objects 2)) emptyValues (by decide)).bind (fun S => (integers.extract S).map ULift.up) = _
  rw [empty_meaning]
  simp

theorem strict_false_undefined : meaning .boolean
    (.and (.boolean false) (.less (.integerOf 2 emptyValues) (.integer 0))) (by decide) = none := by
  change Clafer.Constraints.lift₂ (fun p q : ULift Prop => (⟨p.down ∧ q.down⟩ : ULift Prop))
    (some ⟨false = true⟩)
    (Clafer.Constraints.lift₂ (fun p q : ULift Int => ⟨p.down < q.down⟩)
      (meaning .integer (.integerOf 2 emptyValues) (by decide)) (some ⟨0⟩)) = none
  rw [empty_extraction]
  rfl

theorem defined_false : meaning .boolean (.less (.integer 4) (.integer 3)) (by decide) = some ⟨False⟩ := by
  simp [meaning, interpret, Clafer.Constraints.Expr.denote, Clafer.Constraints.lift₂]

theorem ordered_subtraction : meaning .integer (.arithmetic .subtract (.integer 2) (.integer 5))
    (by decide) = some ⟨-3⟩ := rfl

theorem nested_shadowing : meaning .boolean shadow (by decide) = some ⟨True⟩ := by
  change (meaning (.collection (.objects 1)) heads (by decide)).bind (fun S =>
    Clafer.Constraints.universal S (fun x => Clafer.Constraints.universal {x}
      (fun y => some ⟨({y} : Set Atom) = {x}⟩))) = some ⟨True⟩
  rw [heads_meaning]
  simp [Clafer.Constraints.universal]

theorem empty_quantifier_undefined_body : meaning .boolean
    (.all ⟨3, "i", 2⟩ emptyValues (.less (.integerOf 2 emptyValues) (.integer 0))) (by decide) = some ⟨True⟩ := by
  simp only [meaning, interpret, Clafer.Constraints.Expr.denote]
  change (meaning (.collection (.objects 2)) emptyValues (by decide)).bind _ = _
  rw [empty_meaning]
  exact Clafer.Constraints.universal_empty _

theorem repeated_maps : meaning (.collection (.relation 1 2)) (.map 1) (by decide) =
    meaning (.collection (.relation 1 2)) (.map 2) (by decide) := by
  exact Clafer.Constraints.repeated_map_denotation model (extend_coherent observed_valid) env 1 2 rfl rfl

theorem collection_finite : ∃ S, meaning (.collection (.objects 2)) values (by decide) = some S ∧ S.Finite :=
  checked_collection_finite (⟨values, by decide, by decide⟩ : Checked s [] (.collection (.objects 2))) observed_valid env

theorem full_integers (i : Int) : Atom.integer i ∈ fullExtent s observed (2 : Fin 3) := ⟨i, rfl⟩

theorem root_preserved : fullExtent s observed (0 : Fin 3) = {Atom.object 0} := by
  ext a; simp [fullExtent, s, observed, atomSet]

theorem environment_ok :
    (environment s [inner, outer] ⟨.object 0, [.object 1, .object 2]⟩).Admissible model :=
  environment_admissible s observed observed_valid _ _ (by decide)

/-- A map-free support interprets literal constraints directly. -/
def noMaps : Support 1 0 := ⟨#v[100], #v[], 0, #v[false]⟩
theorem literal_without_navigation : ∃ c, check noMaps [] .boolean
    (.less (.integer 1) (.integer 2)) = .ok c := (check_iff _ _ _ _).mpr (by decide)

theorem literal_denotation_no_maps
    (m : Clafer.Constraints.IntegerBinding.{0,0} (support noMaps) Atom)
    (ρ : Clafer.Constraints.Environment (support noMaps) Atom []) :
    (interpret noMaps (.less (.integer 1) (.integer 2)) (Γ := []) (t := .boolean) (by decide)).denote m ρ =
      some ⟨True⟩ := by
  simp [interpret, Clafer.Constraints.Expr.denote, Clafer.Constraints.lift₂]

theorem ordered_maps : shadow.maps = [0] ∧ values.maps = [0, 1] ∧
    (Term.setOp .union (.relation 1 2) (.map 1) (.map 1) : Term 3 3).maps = [1, 1] := by decide

end ClaferCompiler.Tests.Expressions
