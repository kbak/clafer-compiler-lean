module

public import ClaferCompiler.Backend.Alloy.Semantics

@[expose] public section

namespace ClaferCompiler.Tests.AlloyCore
open Backend.Alloy

/-! Independent small target instances and kernel-reduced truth tables.
[utest->req~compiler-alloy-core~1]
[utest->req~compiler-bounds~1]
[proof->req~compiler-alloy-core~1]
[proof->req~compiler-bounds~1] -/

def schema : Schema := ⟨[{}, {}], [⟨0, 1, .set⟩]⟩
def fixture : Instance := ⟨[[0, 1], [2, 3]], [[[0, 2], [0, 3], [1, 2]]]⟩
def a : Rel := .sig 0
def b : Rel := .sig 1
def r : Rel := .field 0

def model (body : Formula) : Module :=
  ⟨schema, [], ⟨.run, body, [⟨2, true⟩, ⟨2, true⟩], 4⟩⟩

def observe (m : Module) (i : Instance) : Option Bool :=
  match check m with
  | .error _ => none
  | .ok checked => match evaluate checked i with
    | .error _ => none
    | .ok value => some value

def countEq (e : Rel) (n : Int) : Formula := .compare .eq (.count e) (.literal n)

def bag : Instance := ⟨[[0, 1], [2]], [[[0, 2], [1, 2]]]⟩
def bagModel (p : Formula) : Module :=
  { model p with command := ⟨.run, p, [⟨2, true⟩, ⟨1, true⟩], 4⟩ }

def hierarchy : Schema := ⟨[⟨none, true, .set⟩, ⟨some 0, false, .set⟩,
  ⟨some 0, false, .set⟩], []⟩
def hierarchyModel (p : Formula := .truth) : Module :=
  ⟨hierarchy, [], ⟨.run, p, [⟨2, false⟩, ⟨1, false⟩, ⟨1, false⟩], 4⟩⟩

/-- Each row has independently authored Alloy text in tests/fixtures/alloy-core.
`none` is an error and is never accepted as a negative truth-table result. -/
def observations : List (String × Option Bool) := [
  ("relation_count", observe (model (countEq r 3)) fixture),
  ("image", observe (model (.equal (.join a r) b)) fixture),
  ("transpose", observe (model (.equal (.join b (.transpose r)) a)) fixture),
  ("binary_join", observe (model (.equal (.join r (.transpose r)) (.product a a))) fixture),
  ("right_join", observe (model (.equal (.join r b) a)) fixture),
  ("union_unique", observe (model (countEq (.union a a) 2)) fixture),
  ("intersection", observe (model (.equal (.inter r (.product a b)) r)) fixture),
  ("difference", observe (model (countEq (.diff (.product a b) r) 1)) fixture),
  ("subset_false", observe (model (.subset (.product a b) r)) fixture),
  ("all_some", observe (model (.all a (.mult .some (.join (.var 0) r)))) fixture),
  ("all_one_false", observe (model (.all a (.mult .one (.join (.var 0) r)))) fixture),
  ("exists_one", observe (model (.exists_ a (.mult .one (.join (.var 0) r)))) fixture),
  ("shadow", observe (model (.all a (.exists_ b (.subset (.product (.var 1) (.var 0)) r)))) fixture),
  ("empty_all", observe (model (.all (.diff a a) .falsity)) fixture),
  ("empty_exists", observe (model (.exists_ (.diff a a) .truth)) fixture),
  ("logic", observe (model (.conj (.neg (.subset (.product a b) r))
    (.disj .falsity (.implies .truth (.compare .lt (.literal (-8)) (.literal 7)))))) fixture),
  ("check_counterexample", observe { model (.subset (.product a b) r) with
      command := { (model .truth).command with kind := .check, body := .subset (.product a b) r } } fixture),
  ("check_valid", observe { model (.subset r (.product a b)) with
      command := { (model .truth).command with kind := .check, body := .subset r (.product a b) } } fixture),
  ("bag_heads", observe (bagModel (.conj (countEq r 2) (countEq (.join a r) 1))) bag),
  ("bag_distinct_targets_false", observe (bagModel (countEq (.join a r) 2)) bag),
  ("abstract_cover", observe (hierarchyModel .truth) ⟨[[0, 1], [0], [1]], []⟩),
  ("abstract_uncovered", observe (hierarchyModel .truth) ⟨[[0, 1], [0], []], []⟩),
  ("siblings_overlap", observe (hierarchyModel .truth) ⟨[[0], [0], [0]], []⟩),
  ("parent_inclusion", observe (hierarchyModel .truth) ⟨[[0], [1], []], []⟩),
  ("abstract_leaf", observe ⟨⟨[⟨none, true, .set⟩], []⟩, [],
      ⟨.run, .truth, [⟨1, true⟩], 2⟩⟩ ⟨[[99]], []⟩),
  ("top_disjoint", observe (model .truth) ⟨[[0, 1], [1, 2]], [[[0, 2]]]⟩),
  ("field_orientation", observe (model .truth) ⟨[[0, 1], [2, 3]], [[[2, 0]]]⟩),
  ("field_one_false", observe { model .truth with
      schema := ⟨[{}, {}], [⟨0, 1, .one⟩]⟩ } fixture),
  ("field_one", observe { bagModel .truth with
      schema := ⟨[{}, {}], [⟨0, 1, .one⟩]⟩ } bag),
  ("upper_unused", observe ⟨⟨[{}], []⟩, [], ⟨.run, .truth, [⟨3, false⟩], 2⟩⟩ ⟨[[7]], []⟩),
  ("exact_too_small", observe ⟨⟨[{}], []⟩, [], ⟨.run, .truth, [⟨2, true⟩], 2⟩⟩ ⟨[[7]], []⟩),
  ("fact_false", observe { model .truth with facts := [.subset (.product a b) r] } fixture)
]

def expected : List Bool := [true, true, true, true, true, true, true, true,
  false, true, false, true, true, true, false, true, true, false, true, false,
  true, false, false, false, true, false, false, false, true, true, false, false]

set_option maxRecDepth 10000 in
theorem independent_truth_table : observations.map Prod.snd = expected.map some := by decide

theorem arity_and_binding_rejections :
    [Rel.typeOf schema 0 (.sig 2), Rel.typeOf schema 0 (.field 1),
     Rel.typeOf schema 0 (.var 0), Rel.typeOf schema 1 (.var 1),
     Rel.typeOf schema 0 (.union a r), Rel.typeOf schema 0 (.transpose a),
     Rel.typeOf schema 0 (.join a b), Rel.typeOf schema 0 (.product r b)] =
    List.replicate 8 none := by decide

theorem invalid_declarations_rejected :
    Schema.wellFormed ⟨[⟨some 0, false, .set⟩], []⟩ = false ∧
    Schema.wellFormed ⟨[{}, ⟨some 2, false, .set⟩], []⟩ = false ∧
    Schema.wellFormed ⟨[{}], [⟨0, 1, .set⟩]⟩ = false := by decide

theorem malformed_instruction_stacks_rejected :
    Rel.typeOf schema 0 ⟨[.join]⟩ = none ∧
    Rel.typeOf schema 0 ⟨[.sig 0, .sig 1]⟩ = none ∧
    Formula.wellTyped schema 0 ⟨[.neg]⟩ = false ∧
    Formula.wellTyped schema 0 ⟨[.truth, .falsity]⟩ = false := by decide

theorem malformed_tables_rejected :
    Instance.wellFormed schema ⟨[[0, 0], [1]], [[]]⟩ = false ∧
    Instance.wellFormed schema ⟨[[0], [1]], [[[0, 1], [0, 1]]]⟩ = false ∧
    Instance.wellFormed schema ⟨[[0], [1]], [[[0, 1, 2]]]⟩ = false ∧
    Instance.wellFormed schema ⟨[[0]], []⟩ = false := by decide

def countModel (size width : Nat) (p : Formula) : Module :=
  ⟨⟨[{}], []⟩, [], ⟨.run, p, [⟨size, false⟩], width⟩⟩

theorem signed_boundary :
    boundedInt 4 (-8) = some (-8) ∧ boundedInt 4 7 = some 7 ∧
    boundedInt 4 (-9) = none ∧ boundedInt 4 8 = none ∧
    boundedInt 1 0 = some 0 ∧ boundedInt 1 1 = none ∧
    boundedInt 0 0 = none ∧ boundedInt 17 0 = none := by decide

theorem conservative_cardinality_admission :
    (countModel 7 4 (countEq a 7)).safeBounds = true ∧
    (countModel 8 4 (countEq a 7)).safeBounds = false ∧
    (countModel 8 5 (countEq a 8)).safeBounds = true ∧
    (countModel 3 4 (countEq (.product a a) 0)).safeBounds = false ∧
    (countModel 2 4 (countEq (.product a a) 0)).safeBounds = true ∧
    (countModel 8 4 (.disj .truth (countEq a 0))).safeBounds = false ∧
    (countModel 8 4 (.all (.empty .unary) (countEq a 0))).safeBounds = false := by decide

theorem overflow_is_not_false :
    Formula.eval 4 ⟨[List.range 8], []⟩ [] (countEq a 0) = none ∧
    Formula.eval 4 ⟨[List.range 8], []⟩ [] (.neg (countEq a 0)) = none ∧
    Formula.eval 4 ⟨[List.range 8], []⟩ [] (.disj .truth (countEq a 0)) = none := by decide

theorem scope_count_rejected :
    ({ model .truth with command := ⟨.run, .truth, [⟨2, true⟩], 4⟩ } : Module).safeBounds = false := by decide

def multiplicityModel (mult : Multiplicity) (n : Nat) : Module :=
  ⟨⟨[⟨none, false, mult⟩], []⟩, [], ⟨.run, .truth, [⟨n, true⟩], 4⟩⟩

theorem signature_multiplicity_scopes :
    (multiplicityModel .one 0).safeBounds = false ∧
    (multiplicityModel .one 1).safeBounds = true ∧
    (multiplicityModel .one 2).safeBounds = false ∧
    (multiplicityModel .lone 0).safeBounds = true ∧
    (multiplicityModel .lone 1).safeBounds = true ∧
    (multiplicityModel .lone 2).safeBounds = false ∧
    (multiplicityModel .some 0).safeBounds = false ∧
    (multiplicityModel .some 2).safeBounds = true := by decide

theorem conflicting_source_scope_remains_negative :
    observe { multiplicityModel .set 0 with facts := [.mult .one a] } ⟨[[]], []⟩ = some false := by decide

theorem fiber_multiplicities :
    fixture.declarations ⟨[{}, {}], [⟨0, 1, .some⟩]⟩ = true ∧
    fixture.declarations ⟨[{}, {}], [⟨0, 1, .lone⟩]⟩ = false ∧
    bag.declarations ⟨[{}, {}], [⟨0, 1, .lone⟩]⟩ = true ∧
    Instance.declarations ⟨[{}, {}], [⟨0, 1, .one⟩]⟩ ⟨[[0, 1], [2]], [[[0, 2]]]⟩ = false := by decide

theorem safety_checks_facts_literals_and_negation :
    ({ model .truth with facts := [.compare .eq (.literal 8) (.literal 8)] } : Module).safeBounds = false ∧
    (model (.neg (.compare .lt (.literal (-9)) (.literal 0)))).safeBounds = false ∧
    (countModel 8 4 (.implies .falsity (countEq a 0))).safeBounds = false := by decide

end ClaferCompiler.Tests.AlloyCore
