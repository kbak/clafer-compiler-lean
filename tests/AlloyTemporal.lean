module

public import ClaferCompiler.Backend.Alloy.Temporal

@[expose] public section
namespace ClaferCompiler.Tests.AlloyTemporal
open Backend.Alloy (Multiplicity CommandKind)
open Backend.Alloy.Temporal

-- [utest->req~compiler-alloy-temporal-target~1]
-- [utest->req~compiler-alloy-temporal-text~1]
def p : Formula := .mult .some (.sig 0)
def q : Formula := .unary .neg p
def always (f : Formula) : Formula := .unary .always f
def after (f : Formula) : Formula := .unary .after f
def not_ (f : Formula) : Formula := .unary .neg f
def and_ (f g : Formula) : Formula := .binary .conj f g

def base (body : Formula) (facts : List Formula := []) (kind : CommandKind := .run) : Module :=
  ⟨⟨⟨[{}], []⟩, [true], []⟩, facts, ⟨kind, body, [⟨1, false⟩], 4, 1, 4⟩⟩

def toggle : Formula := always (and_ (.binary .implies p (after q)) (.binary .implies q (after p)))
def equivalent (a b : Formula) : Formula := and_ (.binary .implies a b) (.binary .implies b a)

def fieldModel (mutable : Bool) : Module :=
  ⟨⟨⟨[{ multiplicity := .one }, {}], [⟨0, 1, .set⟩]⟩, [false, false], [mutable]⟩,
    [.mult .some (.field 0)],
    ⟨.run, after (not_ (.mult .some (.field 0))), [⟨1, true⟩, ⟨2, true⟩], 4, 1, 4⟩⟩

def replacement (capacity : Nat) : Module :=
  { base (.all (.sig 0) (after (and_ p (not_ (.subset (.var 0) (.sig 0))))))
      [always (.mult .one (.sig 0))] with
    command := { (base (.all (.sig 0) (after (and_ p (not_ (.subset (.var 0) (.sig 0))))))).command with
      scopes := [⟨capacity, false⟩] } }

def prefixModel : Module :=
  ⟨⟨⟨[{}, {}], []⟩, [true, true], []⟩,
    [p, toggle, .mult .some (.sig 1), always (after (not_ (.mult .some (.sig 1))))],
    ⟨.run, after (after p.birth), [⟨1, false⟩, ⟨1, false⟩], 4, 3, 4⟩⟩

def migrating (capture : Bool) : Module :=
  ⟨⟨⟨[{}, {}], []⟩, [true, true], []⟩, [p],
    ⟨.run, if capture then .all (.sig 0) (after (.subset (.var 0) (.sig 1)))
      else after (.mult .some (.sig 1)), [⟨1, false⟩, ⟨1, false⟩], 4, 1, 4⟩⟩

def singletonReplacement (mult : Multiplicity) : Module :=
  { replacement 2 with schema := ⟨⟨[{ multiplicity := mult }], []⟩, [true], []⟩ }

/-- Each query has a separately authored expected outcome and distinguishing witness. -/
def cases : List (String × Bool × Module) := [
  ("one-var-replacement", true, singletonReplacement .one),
  ("lone-var-replacement", true, singletonReplacement .lone),
  ("type-migration", false, migrating true),
  ("different-types", true, migrating false),
  ("identity-one", false, replacement 1),
  ("identity-two", true, replacement 2),
  ("nonzero-prefix", true, prefixModel),
  ("initial-only", true, base (.unary .eventually q) [p]),
  ("always-mutation", false, base (.unary .eventually q) [always p]),
  ("prime-after", false, base (equivalent (.mult .some (.prime (.sig 0))) (after p)) [] .check),
  ("until-event", true, base (.binary .until p q) [p, toggle]),
  ("until-missing", false, base (.binary .until p q) [always p]),
  ("weak-until", true, base (p.weakUntil q) [always p]),
  ("release-forever", true, base (.binary .releases q p) [always p]),
  ("release-inclusive", false, base (.binary .releases p q) [p]),
  ("before-initial", false, base (.unary .before .truth)),
  ("birth-initial", true, base p.birth [p]),
  ("birth-loop", true, base (after (after p.birth)) [p, toggle]),
  ("history-loop", false, base (after (after (.unary .historically p))) [p, toggle]),
  ("once-history", true, base (after (after (.unary .once p))) [p, toggle]),
  ("since-event", true, base (after (.binary .since q p)) [p, toggle]),
  ("triggered-inclusive", false, base (.binary .triggered p q) [p]),
  ("mutable-field", true, fieldModel true),
  ("static-field", false, fieldModel false),
  ("capture", true, base (.exists_ (.sig 0) (after (and_
      (.mult .some (.var 0)) (.equal (.prime (.var 0)) (.var 0))))) [p, toggle]),
  ("univ-prime", true, base (not_ (.equal .univ (.prime .univ))) [p, toggle]),
  ("iden-prime", true, base (not_ (.equal .iden (.prime .iden))) [p, toggle]),
  ("int-univ", false, base (.subset .ints .univ) [] .check),
  ("scalar-valid", true, base (.compare .eq (.scalar (-3) 3 (.integer 2)) (.literal 2))),
  ("scalar-empty", true, base (.compare .eq (.scalar (-3) 3 (.empty .unary)) (.literal (-3)))),
  ("scalar-object", true, base (.compare .eq (.scalar (-3) 3 (.sig 0)) (.literal (-3))) [p]),
  ("scalar-mixed", true, base (.compare .eq (.scalar (-3) 3 (.union (.sig 0) (.integer 2))) (.literal (-3))) [p]),
  ("scalar-many-overflow", true, base (.compare .eq (.scalar (-3) 3 (.union (.integer 6) (.integer 7))) (.literal (-3)))),
  ("scalar-outside-range", true, base (.compare .eq (.scalar (-3) 3 (.integer 6)) (.literal (-3)))),
  ("integer-product", true, base (.compare .eq (.multiply (.literal (-2)) (.literal 3)) (.literal (-6)))),
  ("integer-quotient", true, base (.compare .eq (.divide (.literal (-7)) (.literal 3)) (.literal (-2)))),
  ("integer-remainder", true, base (.compare .eq (.remainder (.literal (-7)) (.literal 3)) (.literal (-1)))),
  ("integer-negative-divisor", true, base (.compare .eq (.divide (.literal 7) (.literal (-3))) (.literal (-2)))),
  ("integer-two-negatives", true, base (.compare .eq (.divide (.literal (-7)) (.literal (-3))) (.literal 2))),
  ("integer-remainder-sign", true, base (.compare .eq (.remainder (.literal 7) (.literal (-3))) (.literal 1))),
  ("integer-floor-mutation", false, base (.compare .eq (.divide (.literal (-7)) (.literal 3)) (.literal (-3)))),
  ("integer-remainder-mutation", false, base (.compare .eq (.remainder (.literal (-7)) (.literal 3)) (.literal 2))),
  ("integer-current-count", true, base (and_
      (.compare .eq (.multiply (.literal 3) (.count (.sig 0))) (.literal 3))
      (after (.compare .eq (.multiply (.literal 3) (.count (.sig 0))) (.literal 0)))) [p, toggle]),
  ("mutable-identity-one", false, base (and_ (.mult .one (.sig 0))
      (after (.equal (.sig 0) (.empty .unary)))) [always p])
]

/-- Constructor coverage includes nested capture, noncommutative relations,
integers, all temporal tokens and both command polarities. -/
def syntaxBodies : List Formula :=
  let r := Rel.sig 0
  let relations : List Rel := [r, .empty .unary, .univ, .ints, .prime r,
    .union r r, .inter r r, .diff r r, .join r .iden,
    .empty .binary, .iden, .product r r, .transpose .iden, .join .iden .iden]
  relations.flatMap (fun r => [.equal r r, .subset r r, .mult .set r, .mult .lone r,
    .mult .one r, .mult .some r]) ++
  ([Unary.neg, .after, .always, .eventually, .before, .once, .historically].map fun op => .unary op p) ++
  ([Binary.conj, .disj, .implies, .until, .releases, .since, .triggered].map fun op => .binary op p q) ++
  [.truth, .falsity, .compare .eq (.literal (-8)) (.literal (-8)),
   .compare .lt (.count r) (.add (.literal 1) (.literal 2)),
   .compare .le (.subtract (.literal 3) (.count r)) (.literal 3),
   .all r (.exists_ r (after (.equal (.var 1) (.var 0))))]

def cycle : Lasso := ⟨[7], [⟨[[7]], [], []⟩, ⟨[[]], [], []⟩], 0, by decide, by decide⟩
def prefixed : Lasso := ⟨[7], [⟨[[]], [], []⟩, ⟨[[7]], [], []⟩, ⟨[[]], [], []⟩],
  1, by decide, by decide⟩

-- [proof->req~compiler-alloy-temporal-target~1]
-- [utest->req~compiler-alloy-temporal-target~1]
theorem loop_indices : (List.range 8).map cycle.index = [0, 1, 0, 1, 0, 1, 0, 1] := by decide

theorem prefix_indices : (List.range 8).map prefixed.index = [0, 1, 2, 1, 2, 1, 2, 1] := by decide

theorem loop_birth : p.birth.Holds (base p).schema 4 cycle.unfold [] 2 := by
  apply (birth_succ (base p).schema 4 cycle.unfold [] p (.mult .some (.sig 0)) 1).mpr
  constructor
  · change true = true
    rfl
  · change ¬ false = true
    decide

theorem initial_history_differs :
    ¬ (Formula.unary .historically p).Holds (base p).schema 4 cycle.unfold [] 2 := by
  intro h
  have bad := h 1 (by decide)
  change false = true at bad
  cases bad

-- [utest->req~compiler-alloy-temporal-target~1]
theorem admitted_cases : cases.all (fun c => (check c.2.2).isOk) = true := by decide

theorem zero_steps_rejected : (check { base p with command := { (base p).command with minSteps := 0 } }).isOk = false := by decide

theorem hidden_overflow_rejected :
    (check (base (not_ (.compare .eq (.add (.literal 7) (.literal 1)) (.literal 0))))).isOk = false := by decide

-- [utest->req~compiler-alloy-temporal-target~1]
theorem product_overflow_under_false_guard_rejected :
    (check (base (.binary .implies .falsity
      (.compare .eq (.multiply (.literal 3) (.literal 3)) (.literal 1))))).isOk = false := by decide

theorem division_by_zero_under_negation_rejected :
    (check (base (not_ (.compare .eq (.divide (.literal 1) (.literal 0)) (.literal 0))))).isOk = false := by decide

theorem remainder_by_zero_in_empty_binder_rejected :
    (check (base (.all (.empty .unary)
      (.compare .eq (.remainder (.literal 1) (.literal 0)) (.literal 0))))).isOk = false := by decide

theorem possible_zero_divisor_rejected :
    (check (base (.compare .eq (.divide (.literal 1) (.count (.sig 0))) (.literal 1)) [p])).isOk = false := by decide

theorem quotient_overflow_rejected :
    (check (base (.compare .eq (.divide (.literal (-8)) (.literal (-1))) (.literal 0)))).isOk = false := by decide

theorem overflowing_intermediate_rejected :
    (check (base (.compare .eq
      (.multiply (.multiply (.literal 3) (.literal 3)) (.literal 0)) (.literal 0)))).isOk = false := by decide

theorem signed_arithmetic_evaluation :
    (Integer.divide (.literal (-7)) (.literal 3)).eval (base p).schema 4 cycle.unfold [] 0 = some (-2) ∧
    (Integer.remainder (.literal (-7)) (.literal 3)).eval (base p).schema 4 cycle.unfold [] 0 = some (-1) ∧
    (Integer.multiply (.literal (-2)) (.literal 3)).eval (base p).schema 4 cycle.unfold [] 0 = some (-6) := by decide

theorem undefined_arithmetic_evaluation :
    (Integer.divide (.literal 1) (.literal 0)).eval (base p).schema 4 cycle.unfold [] 0 = none ∧
    (Integer.remainder (.literal 1) (.literal 0)).eval (base p).schema 4 cycle.unfold [] 0 = none ∧
    (Integer.divide (.literal (-8)) (.literal (-1))).eval (base p).schema 4 cycle.unfold [] 0 = none ∧
    (Integer.multiply (.literal 3) (.literal 3)).eval (base p).schema 4 cycle.unfold [] 0 = none := by decide

theorem nested_integer_literal_rejected :
    (check (base (.compare .eq (.count (.integer 100)) (.literal 0)))).isOk = false ∧
    (check (base (.compare .eq (.scalar 0 1 (.integer 100)) (.literal 0)))).isOk = false := by decide

theorem bad_binding_rejected : (check (base (.mult .one (.var 0)))).isOk = false := by decide

-- [utest->req~compiler-alloy-temporal-target~1]
theorem empty_lasso_rejected : (checkLasso (base p).schema [] [] 0).isOk = false := by decide

theorem bad_loop_rejected :
    (checkLasso (base p).schema [7] cycle.frames 2).isOk = false := by decide

theorem foreign_atom_rejected :
    (checkLasso (base p).schema [] cycle.frames 0).isOk = false := by decide

theorem valid_lasso_admitted :
    (checkLasso (base p).schema [7] cycle.frames 0).isOk = true := by decide

theorem exact_mutable_rejected :
    (check { base p with command := { (base p).command with scopes := [⟨1, true⟩] } }).isOk = false := by decide

theorem static_steps_rejected :
    (check { base p with schema := ⟨⟨[{}], []⟩, [false], []⟩ }).isOk = false := by decide

-- [utest->req~compiler-alloy-temporal-target~1]
theorem malformed_programs_rejected :
    ([Formula.mult .some ⟨[.union]⟩, .mult .some ⟨[.sig 0, .sig 0]⟩,
      .compare .eq ⟨[.add]⟩ (.literal 0), .compare .eq ⟨[.literal 0, .literal 1]⟩ (.literal 0),
      .compare .eq ⟨[.multiply]⟩ (.literal 0), .compare .eq ⟨[.literal 1, .divide]⟩ (.literal 0),
      .compare .eq ⟨[.literal 1, .remainder]⟩ (.literal 0),
      ⟨[.unary .after]⟩, ⟨[.truth, .truth]⟩].all fun f => !(check (base f)).isOk) = true := by decide

end ClaferCompiler.Tests.AlloyTemporal
