module

public import ClaferCompiler.Frontend.Behavioral.Values

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.ValueRules
open IR.Behavioral Values

/-- Presence observes heads; scalar integers never become truth values. -/
inductive Boolean : Value k n → Expression.Formula k n → Prop where
  | formula : Boolean (.formula a) a
  | collection : Boolean (.collection type a) (.atom (.primitive (.inhabited a)))
  | chain : Boolean (.chain a) (Surface.Transitions.expand self a)

inductive Heads : Value k n → Ty k → Expression.Collection k n → Prop where
  | collection : Heads (.collection type a) type a
  | integer : Heads (.integer a) .integers (.integer a)

/-- One implicit reference step, never recursive scalar coercion. A mixed view
is the union of its fixed-type pieces; its filter does not test current liveness. -/
inductive Target (v : IR.BehavioralStructural.Validated k) : Value k n → Value k n → Prop where
  | plain (h : IR.BehavioralSupport.referenceView v d = none) :
      Target v (.collection (.objects d) a) (.collection (.objects d) a)
  | reference {a : Expression.Collection k n} (h : IR.BehavioralSupport.referenceView v d = some r) :
      Target v (.collection (.objects d) a) (.collection (classType v r.target)
        (match a with | .set a => .set (.step (.deref d) a) | a => .step (.deref d) a))
  | mixed {a : Expression.Collection k n} : Target v (.collection (.mixed ds) a)
      (let pieces := ds.map fun d => match IR.BehavioralSupport.referenceView v d with
        | none => (d, Expression.Collection.ofType d a)
        | some r => (r.target, Expression.Collection.step (.deref d) (.ofType d a))
      .collection (classUnion v (pieces.map Prod.fst))
        (pieces.foldl (fun acc p => .union acc p.2) (.set .empty)))
  | integers : Target v (.collection .integers a) (.collection .integers a)
  | empty : Target v (.collection .empty a) (.collection .empty a)
  | integer : Target v (.integer a) (.integer a)
  | formula : Target v (.formula a) (.formula a)
  | chain : Target v (.chain a) (.chain a)

inductive Integer (v : IR.BehavioralStructural.Validated k) : Value k n → Expression.Integer k n → Prop where
  | scalar (h : Target v a (.integer b)) : Integer v a b
  | set (h : Target v a (.collection .integers b)) : Integer v a (.coerce b)
  | empty (h : Target v a (.collection .empty b)) : Integer v a (.coerce b)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem boolean_sound {a : Value k n} (h : boolean a = .ok b) : Boolean a b := by
  cases a <;> simp only [boolean, Except.ok.injEq] at h
  · cases h; exact .collection
  · cases h
  · cases h; exact .formula
  · cases h; exact .chain

theorem heads_sound {a : Value k n} (h : heads a = .ok (type, b)) : Heads a type b := by
  cases a <;> simp only [heads, Except.ok.injEq, Prod.mk.injEq] at h
  · rcases h with ⟨rfl, rfl⟩; exact .collection
  · rcases h with ⟨rfl, rfl⟩; exact .integer
  · cases h
  · cases h

theorem target_sound (v : IR.BehavioralStructural.Validated k) {a b : Value k n}
    (h : target v a = .ok b) : Target v a b := by
  cases a with
  | collection type a =>
    cases type with
    | objects d =>
      cases hr : IR.BehavioralSupport.referenceView v d <;> simp only [target, hr] at h
      · cases Except.ok.inj h; exact .plain hr
      · cases Except.ok.inj h; exact .reference hr
    | mixed ds => cases Except.ok.inj h; exact .mixed
    | integers => cases Except.ok.inj h; exact .integers
    | empty => cases Except.ok.inj h; exact .empty
  | integer a => cases Except.ok.inj h; exact .integer
  | formula a => cases Except.ok.inj h; exact .formula
  | chain a => cases Except.ok.inj h; exact .chain

theorem integer_sound (v : IR.BehavioralStructural.Validated k) {a : Value k n}
    (h : Values.integer v a = .ok b) : Integer v a b := by
  unfold Values.integer at h
  cases ht : target v a with
  | error err => simp [ht, bind, Except.bind] at h
  | ok value =>
    have rule := target_sound v ht
    cases value with
    | integer value => simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; cases h; exact .scalar rule
    | collection type value =>
      cases type <;> simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      · cases h
      · cases h; exact .set rule
      · cases h; exact .empty rule
      · cases h
    | formula _ => simp [ht, bind, Except.bind] at h
    | chain _ => simp [ht, bind, Except.bind] at h


/-- The accepted source spellings map to explicit temporal constructors.
These rules do not invoke the executable operation dispatcher. -/
inductive BooleanUnary : String → Expression.Formula k n → Expression.Formula k n → Prop where
  | not (h : (op == "!") = true) : BooleanUnary op a (.not a)
  | next (h : (op == "X" || op == "next") = true) : BooleanUnary op a (.next a)
  | eventually (h : (op == "F" || op == "eventually") = true) : BooleanUnary op a (.eventually a)
  | always (h : (op == "G" || op == "globally") = true) : BooleanUnary op a (.always a)
  | initially (h : (op == "initially") = true) : BooleanUnary op a (.initially a)
  | finally (h : (op == "finally") = true) : BooleanUnary op a (.finally a)

inductive Unary (v : IR.BehavioralStructural.Validated k) : String → Value k n → Value k n → Prop where
  | boolean (input : Boolean a b) (op : BooleanUnary spelling b c) : Unary v spelling a (.formula c)
  | negative (spelling : (op == "-") = true) (input : Integer v a b) : Unary v op a (.integer (.negate b))
  | cardinality (spelling : (op == "#") = true) (input : Heads a type b) :
      Unary v op a (.integer (.cardinality b))
  | some (spelling : (op == "some") = true) (input : Heads a type b) : Unary v op a (.formula (present b))
  | no (spelling : (op == "no" || op == "not") = true) (input : Heads a type b) :
      Unary v op a (.formula (.not (present b)))
  | one (spelling : (op == "one") = true) (input : Heads a type b) :
      Unary v op a (.formula (.atom (.primitive (.integerEqual (.cardinality b) (.literal 1)))))
  | lone (spelling : (op == "lone") = true) (input : Heads a type b) :
      Unary v op a (.formula (.atom (.primitive (.less (.cardinality b) (.literal 2)))))
  | extreme (spelling : (op == "min" || op == "max") = true) (view : Target v a b)
      (input : Heads b type c) (numeric : (type == .integers || type == .empty) = true) :
      Unary v op a (.collection .integers (.extreme (if op == "min" then .minimum else .maximum) c))

-- [proof->req~compiler-behavioral-elaboration~1]
theorem unary_sound (v : IR.BehavioralStructural.Validated k) {a b : Value k n}
    (h : Values.unary v op a = .ok b) : Unary v op a b := by
  unfold Values.unary at h
  by_cases hop : (op == "!") = true
  · simp only [ite_eq_left hop] at h
    cases hb : boolean a with
    | error err => simp [hb, bind, Except.bind] at h
    | ok value =>
      simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      cases h
      exact .boolean (boolean_sound hb) (.not hop)
  · simp only [ite_eq_right hop] at h
    by_cases hop : (op == "X" || op == "next") = true
    · simp only [ite_eq_left hop] at h
      cases hb : boolean a with
      | error err => simp [hb, bind, Except.bind] at h
      | ok value =>
        simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        cases h
        exact .boolean (boolean_sound hb) (.next hop)
    · simp only [ite_eq_right hop] at h
      by_cases hop : (op == "F" || op == "eventually") = true
      · simp only [ite_eq_left hop] at h
        cases hb : boolean a with
        | error err => simp [hb, bind, Except.bind] at h
        | ok value =>
          simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          cases h
          exact .boolean (boolean_sound hb) (.eventually hop)
      · simp only [ite_eq_right hop] at h
        by_cases hop : (op == "G" || op == "globally") = true
        · simp only [ite_eq_left hop] at h
          cases hb : boolean a with
          | error err => simp [hb, bind, Except.bind] at h
          | ok value =>
            simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
            cases h
            exact .boolean (boolean_sound hb) (.always hop)
        · simp only [ite_eq_right hop] at h
          by_cases hop : (op == "initially") = true
          · simp only [ite_eq_left hop] at h
            cases hb : boolean a with
            | error err => simp [hb, bind, Except.bind] at h
            | ok value =>
              simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
              cases h
              exact .boolean (boolean_sound hb) (.initially hop)
          · simp only [ite_eq_right hop] at h
            by_cases hop : (op == "finally") = true
            · simp only [ite_eq_left hop] at h
              cases hb : boolean a with
              | error err => simp [hb, bind, Except.bind] at h
              | ok value =>
                simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                cases h
                exact .boolean (boolean_sound hb) (.finally hop)
            · simp only [ite_eq_right hop] at h
              by_cases hop : (op == "-") = true
              · simp only [ite_eq_left hop] at h
                cases hb : Values.integer v a with
                | error err => simp [hb, bind, Except.bind] at h
                | ok value =>
                  simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                  cases h
                  exact .negative hop (integer_sound v hb)
              · simp only [ite_eq_right hop] at h
                by_cases hop : (op == "#") = true
                · simp only [ite_eq_left hop] at h
                  cases hb : heads a with
                  | error err => simp [hb, bind, Except.bind] at h
                  | ok value =>
                    rcases value with ⟨type, value⟩
                    simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                    cases h
                    exact .cardinality hop (heads_sound hb)
                · simp only [ite_eq_right hop] at h
                  by_cases hop : (op == "some") = true
                  · simp only [ite_eq_left hop] at h
                    cases hb : heads a with
                    | error err => simp [hb, bind, Except.bind] at h
                    | ok value =>
                      rcases value with ⟨type, value⟩
                      simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                      cases h
                      exact .some hop (heads_sound hb)
                  · simp only [ite_eq_right hop] at h
                    by_cases hop : (op == "no" || op == "not") = true
                    · simp only [ite_eq_left hop] at h
                      cases hb : heads a with
                      | error err => simp [hb, bind, Except.bind] at h
                      | ok value =>
                        rcases value with ⟨type, value⟩
                        simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                        cases h
                        exact .no hop (heads_sound hb)
                    · simp only [ite_eq_right hop] at h
                      by_cases hop : (op == "one") = true
                      · simp only [ite_eq_left hop] at h
                        cases hb : heads a with
                        | error err => simp [hb, bind, Except.bind] at h
                        | ok value =>
                          rcases value with ⟨type, value⟩
                          simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                          cases h
                          exact .one hop (heads_sound hb)
                      · simp only [ite_eq_right hop] at h
                        by_cases hop : (op == "lone") = true
                        · simp only [ite_eq_left hop] at h
                          cases hb : heads a with
                          | error err => simp [hb, bind, Except.bind] at h
                          | ok value =>
                            rcases value with ⟨type, value⟩
                            simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                            cases h
                            exact .lone hop (heads_sound hb)
                        · simp only [ite_eq_right hop] at h
                          by_cases hop : (op == "min" || op == "max") = true
                          · simp only [ite_eq_left hop] at h
                            cases ht : target v a with
                            | error err => simp [ht, bind, Except.bind] at h
                            | ok value =>
                              cases hh : heads value with
                              | error err => simp [ht, hh, bind, Except.bind] at h
                              | ok pair =>
                                rcases pair with ⟨type, value⟩
                                simp only [ht, hh, bind, Except.bind] at h
                                by_cases hn : (type == Ty.integers || type == Ty.empty) = true
                                · simp only [ite_eq_left hn] at h
                                  simp only [pure, Except.pure, Except.ok.injEq] at h
                                  cases h
                                  exact .extreme hop (target_sound v ht) (heads_sound hh) hn
                                · simp [hn] at h
                          · simp [hop] at h

end ClaferCompiler.Frontend.Behavioral.ValueRules
