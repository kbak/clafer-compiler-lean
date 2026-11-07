module

public import ClaferCompiler.Frontend.Behavioral.ValueRules

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.ValueRules
open IR.Behavioral Values

/-- Success of sequencing retains both successful observations. -/
theorem bind_success {x : Except ε α} {f : α → Except ε β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- This table specifies the result for each accepted Boolean binary spelling;
it has no coercion, error recovery or default temporal operator. -/
def booleanBinary (op : String) (a b : Expression.Formula k n) : Option (Expression.Formula k n) :=
  match op with
  | "&&" => some (.and a b) | "||" => some (.or a b)
  | "=>" => some (.implies a b) | "<=>" => some (.iff a b)
  | "xor" => some (.xor a b)
  | "U" | "until" => some (.strongUntil a b)
  | "W" | "weakuntil" => some (.weakUntil a b)
  | _ => none

def integerBinary (op : String) (a b : Expression.Integer k n) : Option (Value k n) :=
  match op with
  | "+" => some (.integer (.binary .add a b))
  | "-" => some (.integer (.binary .subtract a b))
  | "*" => some (.integer (.binary .multiply a b))
  | "/" => some (.integer (.binary .divide a b))
  | "%" => some (.integer (.binary .remainder a b))
  | "<" => some (.formula (.atom (.primitive (.less a b))))
  | ">" => some (.formula (.atom (.primitive (.less b a))))
  | "<=" => some (.formula (.not (.atom (.primitive (.less b a)))))
  | ">=" => some (.formula (.not (.atom (.primitive (.less a b)))))
  | _ => none

/-- Unary collections have a single column, so both relation restrictions
select the intersection. Total head paths retain their total representation. -/
def setBinary (op : String) (a b : Expression.Collection k n) : Option (Expression.Collection k n) :=
  match op with
  | "++" | "," => some (match a, b with | .set a, .set b => .set (.union a b) | a, b => .union a b)
  | "--" => some (match a, b with | .set a, .set b => .set (.diff a b) | a, b => .diff a b)
  | "**" | "&" | "<:" | ":>" => some (match a, b with | .set a, .set b => .set (.inter a b) | a, b => .inter a b)
  | _ => none

/-- The type intersection is a finite union of the more specific compatible
classes; emptiness is a polymorphic bottom type. -/
def intersectionClasses (v : IR.BehavioralStructural.Validated k) (a b : Ty k) : List (Fin k) :=
  (classes v a).flatMap fun x => (classes v b).filterMap fun y =>
    if y ∈ v.analysis.ancestors[x] then some x
    else if x ∈ v.analysis.ancestors[y] then some y else none

def Compatible (v : IR.BehavioralStructural.Validated k) (a b : Ty k) : Prop :=
  a = .empty ∨ b = .empty ∨ (intersectionClasses v a b).isEmpty = false

inductive SetType (v : IR.BehavioralStructural.Validated k) : String → Ty k → Ty k → Ty k → Prop where
  | union (op : spelling = "++" ∨ spelling = ",") :
      SetType v spelling a b (classUnion v (classes v a ++ classes v b))
  | difference (compatible : Compatible v a b) : SetType v "--" a b a
  | intersection (op : spelling ∈ ["**", "&", "<:", ":>"]) (compatible : Compatible v a b) :
      SetType v spelling a b (classUnion v (intersectionClasses v a b))

/-- Equality and containment use head comparison when either operand has the
empty type; otherwise exactly one implicit target view is selected. -/
inductive ComparisonViews (v : IR.BehavioralStructural.Validated k) :
    Value k n → Value k n → Value k n → Value k n → Prop where
  | emptyLeft : ComparisonViews v (.collection .empty a) b (.collection .empty a) b
  | emptyRight : ComparisonViews v a (.collection .empty b) a (.collection .empty b)
  | targets (nonempty : emptyPair a b = false) (left : Target v a x) (right : Target v b y) : ComparisonViews v a b x y

def comparison (op : String) (a b : Expression.Collection k n) : Option (Expression.Formula k n) :=
  match op with
  | "=" => some (.atom (.primitive (.equal a b)))
  | "!=" => some (.not (.atom (.primitive (.equal a b))))
  | "in" => some (.atom (.primitive (.subset a b)))
  | "not in" => some (.not (.atom (.primitive (.subset a b))))
  | _ => none

-- [impl->req~compiler-behavioral-elaboration~1]
inductive Binary (v : IR.BehavioralStructural.Validated k) : String → Value k n → Value k n → Value k n → Prop where
  | boolean (left : Boolean a x) (right : Boolean b y) (result : booleanBinary op x y = some z) :
      Binary v op a b (.formula z)
  | integer (left : Integer v a x) (right : Integer v b y) (result : integerBinary op x y = some c) :
      Binary v op a b c
  | collection (left : Heads a tx x) (right : Heads b ty y) (type : SetType v op tx ty tz)
      (result : setBinary op x y = some z) : Binary v op a b (.collection tz z)
  | iff (boolean : (booleanLike a || booleanLike b) = true) (left : Boolean a x) (right : Boolean b y) :
      Binary v "=" a b (.formula (.iff x y))
  | notIff (boolean : (booleanLike a || booleanLike b) = true) (left : Boolean a x) (right : Boolean b y) :
      Binary v "!=" a b (.formula (.not (.iff x y)))
  | comparison (views : ComparisonViews v a b x y) (left : Heads x tx p) (right : Heads y ty q)
      (compatible : Compatible v tx ty) (result : comparison op p q = some z) :
      Binary v op a b (.formula z)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem overlap_sound (h : overlap v a b = .ok t) :
    Compatible v a b ∧ t = classUnion v (intersectionClasses v a b) := by
  unfold overlap at h
  dsimp only at h
  split at h
  · cases h
  · next hn =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine ⟨?_, h.symm⟩
    simp only [Bool.and_eq_true, bne_iff_ne, not_and] at hn
    unfold Compatible intersectionClasses
    by_cases ha : a = .empty
    · exact Or.inl ha
    · by_cases hb : b = .empty
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Bool.eq_false_iff.mpr (fun he => hn ⟨he, ha⟩ hb)))

private theorem comparison_result (hop : op ∈ ["=", "!=", "in", "not in"])
    (p q : Expression.Collection k n) :
    comparison op p q = some (if op == "!=" || op == "not in" then
      .not (.atom (.primitive (if op == "=" || op == "!=" then .equal p q else .subset p q)))
      else .atom (.primitive (if op == "=" || op == "!=" then .equal p q else .subset p q))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;> rfl

private theorem empty_views {a b : Value k n}
    (h : emptyPair a b = true) : ComparisonViews v a b a b := by
  unfold emptyPair at h
  cases a with
  | collection ta a =>
    cases ta with
    | empty => exact .emptyLeft
    | objects d | integers | mixed ds =>
      cases b with
      | collection tb b =>
        cases tb <;> simp only [Bool.false_eq_true] at h
        exact .emptyRight
      | integer _ | formula _ | chain _ => cases h
  | integer _ | formula _ | chain _ =>
    cases b with
    | collection tb b =>
      cases tb <;> simp only [Bool.false_eq_true] at h
      exact .emptyRight
    | integer _ | formula _ | chain _ => cases h

-- [proof->req~compiler-behavioral-elaboration~1]
theorem compare_sound (hop : op ∈ ["=", "!=", "in", "not in"])
    {a b c : Value k n} (h : Values.compareValues v op a b = .ok c) : Binary v op a b c := by
  unfold Values.compareValues at h
  cases he : emptyPair a b with
  | false =>
    simp [he, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, tx, p, hp, ty, q, hq, htype, rfl⟩
    obtain ⟨t, ht⟩ := htype
    exact .comparison (.targets he (target_sound v hx) (target_sound v hy))
      (heads_sound hp) (heads_sound hq) (overlap_sound ht).1 (by simpa only [Bool.or_eq_true, beq_iff_eq] using comparison_result hop p q)
  | true =>
    simp [he, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, p, hp, ty, q, hq, htype, rfl⟩
    obtain ⟨t, ht⟩ := htype
    exact .comparison (empty_views he) (heads_sound hp) (heads_sound hq)
      (overlap_sound ht).1 (by simpa only [Bool.or_eq_true, beq_iff_eq] using comparison_result hop p q)

-- [proof->req~compiler-behavioral-elaboration~1]
theorem binary_sound {a b c : Value k n} (h : Values.binary v op a b = .ok c) : Binary v op a b c := by
  by_cases hop0 : op = "&&"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop1 : op = "||"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop2 : op = "=>"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop3 : op = "<=>"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop4 : op = "xor"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop5 : op = "U"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop6 : op = "until"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop7 : op = "W"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop8 : op = "weakuntil"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .boolean (boolean_sound hx) (boolean_sound hy) rfl
  by_cases hop9 : op = "+"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop10 : op = "-"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop11 : op = "*"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop12 : op = "/"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop13 : op = "%"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop14 : op = "<"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop15 : op = ">"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop16 : op = "<="
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop17 : op = ">="
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨x, hx, y, hy, rfl⟩
    exact .integer (integer_sound v hx) (integer_sound v hy) rfl
  by_cases hop18 : op = "++"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure, common] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, rfl⟩
    refine .collection (heads_sound hx) (heads_sound hy) (.union (Or.inl rfl)) ?_
    cases x <;> cases y <;> rfl
  by_cases hop19 : op = ","
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure, common] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, rfl⟩
    refine .collection (heads_sound hx) (heads_sound hy) (.union (Or.inr rfl)) ?_
    cases x <;> cases y <;> rfl
  by_cases hop20 : op = "--"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, htype, rfl⟩
    obtain ⟨t, ht⟩ := htype
    refine .collection (heads_sound hx) (heads_sound hy) (.difference (overlap_sound ht).1) ?_
    cases x <;> cases y <;> rfl
  by_cases hop21 : op = "**"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, t, ht, rfl⟩
    have checked := overlap_sound ht
    cases checked.2
    refine .collection (heads_sound hx) (heads_sound hy) (.intersection (by simp) checked.1) ?_
    cases x <;> cases y <;> rfl
  by_cases hop22 : op = "&"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, t, ht, rfl⟩
    have checked := overlap_sound ht
    cases checked.2
    refine .collection (heads_sound hx) (heads_sound hy) (.intersection (by simp) checked.1) ?_
    cases x <;> cases y <;> rfl
  by_cases hop23 : op = "<:"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, t, ht, rfl⟩
    have checked := overlap_sound ht
    cases checked.2
    refine .collection (heads_sound hx) (heads_sound hy) (.intersection (by simp) checked.1) ?_
    cases x <;> cases y <;> rfl
  by_cases hop24 : op = ":>"
  · subst op
    simp [Values.binary, bind_success, pure, Except.pure] at h
    rcases h with ⟨tx, x, hx, ty, y, hy, t, ht, rfl⟩
    have checked := overlap_sound ht
    cases checked.2
    refine .collection (heads_sound hx) (heads_sound hy) (.intersection (by simp) checked.1) ?_
    cases x <;> cases y <;> rfl
  by_cases hop25 : op = "="
  · subst op
    cases hb : booleanLike a || booleanLike b with
    | true =>
      simp [Values.binary, hb, bind_success, pure, Except.pure] at h
      rcases h with ⟨x, hx, y, hy, rfl⟩
      exact .iff hb (boolean_sound hx) (boolean_sound hy)
    | false =>
      simp [Values.binary, hb] at h
      exact compare_sound (by simp) h
  by_cases hop26 : op = "!="
  · subst op
    cases hb : booleanLike a || booleanLike b with
    | true =>
      simp [Values.binary, hb, bind_success, pure, Except.pure] at h
      rcases h with ⟨x, hx, y, hy, rfl⟩
      exact .notIff hb (boolean_sound hx) (boolean_sound hy)
    | false =>
      simp [Values.binary, hb] at h
      exact compare_sound (by simp) h
  by_cases hop27 : op = "in"
  · subst op
    simp [Values.binary] at h
    exact compare_sound (by simp) h
  by_cases hop28 : op = "not in"
  · subst op
    simp [Values.binary] at h
    exact compare_sound (by simp) h
  simp [Values.binary, hop0, hop1, hop2, hop3, hop4, hop5, hop6, hop7, hop8, hop9, hop10, hop11, hop12, hop13, hop14, hop15, hop16, hop17, hop18, hop19, hop20, hop21, hop22, hop23, hop24, hop25, hop26, hop27, hop28] at h

end ClaferCompiler.Frontend.Behavioral.ValueRules
