module

public import ClaferCompiler.Frontend.Behavioral.BinaryRules

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.ValueRules
open IR.Behavioral Values

def scalarPair (a b : Value k n) : Bool :=
  match a, b with
  | .integer _, _ | _, .integer _ => true
  | _, _ => false

/-- Conditional branches have a common value kind. A Boolean branch selects
presence coercion; a scalar branch selects integer coercion. Collection branches
retain their heads and union their possible classes. All branches remain in IR. -/
-- [impl->req~compiler-behavioral-elaboration~1]
inductive Conditional (v : IR.BehavioralStructural.Validated k) (condition : Expression.Formula k n) :
    Value k n → Value k n → Value k n → Prop where
  | boolean (kind : (booleanLike a || booleanLike b) = true)
      (yes : Boolean a x) (no : Boolean b y) : Conditional v condition a b (.formula (.ite condition x y))
  | integer (kind : scalarPair a b = true) (yes : Integer v a x) (no : Integer v b y) :
      Conditional v condition a b (.integer (.ite condition x y))
  | collection : Conditional v condition (.collection tx x) (.collection ty y)
      (.collection (classUnion v (classes v tx ++ classes v ty)) (.ite condition x y))

private theorem conditional_boolean {a b c : Value k n} {condition : Expression.Formula k n}
    {v : IR.BehavioralStructural.Validated k} (kind : (booleanLike a || booleanLike b) = true)
    (h : (do
      let x ← boolean a
      let y ← boolean b
      pure (.formula (.ite condition x y))) = (.ok c : Except String (Value k n))) :
    Conditional v condition a b c := by
  simp [bind_success, pure, Except.pure] at h
  rcases h with ⟨x, hx, y, hy, rfl⟩
  exact .boolean kind (boolean_sound hx) (boolean_sound hy)

private theorem conditional_integer {a b c : Value k n} {condition : Expression.Formula k n}
    {v : IR.BehavioralStructural.Validated k} (kind : scalarPair a b = true)
    (h : (do
      let x ← Values.integer v a
      let y ← Values.integer v b
      pure (.integer (.ite condition x y))) = (.ok c : Except String (Value k n))) :
    Conditional v condition a b c := by
  simp [bind_success, pure, Except.pure] at h
  rcases h with ⟨x, hx, y, hy, rfl⟩
  exact .integer kind (integer_sound v hx) (integer_sound v hy)

private theorem conditional_collection
    (h : Values.conditional v condition (.collection tx x) (.collection ty y) = .ok c) :
    Conditional v condition (.collection tx x) (.collection ty y) c := by
  simp only [Values.conditional, common, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  cases h
  exact .collection

-- [proof->req~compiler-behavioral-elaboration~1]
theorem conditional_sound {a b c : Value k n}
    (h : Values.conditional v condition a b = .ok c) : Conditional v condition a b c := by
  cases a <;> cases b
  all_goals first
    | exact conditional_boolean rfl h
    | exact conditional_integer rfl h
    | exact conditional_collection h

end ClaferCompiler.Frontend.Behavioral.ValueRules
