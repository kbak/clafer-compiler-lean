module

public import ClaferCompiler.Frontend.Constraints

@[expose] public section
/-! Source syntax only observes maps through navigation from a finite input.
In particular, it never reads the full primitive containment map as a value.
[proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr Frontend.Constraints

def HeadSafe (c : IR.Structural.Core n) (s : Support n m) (e : Fin m) : Prop :=
  s.maps[e].kind = .head → (c.get s.maps[e].target).origin = .user

noncomputable def NavigationOnly (c : IR.Structural.Core n) (s : Support n m) : Syntax n m → Prop
  | .map _ | .join _ _ _ _ _ | .widenRelation _ _ _ _ _ _ _ => False
  | .image _ _ a (.map e) => NavigationOnly c s a ∧ HeadSafe c s e
  | .image _ _ _ _ => False
  | .and a b | .equal _ a b | .less a b | .arithmetic _ a b | .setOp _ _ a b |
    .subset _ a b | .all _ a b => NavigationOnly c s a ∧ NavigationOnly c s b
  | .not a | .integerOf _ a | .cardinality _ a | .widenObjects _ _ _ a | .located _ a =>
    NavigationOnly c s a
  | _ => True

theorem navigate_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : Navigate c s x a name y b) (ha : NavigationOnly c s a) : NavigationOnly c s b := by
  induction h with
  | field field _ kind _ target =>
    exact ⟨ha,fun _ => target ▸ field.2.2.2.1⟩
  | parent kind _ => exact ⟨ha,by intro he; have h := kind.symm.trans he; cases h⟩
  | dereference kind _ => exact ⟨ha,by intro he; have h := kind.symm.trans he; cases h⟩
  | throughReference _ kind _ _ ih => exact ih ⟨ha,by intro he; have h := kind.symm.trans he; cases h⟩

theorem scope_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : ScopePath s x a k y b) (ha : NavigationOnly c s a) : NavigationOnly c s b := by
  induction h with
  | here => exact ha
  | parent _ kind _ ih => exact ⟨ih,by intro he; have h := kind.symm.trans he; cases h⟩

def CursorNavigation (c : IR.Structural.Core n) (s : Support n m) : Cursor n m → Prop
  | none => True
  | some (_,a) => NavigationOnly c s a

theorem name_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : NameRule c s Γ cursor name t a) (hc : CursorNavigation c s cursor) :
    NavigationOnly c s a := by
  cases h with
  | this => trivial
  | «local» => trivial
  | global => trivial
  | special _ h => exact navigate_navigation h trivial
  | contextual _ _ _ _ _ _ path h => exact navigate_navigation h (scope_navigation path trivial)
  | relative h => exact navigate_navigation h hc

theorem coercion_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : Coerces s t a u b) (ha : NavigationOnly c s a) : NavigationOnly c s b := by
  induction h with
  | same => exact ha
  | some => exact ⟨trivial,ha⟩
  | integer => exact ha
  | dereference kind _ => exact ⟨ha,by intro he; have h := kind.symm.trans he; cases h⟩
  | widen => exact ha
  | trans _ _ _ iha ihb => exact ihb (iha ha)

theorem unary_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : UnaryRule op t a u b) (ha : NavigationOnly c s a) : NavigationOnly c s b := by
  cases h <;> simp_all [NavigationOnly]

theorem binary_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : BinaryRule s op t a b u d) (ha : NavigationOnly c s a) (hb : NavigationOnly c s b) :
    NavigationOnly c s d := by
  cases h <;> simp_all [NavigationOnly]

theorem quantified_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : QuantifierRule b d a op out) (hd : NavigationOnly c s d) (ha : NavigationOnly c s a) :
    NavigationOnly c s out := by
  cases h <;> simp_all [NavigationOnly]

/-- Derived from the independently stated source elaboration rules, not from a
new admission test or a restriction on accepted primitive parent navigation. -/
theorem elaborated_navigation {c : IR.Structural.Core n} {s : Support n m}
    (h : Elaborates c s Γ cursor coerce e t a) (hc : CursorNavigation c s cursor) :
    NavigationOnly c s a := by
  induction h with
  | name h => simpa only [NavigationOnly] using (name_navigation h hc)
  | integer => trivial
  | parens _ ih => exact ih hc
  | unary _ h ih => simpa only [NavigationOnly] using (unary_navigation h (ih hc))
  | binary _ _ h iha ihb => simpa only [NavigationOnly] using (binary_navigation h (iha hc) (ihb hc))
  | dot _ _ _ iha ihb => exact ihb (iha hc)
  | quantified _ _ _ _ h ihd iha => simpa only [NavigationOnly] using (quantified_navigation h (ihd hc) (iha trivial))
  | coerce _ h ih => exact coercion_navigation h (ih hc)

end ClaferCompiler.Correctness.Pipeline
