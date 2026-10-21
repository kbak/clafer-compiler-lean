module

public import ClaferCompiler.Backend.Alloy.Expressions
public import ClaferCompiler.Correctness.AlloyEvaluation
public import ClaferCompiler.Correctness.IntegerArithmetic

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionConstruction
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

/-- Construction witnesses establish stack discipline only. -/
def ValueBuilt : (t : Ty n) → ValueCode t → Prop
  | .boolean, p => p.Term
  | .integer, i => i.Term
  | .collection _, r => r.Term

def Built {t : Ty n} (c : Code t) : Prop := c.defined.Term ∧ ValueBuilt t c.value

def LayoutBuilt (l : Layout n m) : Prop :=
  (∀ x : Fin n, l.extents[x].Term) ∧ ∀ e : Fin m, l.maps[e].Term

theorem equal_built (t : Ty n) (a b : ValueCode t) (ha : ValueBuilt t a) (hb : ValueBuilt t b) :
    (equalCode t a b).Term := by
  cases t with
  | boolean => exact .conj (.implies ha hb) (.implies hb ha)
  | integer => exact .compare _ _ _
  | collection k => exact .equal _ _

theorem encodeAt_built (s : Support n m) (l : Layout n m) (b : IR.Expr.Bounds n)
    (hl : LayoutBuilt l) (fuel : Nat) (e : Syntax n m) (h : e.depth < fuel)
    {Γ : List (Local n)} {t : Ty n} (ht : e.Typed s Γ t) :
    Built (encodeAt s l b fuel e h ht) := by
  induction fuel generalizing e Γ t with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ fuel ih =>
    cases e with
    | boolean v => subst t; cases v <;> exact ⟨.truth, by constructor⟩
    | integer v => subst t; exact ⟨.truth, .literal _⟩
    | this => subst t; exact ⟨.truth, .var _⟩
    | extent x => subst t; exact ⟨.truth, hl.1 x⟩
    | map e => subst t; exact ⟨.truth, hl.2 e⟩
    | var pos =>
      cases t with
      | collection k => exact ⟨.truth, .var pos⟩
      | boolean | integer =>
        cases hp : Γ[pos]? <;> simp [Syntax.Typed, hp] at ht
    | and a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, vc⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      exact ⟨.conj da dc, .conj va vc⟩
    | not a =>
      obtain ⟨rfl, ha⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      exact ⟨da, .neg va⟩
    | equal k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, vc⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      exact ⟨.conj da dc, equal_built k _ _ va vc⟩
    | less a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, _⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, _⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      exact ⟨.conj da dc, .compare _ _ _⟩
    | arithmetic op a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, vc⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      cases op <;> exact ⟨.conj da dc, by constructor <;> assumption⟩
    | integerOf x a =>
      obtain ⟨rfl, _, ha⟩ := ht
      obtain ⟨da, _⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      exact ⟨.conj da (.conj (.mult _ _) (.subset _ _)), .scalar _ _ _ _⟩
    | cardinality k a =>
      obtain ⟨rfl, ha⟩ := ht
      obtain ⟨da, _⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      exact ⟨da, .count _⟩
    | setOp op k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, vc⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      cases op <;> exact ⟨.conj da dc, by constructor <;> assumption⟩
    | subset k a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, _⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, _⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      exact ⟨.conj da dc, .subset _ _⟩
    | image x y a c | join x y z a c =>
      obtain ⟨rfl, ha, hc⟩ := ht
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      obtain ⟨dc, vc⟩ := ih c (by simp only [Syntax.depth] at h; omega) hc
      exact ⟨.conj da dc, .join va vc⟩
    | widenObjects x y p a =>
      obtain ⟨rfl, _, ha⟩ := ht
      exact ih a (by simp only [Syntax.depth] at h; omega) ha
    | widenRelation x y x' y' p q a =>
      obtain ⟨rfl, _, _, ha⟩ := ht
      exact ih a (by simp only [Syntax.depth] at h; omega) ha
    | all binder d a =>
      obtain ⟨rfl, _, hd, ha⟩ := ht
      obtain ⟨dd, _⟩ := ih d (by simp only [Syntax.depth] at h; omega) hd
      obtain ⟨da, va⟩ := ih a (by simp only [Syntax.depth] at h; omega) ha
      exact ⟨.conj dd (.all _ da), .all _ va⟩
    | located _ a => exact ih a (by simp only [Syntax.depth] at h; omega) ht.2

end ClaferCompiler.Correctness.ExpressionConstruction
