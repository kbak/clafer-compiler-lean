module

public import ClaferCompiler.IR.ExprBounds
public import ClaferCompiler.Backend.Alloy.Semantics

/-! [impl->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Expressions
open IR.Expr

/-- Closed target relations retain support positions; repeated source identities
may intentionally select the same relation. Scalar owners identify real fields. -/
structure Layout (n m : Nat) where
  extents : Vector Rel n
  maps : Vector Rel m
  scalarOwners : Vector Nat n

abbrev ValueCode : Ty n → Type
  | .boolean => Formula
  | .integer => Integer
  | .collection _ => Rel

/-- Definedness is generated separately. Internal numeric fallbacks are never
interpreted as the meaning of an undefined source expression. -/
structure Code (t : Ty n) where
  defined : Formula
  value : ValueCode t

def equalCode (t : Ty n) : ValueCode t → ValueCode t → Formula :=
  match t with
  | .boolean => fun a b => .conj (.implies a b) (.implies b a)
  | .integer => .compare .eq
  | .collection _ => Formula.equal

def encodeAt (s : Support n m) (l : Layout n m) (b : IR.Expr.Bounds n) :
    (fuel : Nat) → (e : Syntax n m) → e.depth < fuel →
    {Γ : List (Local n)} → {t : Ty n} → e.Typed s Γ t → Code t :=
  Nat.rec (motive := fun fuel => (e : Syntax n m) → e.depth < fuel →
    {Γ : List (Local n)} → {t : Ty n} → e.Typed s Γ t → Code t)
    (fun _ h => False.elim (Nat.not_lt_zero _ h))
    (fun _ next e h Γ t ht => by
      cases e with
      | boolean v => subst t; exact ⟨.truth, if v then .truth else .falsity⟩
      | integer v => subst t; exact ⟨.truth, .literal v⟩
      | this => subst t; exact ⟨.truth, .var Γ.length⟩
      | extent x => subst t; exact ⟨.truth, l.extents[x]⟩
      | map e => subst t; exact ⟨.truth, l.maps[e]⟩
      | var pos =>
        cases t with
        | collection k => exact ⟨.truth, .var pos⟩
        | boolean | integer =>
          cases hp : Γ[pos]? <;> simp [Syntax.Typed, hp] at ht
      | and a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, .conj a.value c.value⟩
      | not a =>
        obtain ⟨rfl, ha⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨a.defined, .neg a.value⟩
      | equal k a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, equalCode k a.value c.value⟩
      | less a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, .compare .lt a.value c.value⟩
      | arithmetic op a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, match op with
          | .add => .add a.value c.value | .subtract => .subtract a.value c.value⟩
      | integerOf x a =>
        obtain ⟨rfl, _, ha⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨.conj a.defined (.conj (.mult .one a.value)
          (.subset a.value (.sig l.scalarOwners[x]))),
          .scalar l.scalarOwners[x] b.integers[x].lower b.integers[x].upper a.value⟩
      | cardinality k a =>
        obtain ⟨rfl, ha⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨a.defined, .count a.value⟩
      | setOp op k a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, match op with
          | .union => .union a.value c.value | .difference => .diff a.value c.value
          | .intersection => .inter a.value c.value⟩
      | subset k a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, .subset a.value c.value⟩
      | image x y a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, .join a.value c.value⟩
      | join x y z a c =>
        obtain ⟨rfl, ha, hc⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        let c := next c (by simp only [Syntax.depth] at h; omega) hc
        exact ⟨.conj a.defined c.defined, .join a.value c.value⟩
      | widenObjects x y p a =>
        obtain ⟨rfl, _, ha⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨a.defined, a.value⟩
      | widenRelation x y x' y' p q a =>
        obtain ⟨rfl, _, _, ha⟩ := ht
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨a.defined, a.value⟩
      | all binder d a =>
        obtain ⟨rfl, _, hd, ha⟩ := ht
        let d := next d (by simp only [Syntax.depth] at h; omega) hd
        let a := next a (by simp only [Syntax.depth] at h; omega) ha
        exact ⟨.conj d.defined (.all d.value a.defined), .all d.value a.value⟩
      | located _ a => exact next a (by simp only [Syntax.depth] at h; omega) ht.2)

def encode {s : Support n m} {b : IR.Expr.Bounds n} {Γ : List (Local n)} {t : Ty n}
    (l : Layout n m) (a : Admitted s b Γ t) : Code t :=
  encodeAt s l b a.checked.term.budget a.checked.term.raw a.checked.term.bound a.checked.typed

/-- Hard constraints demand both definedness and truth, including under negation
and at every actual owner object. -/
def Code.holds (c : Code (.boolean : Ty n)) : Formula := .conj c.defined c.value

def attach (owners : Rel) (c : Code (.boolean : Ty n)) : Formula := .all owners c.holds

end ClaferCompiler.Backend.Alloy.Expressions
