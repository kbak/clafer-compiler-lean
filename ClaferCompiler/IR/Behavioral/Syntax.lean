module

public import ClaferCompiler.IR.Structural

@[expose] public section
namespace ClaferCompiler.IR.Behavioral

inductive Step (k : Nat) where
  | parent
  | child (declaration : Fin k)
  | deref (declaration : Fin k)
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-ir~1]
/-- Indices are resolved table/lexical positions, never display names. -/
inductive SetExpr (k n : Nat) where
  | empty | this | root
  | var (index : Fin n)
  | extent (declaration : Fin k)
  | union (a b : SetExpr k n)
  | inter (a b : SetExpr k n)
  | diff (a b : SetExpr k n)
  | step (s : Step k) (a : SetExpr k n)
  | thisStep (s : Step k)

inductive Atom (k n : Nat) where
  | inhabited (a : SetExpr k n)
  | equal (a b : SetExpr k n)
  | subset (a b : SetExpr k n)

inductive Quantifier where
  | all | some | no | one | lone
  deriving DecidableEq, Repr

-- [impl->req~compiler-behavioral-ir~1]
/-- Atom/domain families distinguish total-set admission from the full partial
primitive language. A formula alone never certifies atom definedness. -/
inductive FormulaF (A D : Nat → Type) : Nat → Type where
  | truth : FormulaF A D n
  | atom (a : A n) : FormulaF A D n
  | not (a : FormulaF A D n) : FormulaF A D n
  | and (a b : FormulaF A D n) : FormulaF A D n
  | or (a b : FormulaF A D n) : FormulaF A D n
  | implies (a b : FormulaF A D n) : FormulaF A D n
  | iff (a b : FormulaF A D n) : FormulaF A D n
  | xor (a b : FormulaF A D n) : FormulaF A D n
  | ite (c a b : FormulaF A D n) : FormulaF A D n
  | next (a : FormulaF A D n) : FormulaF A D n
  | eventually (a : FormulaF A D n) : FormulaF A D n
  | always (a : FormulaF A D n) : FormulaF A D n
  | strongUntil (a b : FormulaF A D n) : FormulaF A D n
  | weakUntil (a b : FormulaF A D n) : FormulaF A D n
  | initially (a : FormulaF A D n) : FormulaF A D n
  | finally (a : FormulaF A D n) : FormulaF A D n
  | quant (q : Quantifier) (domain : D n) (body : FormulaF A D (n + 1)) : FormulaF A D n
  | letSet (value : D n) (body : FormulaF A D (n + 1)) : FormulaF A D n

-- [impl->req~compiler-behavioral-interpretation~1]
/-- Executable T2 normalization. Counting barriers keep the original body.
Constructor equations adapted from Clafer/Behavioral/Normalization.lean at
27a5bbe86657edab00980da57b2f86221f92a5f1 (MIT, copyright 2026 Kacper Bak).
Independent signed denotation and lifetime semantics remain upstream. -/
def FormulaF.normalizeStep {A D : Nat → Type} [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)] (fuel : Nat)
    (next : {n : Nat} → (a : FormulaF A D n) → sizeOf a < fuel → Bool → FormulaF A D n)
    {n} (a : FormulaF A D n) : sizeOf a < fuel + 1 → Bool → FormulaF A D n :=
  match a with
      | .truth => fun _h s => if s then .truth else .not .truth
      | .atom a => fun _h s => if s then .atom a else .not (.atom a)
      | .not a => fun _h s => next a (by simp_all; omega) (!s)
      | .and a b => fun _h s => if s then .and (next a (by simp_all; omega) true) (next b (by simp_all; omega) true)
          else .or (next a (by simp_all; omega) false) (next b (by simp_all; omega) false)
      | .or a b => fun _h s => if s then .or (next a (by simp_all; omega) true) (next b (by simp_all; omega) true)
          else .and (next a (by simp_all; omega) false) (next b (by simp_all; omega) false)
      | .implies a b => fun _h s => if s then .or (next a (by simp_all; omega) false) (next b (by simp_all; omega) true)
          else .and (next a (by simp_all; omega) true) (next b (by simp_all; omega) false)
      | .iff a b => fun _h s => if s then
          .and (.or (next a (by simp_all; omega) false) (next b (by simp_all; omega) true)) (.or (next b (by simp_all; omega) false) (next a (by simp_all; omega) true))
          else .or (.and (next a (by simp_all; omega) true) (next b (by simp_all; omega) false)) (.and (next b (by simp_all; omega) true) (next a (by simp_all; omega) false))
      | .xor a b => fun _h s => if s then
          .or (.and (next a (by simp_all; omega) true) (next b (by simp_all; omega) false)) (.and (next a (by simp_all; omega) false) (next b (by simp_all; omega) true))
          else .and (.or (next a (by simp_all; omega) false) (next b (by simp_all; omega) true)) (.or (next a (by simp_all; omega) true) (next b (by simp_all; omega) false))
      | .ite c a b => fun _h s => if s then
          .and (.or (next c (by simp_all; omega) false) (next a (by simp_all; omega) true)) (.or (next c (by simp_all; omega) true) (next b (by simp_all; omega) true))
          else .or (.and (next c (by simp_all; omega) true) (next a (by simp_all; omega) false)) (.and (next c (by simp_all; omega) false) (next b (by simp_all; omega) false))
      | .next a => fun _h s => .next (next a (by simp_all; omega) s)
      | .eventually a => fun _h s => if s then .eventually (next a (by simp_all; omega) true) else .always (next a (by simp_all; omega) false)
      | .always a => fun _h s => if s then .always (next a (by simp_all; omega) true) else .eventually (next a (by simp_all; omega) false)
      | .strongUntil a b => fun _h s => if s then .strongUntil (next a (by simp_all; omega) true) (next b (by simp_all; omega) true)
          else .weakUntil (next b (by simp_all; omega) false) (.and (next a (by simp_all; omega) false) (next b (by simp_all; omega) false))
      | .weakUntil a b => fun _h s => if s then .weakUntil (next a (by simp_all; omega) true) (next b (by simp_all; omega) true)
          else .strongUntil (next b (by simp_all; omega) false) (.and (next a (by simp_all; omega) false) (next b (by simp_all; omega) false))
      | .initially a => fun _h s => .initially (next a (by simp_all; omega) s)
      | .finally a => fun _h s => .finally (next a (by simp_all; omega) s)
      | .quant .all d a => fun _h s => if s then .quant .all d (next a (by simp_all; omega) true)
          else .quant .some d (next a (by simp_all; omega) false)
      | .quant .some d a => fun _h s => if s then .quant .some d (next a (by simp_all; omega) true)
          else .quant .all d (next a (by simp_all; omega) false)
      | .quant .no d a => fun _h s => if s then .quant .all d (next a (by simp_all; omega) false)
          else .quant .some d (next a (by simp_all; omega) true)
      | .quant .one d a => fun _h s => if s then .quant .one d a else .not (.quant .one d a)
      | .quant .lone d a => fun _h s => if s then .quant .lone d a else .not (.quant .lone d a)
      | .letSet d a => fun _h s => .letSet d (next a (by simp_all; omega) s)

def FormulaF.normalizeAt {A D : Nat → Type} [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)] : (fuel : Nat) → {n : Nat} → (a : FormulaF A D n) →
    sizeOf a < fuel → Bool → FormulaF A D n :=
  Nat.rec (motive := fun fuel => {n : Nat} → (a : FormulaF A D n) →
      sizeOf a < fuel → Bool → FormulaF A D n)
    (fun {_} _ h => False.elim (Nat.not_lt_zero _ h)) FormulaF.normalizeStep

variable {A D : Nat → Type} [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)]

theorem FormulaF.normalizeAt_succ (fuel : Nat) (a : FormulaF A D n)
    (h : sizeOf a < fuel + 1) (s : Bool) :
    normalizeAt (fuel + 1) a h s = normalizeStep fuel (normalizeAt fuel) a h s := rfl

/-- The budget is traversal storage, never a language or observation cutoff. -/
def FormulaF.normalize (a : FormulaF A D n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) : FormulaF A D n := normalizeAt fuel a enough s

/-- Original total-set fragment; partial atoms cannot enter its admission API. -/
abbrev Formula (k : Nat) := FormulaF (Atom k) (SetExpr k)

namespace Formula
abbrev truth : Formula k n := FormulaF.truth
abbrev atom (a : Atom k n) : Formula k n := FormulaF.atom a
abbrev not (a : Formula k n) : Formula k n := FormulaF.not a
abbrev next (a : Formula k n) : Formula k n := FormulaF.next a
abbrev eventually (a : Formula k n) : Formula k n := FormulaF.eventually a
abbrev always (a : Formula k n) : Formula k n := FormulaF.always a
abbrev initially (a : Formula k n) : Formula k n := FormulaF.initially a
abbrev «finally» (a : Formula k n) : Formula k n := FormulaF.finally a
abbrev and (a b : Formula k n) : Formula k n := FormulaF.and a b
abbrev or (a b : Formula k n) : Formula k n := FormulaF.or a b
abbrev implies (a b : Formula k n) : Formula k n := FormulaF.implies a b
abbrev iff (a b : Formula k n) : Formula k n := FormulaF.iff a b
abbrev xor (a b : Formula k n) : Formula k n := FormulaF.xor a b
abbrev strongUntil (a b : Formula k n) : Formula k n := FormulaF.strongUntil a b
abbrev weakUntil (a b : Formula k n) : Formula k n := FormulaF.weakUntil a b
abbrev ite (c a b : Formula k n) : Formula k n := FormulaF.ite c a b
abbrev quant (q : Quantifier) (d : SetExpr k n) (a : Formula k (n + 1)) : Formula k n := FormulaF.quant q d a
abbrev letSet (d : SetExpr k n) (a : Formula k (n + 1)) : Formula k n := FormulaF.letSet d a

def normalizeStep {k} (fuel : Nat)
    (next : {n : Nat} → (a : Formula k n) → sizeOf a < fuel → Bool → Formula k n)
    {n} (a : Formula k n) (h : sizeOf a < fuel + 1) (s : Bool) : Formula k n :=
  FormulaF.normalizeStep fuel next a h s

def normalizeAt {k} (fuel : Nat) {n} (a : Formula k n)
    (h : sizeOf a < fuel) (s : Bool) : Formula k n := FormulaF.normalizeAt fuel a h s

theorem normalizeAt_succ (fuel : Nat) (a : Formula k n)
    (h : sizeOf a < fuel + 1) (s : Bool) :
    normalizeAt (fuel + 1) a h s = normalizeStep fuel (normalizeAt fuel) a h s := rfl

def normalize (a : Formula k n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) : Formula k n := FormulaF.normalize a s fuel enough
end Formula

end ClaferCompiler.IR.Behavioral
