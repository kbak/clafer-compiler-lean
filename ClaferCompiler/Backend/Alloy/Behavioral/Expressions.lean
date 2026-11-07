module

public import ClaferCompiler.Backend.Alloy.Behavioral.Layout

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral

abbrev TRel := Temporal.Rel
abbrev TFormula := Temporal.Formula

def shift (amount : Nat) (r : TRel) : TRel :=
  ⟨r.code.map fun op => match op with
    | .var i => .var (i + amount)
    | other => other⟩

/-- Captures are relations built from frozen singleton variables. `aliases`
covers the static object pool; duplicates are allowed for bounded padding. -/
structure Context (n : Nat) where
  this : TRel
  lookup : Fin n → TRel
  aliases : List TRel

def Context.shift (c : Context n) (amount : Nat) : Context n :=
  ⟨Behavioral.shift amount c.this, fun i => Behavioral.shift amount (c.lookup i), c.aliases.map (Behavioral.shift amount)⟩

def Context.push (c : Context n) (value : TRel) : Context (n + 1) :=
  ⟨c.this, Fin.cases value c.lookup, c.aliases⟩

-- [impl->req~compiler-behavioral-encoding~1]
def setStep (v : IR.Structural.Layout k) (c : Context n) (fuel : Nat)
    (recur : (a : IR.Behavioral.SetExpr k n) → sizeOf a < fuel → TRel)
    (a : IR.Behavioral.SetExpr k n) : sizeOf a < fuel + 1 → TRel :=
  match a with
  | .empty => fun _ => .empty .unary
  | .this => fun _ => .inter c.this (live v)
  | .root => fun _ => root v
  | .var i => fun _ => c.lookup i
  | .extent d => fun _ => head v d
  | .union a b => fun h => .union (recur a (by (try simp_all); omega)) (recur b (by (try simp_all); omega))
  | .inter a b => fun h => .inter (recur a (by (try simp_all); omega)) (recur b (by (try simp_all); omega))
  | .diff a b => fun h => .diff (recur a (by (try simp_all); omega)) (recur b (by (try simp_all); omega))
  | .step s a => fun h => .join (recur a (by (try simp_all); omega)) (step v s)
  | .thisStep s => fun _ => .join c.this (step v s)

def setAt (v : IR.Structural.Layout k) (c : Context n) :
    (fuel : Nat) → (a : IR.Behavioral.SetExpr k n) → sizeOf a < fuel → TRel :=
  Nat.rec (motive := fun fuel => (a : IR.Behavioral.SetExpr k n) → sizeOf a < fuel → TRel)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (setStep v c)

def atom (v : IR.Structural.Layout k) (c : Context n)
    (a : IR.Behavioral.Atom k n) (fuel : Nat) (enough : sizeOf a < fuel) : TFormula :=
  match a with
  | .inhabited a => .mult .some (setAt v c fuel a (by (try simp_all); omega))
  | .equal a b => .equal (setAt v c fuel a (by (try simp_all); omega))
      (setAt v c fuel b (by (try simp_all); omega))
  | .subset a b => .subset (setAt v c fuel a (by (try simp_all); omega))
      (setAt v c fuel b (by (try simp_all); omega))

def present (v : IR.Structural.Layout k) (c : Context n) : TFormula :=
  .mult .some (.inter c.this (live v))

def parentPresent (v : IR.Structural.Layout k) (c : Context n) : TFormula :=
  .binary .disj (.subset c.this (root v))
    (.mult .some (.join c.this (step v .parent)))

/-- The classical body is retained separately for one/lone counting barriers.
The two source signs are not classical complements after cancellation. -/
structure Translation where
  raw : TFormula
  positive : TFormula
  negative : TFormula

def Translation.map (f : TFormula → TFormula) (a : Translation) : Translation :=
  ⟨f a.raw, f a.positive, f a.negative⟩

def Translation.atomic (a : TFormula) : Translation := ⟨a, a, .unary .neg a⟩

/-- Freeze a current collection by membership cases over a finite covering
enumeration of static identities. Guards run now; leaves use only captured atoms.
Ordinary Alloy let substitution would incorrectly re-evaluate mutable sets. -/
def freezeChoice (guard : TFormula) (yes no : Translation) : Translation :=
  let choose := fun a b => Temporal.Formula.binary .disj (.binary .conj guard a)
    (.binary .conj (.unary .neg guard) b)
  ⟨choose yes.raw no.raw, choose yes.positive no.positive,
    choose yes.negative no.negative⟩

def freezeFrom (aliases : List TRel) (value : TRel)
    (body : TRel → Translation) (captured : TRel) : Translation :=
  aliases.foldr (fun x next captured =>
    freezeChoice (.subset x value) (next (.union captured x)) (next captured)) body captured

def freeze (aliases : List TRel) (value : TRel) (body : TRel → Translation) : Translation :=
  freezeFrom aliases value body (.empty .unary)

def conjunction (a b : Translation) : Translation :=
  ⟨.binary .conj a.raw b.raw, .binary .conj a.positive b.positive,
    .binary .disj a.negative b.negative⟩

def disjunction (a b : Translation) : Translation :=
  ⟨.binary .disj a.raw b.raw, .binary .disj a.positive b.positive,
    .binary .conj a.negative b.negative⟩

def negation (a : Translation) : Translation :=
  ⟨.unary .neg a.raw, a.negative, a.positive⟩

def implication (a b : Translation) : Translation := disjunction (negation a) b
def equivalence (a b : Translation) : Translation :=
  conjunction (implication a b) (implication b a)

-- [impl->req~compiler-behavioral-encoding~1]
/-- Translate every constructor at both source signs and at the raw barrier.
The traversal budget is erased evidence of size, never a language cutoff. -/
def formulaStep (v : IR.Structural.Layout k) (fuel : Nat)
    (recur : {n : Nat} → Context n → (a : IR.Behavioral.Formula k n) →
      sizeOf a < fuel → Translation)
    {n : Nat} (c : Context n) (a : IR.Behavioral.Formula k n) :
    sizeOf a < fuel + 1 → Translation :=
  match a with
  | .truth => fun _ => Translation.atomic .truth
  | .atom a => fun h => Translation.atomic (atom v c a fuel (by simp only [IR.Behavioral.Formula.atom.sizeOf_spec] at h; omega))
  | .not a => fun h => negation (recur c a (by simp only [IR.Behavioral.Formula.not.sizeOf_spec] at h; omega))
  | .and a b => fun h => conjunction (recur c a (by simp only [IR.Behavioral.Formula.and.sizeOf_spec] at h; omega)) (recur c b (by simp only [IR.Behavioral.Formula.and.sizeOf_spec] at h; omega))
  | .or a b => fun h => disjunction (recur c a (by simp only [IR.Behavioral.Formula.or.sizeOf_spec] at h; omega)) (recur c b (by simp only [IR.Behavioral.Formula.or.sizeOf_spec] at h; omega))
  | .implies a b => fun h => implication (recur c a (by simp only [IR.Behavioral.Formula.implies.sizeOf_spec] at h; omega)) (recur c b (by simp only [IR.Behavioral.Formula.implies.sizeOf_spec] at h; omega))
  | .iff a b => fun h => equivalence (recur c a (by simp only [IR.Behavioral.Formula.iff.sizeOf_spec] at h; omega)) (recur c b (by simp only [IR.Behavioral.Formula.iff.sizeOf_spec] at h; omega))
  | .xor a b => fun h => negation (equivalence (recur c a (by simp only [IR.Behavioral.Formula.xor.sizeOf_spec] at h; omega)) (recur c b (by simp only [IR.Behavioral.Formula.xor.sizeOf_spec] at h; omega)))
  | .ite cond a b => fun h =>
      let cond := recur c cond (by simp only [IR.Behavioral.Formula.ite.sizeOf_spec] at h; omega)
      conjunction (implication cond (recur c a (by simp only [IR.Behavioral.Formula.ite.sizeOf_spec] at h; omega)))
        (implication (negation cond) (recur c b (by simp only [IR.Behavioral.Formula.ite.sizeOf_spec] at h; omega)))
  | .next a => fun h => (recur c a (by simp only [IR.Behavioral.Formula.next.sizeOf_spec] at h; omega)).map (next (parentPresent v c))
  | .eventually a => fun h =>
      let a := recur c a (by simp only [IR.Behavioral.Formula.eventually.sizeOf_spec] at h; omega)
      let p := parentPresent v c
      ⟨eventually p a.raw, eventually p a.positive, always p a.negative⟩
  | .always a => fun h =>
      let a := recur c a (by simp only [IR.Behavioral.Formula.always.sizeOf_spec] at h; omega)
      let p := parentPresent v c
      ⟨always p a.raw, always p a.positive, eventually p a.negative⟩
  | .strongUntil a b => fun h =>
      let a := recur c a (by simp only [IR.Behavioral.Formula.strongUntil.sizeOf_spec] at h; omega)
      let b := recur c b (by simp only [IR.Behavioral.Formula.strongUntil.sizeOf_spec] at h; omega)
      let p := parentPresent v c
      ⟨strongUntil p a.raw b.raw, strongUntil p a.positive b.positive,
        weakUntil p b.negative (.binary .conj a.negative b.negative)⟩
  | .weakUntil a b => fun h =>
      let a := recur c a (by simp only [IR.Behavioral.Formula.weakUntil.sizeOf_spec] at h; omega)
      let b := recur c b (by simp only [IR.Behavioral.Formula.weakUntil.sizeOf_spec] at h; omega)
      let p := parentPresent v c
      ⟨weakUntil p a.raw b.raw, weakUntil p a.positive b.positive,
        strongUntil p b.negative (.binary .conj a.negative b.negative)⟩
  | .initially a => fun h => (recur c a (by simp only [IR.Behavioral.Formula.initially.sizeOf_spec] at h; omega)).map (initially (present v c))
  | .finally a => fun h => (recur c a (by simp only [IR.Behavioral.Formula.finally.sizeOf_spec] at h; omega)).map (atEnd (present v c))
  | .letSet d a => fun h =>
      freeze c.aliases (setAt v c fuel d (by simp only [IR.Behavioral.Formula.letSet.sizeOf_spec] at h; omega))
        (fun value => recur (c.push value) a (by simp only [IR.Behavioral.Formula.letSet.sizeOf_spec] at h; omega))
  | .quant q d a => fun h =>
      let domain := setAt v c fuel d (by simp only [IR.Behavioral.Formula.quant.sizeOf_spec] at h; omega)
      let one := recur ((c.shift 1).push (.var 0)) a (by simp only [IR.Behavioral.Formula.quant.sizeOf_spec] at h; omega)
      match q with
      | .all => ⟨.all domain one.raw, .all domain one.positive, .exists_ domain one.negative⟩
      | .some => ⟨.exists_ domain one.raw, .exists_ domain one.positive, .all domain one.negative⟩
      | .no => ⟨.all domain (.unary .neg one.raw), .all domain one.negative,
          .exists_ domain one.positive⟩
      | .one | .lone =>
          let two := recur ((c.shift 2).push (.var 0)) a (by simp only [IR.Behavioral.Formula.quant.sizeOf_spec] at h; omega)
          let unique := Temporal.Formula.all (shift 1 domain)
            (.binary .implies two.raw (.equal (.var 0) (.var 1)))
          let counted := if q == .one then
            Temporal.Formula.exists_ domain (.binary .conj one.raw unique)
            else Temporal.Formula.all domain (.binary .implies one.raw unique)
          Translation.atomic counted

def formulaAt (v : IR.Structural.Layout k) : (fuel : Nat) → {n : Nat} →
    Context n → (a : IR.Behavioral.Formula k n) → sizeOf a < fuel → Translation :=
  Nat.rec (motive := fun fuel => {n : Nat} → Context n →
      (a : IR.Behavioral.Formula k n) → sizeOf a < fuel → Translation)
    (fun _ _ h => False.elim (Nat.not_lt_zero _ h)) (formulaStep v)

end ClaferCompiler.Backend.Alloy.Behavioral
