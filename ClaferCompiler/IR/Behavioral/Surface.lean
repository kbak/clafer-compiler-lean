module

public import ClaferCompiler.IR.Behavioral.Syntax

/-! Executable surface reductions. Constructor equations adapted from
Clafer/Behavioral/{Patterns,Transitions,Modifiers}.lean at
6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4 (MIT, copyright 2026 Kacper Bak).
Independent interval, sequence and modifier meanings remain upstream.
-/

@[expose] public section
namespace ClaferCompiler.IR.Behavioral.Surface
open IR.Behavioral

namespace Patterns
inductive Scope (F : Type) where
  | suffix | before (r : F) | after (q : F) | between (q r : F) | afterUntil (q r : F)

inductive Pattern (F : Type) where
  | never (p : F) | sometime (p : F) | lonce (p : F) | always (p : F)
  | precede (s p : F) | follow (s p : F)

-- [impl->req~compiler-behavioral-elaboration~1]
def expand (pattern : Pattern (FormulaF A D n)) (scope : Scope (FormulaF A D n)) : FormulaF A D n :=
  let g := FormulaF.always
  let f := FormulaF.eventually
  let u := FormulaF.strongUntil
  let w := FormulaF.weakUntil
  let no := FormulaF.not
  let a := FormulaF.and
  let o := FormulaF.or
  let imp := FormulaF.implies
  match pattern, scope with
  | .never p, .suffix => g (no p)
  | .never p, .before r => imp (f r) (u (no p) r)
  | .never p, .after q => g (imp q (g (no p)))
  | .never p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) r))
  | .never p, .afterUntil q r => g (imp (a q (no r)) (w (no p) r))
  | .sometime p, .suffix => f p
  | .sometime p, .before r => w (no r) (a p (no r))
  | .sometime p, .after q => o (g (no q)) (f (a q (f p)))
  | .sometime p, .between q r => g (imp (a q (no r)) (w (no r) (a p (no r))))
  | .sometime p, .afterUntil q r => g (imp (a q (no r)) (u (no r) (a p (no r))))
  | .lonce p, .suffix => w (no p) (w p (g (no p)))
  | .lonce p, .before r => imp (f r) (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r)))))
  | .lonce p, .after q => imp (f q) (u (no q) (a q (w (no p) (w p (g (no p))))))
  | .lonce p, .between q r => g (imp (a q (f r))
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o r (u (no p) r))))))
  | .lonce p, .afterUntil q r => g (imp q
      (u (a (no p) (no r)) (o r (u (a p (no r)) (o (o r (w (no p) r)) (g p))))))
  | .always p, .suffix => g p
  | .always p, .before r => imp (f r) (u p r)
  | .always p, .after q => g (imp q (g p))
  | .always p, .between q r => g (imp (a (a q (no r)) (f r)) (u p r))
  | .always p, .afterUntil q r => g (imp (a q (no r)) (w p r))
  | .precede s p, .suffix => w (no p) s
  | .precede s p, .before r => imp (f r) (u (no p) (o s r))
  | .precede s p, .after q => imp (f q) (u (no q) (a q (w (no p) s)))
  | .precede s p, .between q r => g (imp (a (a q (no r)) (f r)) (u (no p) (o s r)))
  | .precede s p, .afterUntil q r => g (imp (a q (no r)) (w (no p) (o s r)))
  | .follow s p, .suffix => g (imp p (f s))
  | .follow s p, .before r => imp (f r) (u (imp p (u (no r) (a s (no r)))) r)
  | .follow s p, .after q => g (imp q (g (imp p (f s))))
  | .follow s p, .between q r => g (imp (a (a q (no r)) (f r))
      (u (imp p (u (no r) (a s (no r)))) r))
  | .follow s p, .afterUntil q r => g (imp (a q (no r)) (w (imp p (u (no r) (a s (no r)))) r))

end Patterns

namespace Transitions
inductive Arrow where
  | immediate | eventual
  deriving DecidableEq, Repr

structure LinkF (A D : Nat → Type) (n : Nat) where
  source : FormulaF A D n
  guard : Option (FormulaF A D n)
  arrow : Arrow

structure ChainF (A D : Nat → Type) (n : Nat) where
  links : List (LinkF A D n)
  target : FormulaF A D n

abbrev Link (k n : Nat) := LinkF (Atom k) (SetExpr k) n
abbrev Chain (k n : Nat) := ChainF (Atom k) (SetExpr k) n

def precondition (link : LinkF A D n) : FormulaF A D n :=
  match link.guard with
  | none => link.source
  | some guard => .and link.source guard

def step (context : FormulaF A D n) (link : LinkF A D n) (target : FormulaF A D n) : FormulaF A D n :=
  match link.arrow with
  | .immediate => .next target
  | .eventual => .strongUntil (.and context link.source) target

-- [impl->req~compiler-behavioral-elaboration~1]
def sequence (context : FormulaF A D n) (chain : ChainF A D n) : FormulaF A D n :=
  chain.links.foldr (fun link rest => .and (precondition link) (step context link rest)) chain.target

def expand (context : FormulaF A D n) (chain : ChainF A D n) : FormulaF A D n :=
  match chain.links with
  | [] => chain.target
  | link :: rest => .implies (precondition link) (step context link (sequence context ⟨rest, chain.target⟩))

def presence : Formula k n := .atom (.inhabited .this)

def declaration (guard : Option (Formula k n)) (arrow : Arrow) (rest : Chain k n) : Formula k n :=
  expand presence ⟨⟨presence, guard, arrow⟩ :: rest.links, rest.target⟩
end Transitions

namespace Modifiers
inductive Modifier where
  | initial | final | finalref | finaltarget
  deriving DecidableEq, BEq, Repr

inductive View (k : Nat) where
  | heads (d : Fin k) | reference (d : Fin k) | targets (d : Fin k)

inductive Placement (k : Nat) where
  | all | parents (d : Fin k) | heads (d : Fin k)

def View.expression (v : View k) : SetExpr k n :=
  match v with
  | .heads d => .thisStep (.child d)
  | .reference d => .thisStep (.deref d)
  | .targets d => .step (.deref d) (.thisStep (.child d))

def initialExpansion (d : Fin k) : Formula k 0 :=
  .initially (.atom (.inhabited (.thisStep (.child d))))

def stabilityExpansion (v : View k) : Formula k 0 :=
  .letSet v.expression (.next (.implies (.atom (.inhabited .this))
    (.atom (.equal (.var 0) v.expression))))

-- [impl->req~compiler-behavioral-elaboration~1]
def expand (d : Fin k) : Modifier → List (Placement k × Formula k 0)
  | .initial => [(.parents d, initialExpansion d)]
  | .final => [(.all, stabilityExpansion (.heads d)), (.heads d, stabilityExpansion (.reference d))]
  | .finalref => [(.heads d, stabilityExpansion (.reference d))]
  | .finaltarget => [(.all, stabilityExpansion (.targets d))]
end Modifiers
end ClaferCompiler.IR.Behavioral.Surface
