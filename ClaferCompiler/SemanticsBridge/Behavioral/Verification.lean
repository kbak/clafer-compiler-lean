module

public import ClaferCompiler.SemanticsBridge.Behavioral.Trace
public import Clafer.Behavioral.Verification

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Verification
open IR.Behavioral
namespace U
abbrev SetExpr := Clafer.Behavioral.SetExpr
abbrev SetAtom := Clafer.Behavioral.SetAtom
abbrev Core := Clafer.Behavioral.Core
end U

def toStep : Step k → Clafer.Behavioral.Step (Fin k)
  | .parent => .parent | .child d => .child d | .deref d => .deref d

theorem toStep_eq (s : Step k) : toStep s = Behavioral.step s := by
  cases s <;> rfl

def toQuantifier : Quantifier → Clafer.Behavioral.Quantifier
  | .all => .all | .some => .some | .no => .no | .one => .one | .lone => .lone

def toSetStep (go : SetExpr k n → U.SetExpr (Fin k) n) (a : SetExpr k n) : U.SetExpr (Fin k) n :=
  match a with
      | .empty => .empty | .this => .this | .root => .root
      | .var v => .var v | .extent d => .extent d
      | .union a b => .union (go a) (go b)
      | .inter a b => .inter (go a) (go b)
      | .diff a b => .diff (go a) (go b)
      | .step s a => .step (toStep s) (go a)
      | .thisStep s => .thisStep (toStep s)

-- [impl->req~compiler-temporal-comparison~1]
/-- Reuse the upstream checked well-founded traversal pattern. -/
def toSet {k n} (a : SetExpr k n) : U.SetExpr (Fin k) n :=
  (measure (fun a : SetExpr k n => sizeOf a)).wf.fix
    (C := fun _ => U.SetExpr (Fin k) n)
    (fun a go => match a with
      | .empty => .empty | .this => .this | .root => .root
      | .var v => .var v | .extent d => .extent d
      | .union a b => .union (go a (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.union.sizeOf_spec]; omega)) (go b (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.union.sizeOf_spec]; omega))
      | .inter a b => .inter (go a (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.inter.sizeOf_spec]; omega)) (go b (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.inter.sizeOf_spec]; omega))
      | .diff a b => .diff (go a (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.diff.sizeOf_spec]; omega)) (go b (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.diff.sizeOf_spec]; omega))
      | .step s a => .step (toStep s) (go a (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.SetExpr.step.sizeOf_spec]; omega))
      | .thisStep s => .thisStep (toStep s)) a

theorem toSet_unfold (a : SetExpr k n) : toSet a = toSetStep toSet a := by
  unfold toSet
  rw [WellFounded.fix_eq]
  cases a <;> rfl

-- [proof->req~compiler-temporal-comparison~1]
theorem toSet_eq (a : SetExpr k n) : toSet a = Behavioral.setExpr a := by
  induction a <;> rw [toSet_unfold]
  all_goals simp_all only [toSetStep, Behavioral.setExpr, toStep_eq]

def toAtom : Atom k n → U.SetAtom (Fin k) n
  | .inhabited a => .inhabited (toSet a)
  | .equal a b => .equal (toSet a) (toSet b)
  | .subset a b => .subset (toSet a) (toSet b)

theorem toAtom_eq (a : Atom k n) : toAtom a = Behavioral.atom a := by
  cases a <;> simp [toAtom, Behavioral.atom, toSet_eq]

abbrev SourceCore (k : Nat) := U.Core (U.SetAtom (Fin k)) (U.SetExpr (Fin k))

def lowerStep (go : {n : Nat} → Formula k n → SourceCore k n)
    (a : Formula k n) : SourceCore k n :=
  match a with
      | .truth => .truth
      | .atom a => .atom (.source (toAtom a))
      | .not a => .not (go a)
      | .and a b => .and (go a) (go b)
      | .or a b => .or (go a) (go b)
      | .implies a b => .or (.not (go a)) (go b)
      | .iff a b => .and (.or (.not (go a)) (go b)) (.or (.not (go b)) (go a))
      | .xor a b => .not (.and (.or (.not (go a)) (go b)) (.or (.not (go b)) (go a)))
      | .ite c a b => .and (.or (.not (go c)) (go a)) (.or (.not (.not (go c))) (go b))
      | .next a => .next (.or (.not (.atom .parentPresent)) (go a))
      | .eventually a => .eventually (.or (.not (.atom .parentPresent)) (go a))
      | .always a => .weakUntil (.and (.atom .parentPresent) (go a)) (.not (.atom .parentPresent))
      | .strongUntil a b => .strongUntil (.and (.atom .parentPresent) (go a)) (.or (.not (.atom .parentPresent)) (go b))
      | .weakUntil a b => .or (.weakUntil (.and (.atom .parentPresent) (go a)) (.not (.atom .parentPresent))) (.strongUntil (.and (.atom .parentPresent) (go a)) (.or (.not (.atom .parentPresent)) (go b)))
      | .previous a => .previous (.and (.atom .parentPresent) (go a))
      | .weakPrevious a => .not (.previous (.and (.atom .parentPresent) (.not (go a))))
      | .once a => .since (.atom .parentPresent) (.and (.atom .parentPresent) (go a))
      | .historically a => .not (.since (.atom .parentPresent) (.and (.atom .parentPresent) (.not (go a))))
      | .since a b => .since (.and (.atom .parentPresent) (go a)) (.and (.atom .parentPresent) (go b))
      | .triggered a b => .not (.since (.and (.atom .parentPresent) (.not (go a))) (.and (.atom .parentPresent) (.not (go b))))
      | .initially a => .or (.not (.atom .starts)) (go a)
      | .finally a => .or (.not (.atom .ends)) (go a)
      | .quant q d a => .quant (toQuantifier q) (toSet d) (go a)
      | .letSet d a => .letSet (toSet d) (go a)

-- [impl->req~compiler-temporal-comparison~1]
/-- Constructor equations adapt upstream MIT Formula.lower; source meaning stays upstream. -/
def lower {k n} (a : Formula k n) : SourceCore k n :=
  (measure (fun p : (n : Nat) × Formula k n => sizeOf p.2)).wf.fix
    (C := fun (p : (n : Nat) × Formula k n) => SourceCore k p.1)
    (fun p go => match p with
      | ⟨_, .truth⟩ => .truth
      | ⟨_, .atom a⟩ => .atom (.source (toAtom a))
      | ⟨_, .not a⟩ => .not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.not.sizeOf_spec]; omega))
      | ⟨_, .and a b⟩ => .and (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.and.sizeOf_spec]; omega)) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.and.sizeOf_spec]; omega))
      | ⟨_, .or a b⟩ => .or (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.or.sizeOf_spec]; omega)) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.or.sizeOf_spec]; omega))
      | ⟨_, .implies a b⟩ => .or (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.implies.sizeOf_spec]; omega))) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.implies.sizeOf_spec]; omega))
      | ⟨_, .iff a b⟩ => .and (.or (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.iff.sizeOf_spec]; omega))) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.iff.sizeOf_spec]; omega))) (.or (.not (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.iff.sizeOf_spec]; omega))) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.iff.sizeOf_spec]; omega)))
      | ⟨_, .xor a b⟩ => .not (.and (.or (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.xor.sizeOf_spec]; omega))) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.xor.sizeOf_spec]; omega))) (.or (.not (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.xor.sizeOf_spec]; omega))) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.xor.sizeOf_spec]; omega))))
      | ⟨_, .ite c a b⟩ => .and (.or (.not (go ⟨_, c⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.ite.sizeOf_spec]; omega))) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.ite.sizeOf_spec]; omega))) (.or (.not (.not (go ⟨_, c⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.ite.sizeOf_spec]; omega)))) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.ite.sizeOf_spec]; omega)))
      | ⟨_, .next a⟩ => .next (.or (.not (.atom .parentPresent)) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.next.sizeOf_spec]; omega)))
      | ⟨_, .eventually a⟩ => .eventually (.or (.not (.atom .parentPresent)) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.eventually.sizeOf_spec]; omega)))
      | ⟨_, .always a⟩ => .weakUntil (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.always.sizeOf_spec]; omega))) (.not (.atom .parentPresent))
      | ⟨_, .strongUntil a b⟩ => .strongUntil (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.strongUntil.sizeOf_spec]; omega))) (.or (.not (.atom .parentPresent)) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.strongUntil.sizeOf_spec]; omega)))
      | ⟨_, .weakUntil a b⟩ => .or (.weakUntil (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.weakUntil.sizeOf_spec]; omega))) (.not (.atom .parentPresent))) (.strongUntil (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.weakUntil.sizeOf_spec]; omega))) (.or (.not (.atom .parentPresent)) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.weakUntil.sizeOf_spec]; omega))))
      | ⟨_, .previous a⟩ => .previous (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.previous.sizeOf_spec]; omega)))
      | ⟨_, .weakPrevious a⟩ => .not (.previous (.and (.atom .parentPresent) (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.weakPrevious.sizeOf_spec]; omega)))))
      | ⟨_, .once a⟩ => .since (.atom .parentPresent) (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.once.sizeOf_spec]; omega)))
      | ⟨_, .historically a⟩ => .not (.since (.atom .parentPresent) (.and (.atom .parentPresent) (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.historically.sizeOf_spec]; omega)))))
      | ⟨_, .since a b⟩ => .since (.and (.atom .parentPresent) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.since.sizeOf_spec]; omega))) (.and (.atom .parentPresent) (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.since.sizeOf_spec]; omega)))
      | ⟨_, .triggered a b⟩ => .not (.since (.and (.atom .parentPresent) (.not (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.triggered.sizeOf_spec]; omega)))) (.and (.atom .parentPresent) (.not (go ⟨_, b⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.triggered.sizeOf_spec]; omega)))))
      | ⟨_, .initially a⟩ => .or (.not (.atom .starts)) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.initially.sizeOf_spec]; omega))
      | ⟨_, .finally a⟩ => .or (.not (.atom .ends)) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.finally.sizeOf_spec]; omega))
      | ⟨_, .quant q d a⟩ => .quant (toQuantifier q) (toSet d) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.quant.sizeOf_spec]; omega))
      | ⟨_, .letSet d a⟩ => .letSet (toSet d) (go ⟨_, a⟩ (by change sizeOf _ < sizeOf _; simp only [IR.Behavioral.FormulaF.letSet.sizeOf_spec]; omega))) ⟨n, a⟩

theorem lower_unfold (a : Formula k n) : lower a = lowerStep lower a := by
  unfold lower
  rw [WellFounded.fix_eq]
  cases a <;> rfl

-- [proof->req~compiler-temporal-comparison~1]
theorem lower_eq (a : Formula k n) : lower a = (Behavioral.formula a).lower := by
  induction a <;> rw [lower_unfold]
  all_goals simp_all only [lowerStep, Behavioral.formula, Clafer.Behavioral.Formula.lower,
    toSet_eq, toAtom_eq]
  rename_i q _ _ _
  cases q <;> rfl

-- [impl->req~compiler-temporal-comparison~1]
def sourceLasso (l : IR.Behavioral.Lasso k o (last + 1)) :
    Clafer.Behavioral.Lasso (Fin k) o last where
  identities := ⟨l.identities.root, fun x => l.identities.directType[x], fun x => l.identities.parent[x]⟩
  loop := l.loop
  live i x := l.frames[i].live[x]
  deref i d x y := (l.frames[i].references.contains (d, x, y))

/-- The finite evaluator receives exactly the supplied inventory, frames and loop.
No target truth or source-validity premise participates in the conversion. -/
theorem sourceLasso_tables (l : IR.Behavioral.Lasso k o (last + 1)) :
    (sourceLasso l).loop = l.loop ∧
    (∀ i x, (sourceLasso l).live i x = l.frames[i].live[x]) ∧
    (∀ i d x y, (sourceLasso l).deref i d x y = true ↔ (d, x, y) ∈ l.frames[i].references) := by
  simp [sourceLasso]

-- [impl->req~compiler-temporal-comparison~1]
def attached (m : IR.Structural.Core k) (l : IR.Behavioral.Lasso k o (last + 1))
    (owner : Fin k) (a : Formula k 0) (fuel : Nat) (enough : sizeOf a < fuel) : Bool :=
  let L := sourceLasso l
  let model := Structural.interpret m
  let contexts := fun _ : Clafer.Behavioral.Lasso.Clock last =>
    Finset.univ.filter fun x => ancestor m l.identities.directType[x] owner
  (lower (a.normalize true fuel enough)).attachedFinite L
    (Clafer.Behavioral.FiniteAdapter.sets model L).observations contexts

-- [proof->req~compiler-temporal-comparison~1]
theorem attached_correct (m : IR.Structural.Core k) (l : IR.Behavioral.Lasso k o (last + 1))
    (owner : Fin k) (a : Formula k 0) (fuel : Nat) (enough : sizeOf a < fuel) :
    attached m l owner a fuel enough = true ↔
    (Behavioral.formula a).Attached (sourceLasso l).unfold
      (.sets (Structural.interpret m) (sourceLasso l).unfold)
      (fun _ => {x | ancestor m l.identities.directType[x] owner = true}) := by
  unfold attached
  rw [lower_eq, normalize_interpret]
  rw [Clafer.Behavioral.Core.normalized_attached_agrees _ _ _
    (Clafer.Behavioral.FiniteAdapter.sets _ _).agrees]
  simp only [Finset.coe_filter, Finset.mem_univ, true_and]

end ClaferCompiler.SemanticsBridge.Behavioral.Verification
