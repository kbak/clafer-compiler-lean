module

public import ClaferCompiler.Backend.Alloy.Behavioral.Representation
public import ClaferCompiler.Correctness.StructuralSatisfaction
public import ClaferCompiler.SemanticsBridge.Behavioral.Trace

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

-- [proof->req~compiler-trace-representation~1]
@[simp] theorem encode_index (v : IR.Structural.Layout k) (l : IR.Behavioral.Lasso k o steps)
    (t : Nat) : (encode v l).index t = (l.index t).val := by
  by_cases h : t < steps <;> simp [Temporal.Lasso.index, encode, IR.Behavioral.Lasso.index, h]

@[simp] theorem encode_unfold (v : IR.Structural.Layout k) (l : IR.Behavioral.Lasso k o steps)
    (t : Nat) : (encode v l).unfold.state t = encodeState v l.identities (l.at t) := by
  change (encode v l).frames[(encode v l).index t]?.getD _ = _
  rw [encode_index]
  simp [encode, IR.Behavioral.Lasso.at, (l.index t).isLt]

@[simp] theorem encode_pool (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o) (d : Fin k) :
    (encodeState v ids f).signatures[Structural.signatureId v d]?.getD [] =
      ((List.finRange o).filter (fun x => IR.Behavioral.ancestor v.core ids.directType[x] d)).map
        (fun x => ids.ids[x]) := by
  simp [encodeState, Structural.signatureId, Nat.add_comm 1,
    List.getElem?_idxOf (Structural.mem_order v d)]

@[simp] theorem encode_references (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o) (d : Fin k) :
    (encodeState v ids f).fields[2 + d.val]?.getD [] =
      (f.references.filter (fun r => r.1 == d)).map
        (fun r => [ids.ids[r.2.1], ids.ids[r.2.2]]) := by
  simp [encodeState, Nat.add_comm 2, d.isLt]

/-- The target carrier consists exactly of its static object pool; unused solver
inventory slots have no source identity. -/
abbrev Pool (target : Temporal.Lasso) :=
  {x : Nat // x ∈ (target.unfold.state 0).signatures[0]?.getD []}

/-- All observations use this single bijection, including reference-head objects.
These are concrete table equations and a loop equation, with no formula truth or
structural validity hidden in the relation. -/
structure TraceRep (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (target : Temporal.Lasso) where
  objects : Fin o ≃ Pool target
  length : target.frames.length = steps
  loop : target.loop = source.loop.val
  roots : ∀ t label,
    label ∈ (target.unfold.state t).signatures[Structural.signatureId v v.core.root]?.getD [] ↔
      label = (objects source.identities.root).val
  pools : ∀ t d label,
    label ∈ (target.unfold.state t).signatures[Structural.signatureId v d]?.getD [] ↔
      ∃ x, IR.Behavioral.ancestor v.core source.identities.directType[x] d = true ∧
        label = (objects x).val
  allObjects : ∀ t label, label ∈ (target.unfold.state t).signatures[0]?.getD [] ↔
    ∃ x, label = (objects x).val
  parents : ∀ t row, row ∈ (target.unfold.state t).fields[0]?.getD [] ↔
    ∃ x p, source.identities.parent[x] = some p ∧ row = [(objects x).val, (objects p).val]
  lives : ∀ t row, row ∈ (target.unfold.state t).fields[1]?.getD [] ↔
    ∃ x, (source.at t).live[x] = true ∧ row = [(objects source.identities.root).val, (objects x).val]
  references : ∀ t d row, row ∈ (target.unfold.state t).fields[2 + d.val]?.getD [] ↔
    ∃ x y, (d, x, y) ∈ (source.at t).references ∧ row = [(objects x).val, (objects y).val]

namespace TraceRep

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Temporal.Lasso}

def label (rep : TraceRep v source target) (x : Fin o) : Nat := (rep.objects x).val

theorem label_injective (rep : TraceRep v source target) : Function.Injective rep.label := by
  intro x y h
  exact rep.objects.injective (Subtype.ext h)

-- [proof->req~compiler-trace-representation~1]
theorem index (rep : TraceRep v source target) (t : Nat) :
    target.index t = (source.index t).val := by
  by_cases h : t < steps <;>
    simp [Temporal.Lasso.index, IR.Behavioral.Lasso.index, rep.length, rep.loop, h]

theorem pool_label (rep : TraceRep v source target) (t : Nat) (d : Fin k) (x : Fin o) :
    rep.label x ∈ (target.unfold.state t).signatures[Structural.signatureId v d]?.getD [] ↔
      IR.Behavioral.ancestor v.core source.identities.directType[x] d = true := by
  rw [rep.pools]
  constructor
  · rintro ⟨y, hy, he⟩
    exact rep.label_injective he ▸ hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem parent_row (rep : TraceRep v source target) (t : Nat) (x p : Fin o) :
    [rep.label x, rep.label p] ∈ (target.unfold.state t).fields[0]?.getD [] ↔
      source.identities.parent[x] = some p := by
  rw [rep.parents]
  constructor
  · rintro ⟨a, b, hp, he⟩
    have ha : x = a := rep.label_injective (List.cons.inj he).1
    have hb : p = b := rep.label_injective (List.cons.inj (List.cons.inj he).2).1
    subst a b
    exact hp
  · intro hp; exact ⟨x, p, hp, rfl⟩

theorem reference_row (rep : TraceRep v source target) (t : Nat) (d : Fin k) (x y : Fin o) :
    [rep.label x, rep.label y] ∈ (target.unfold.state t).fields[2 + d.val]?.getD [] ↔
      (d, x, y) ∈ (source.at t).references := by
  rw [rep.references]
  constructor
  · rintro ⟨a, b, hr, he⟩
    have ha : x = a := rep.label_injective (List.cons.inj he).1
    have hb : y = b := rep.label_injective (List.cons.inj (List.cons.inj he).2).1
    subst a b
    exact hr
  · intro hr; exact ⟨x, y, hr, rfl⟩

-- [proof->req~compiler-trace-representation~1]
/-- Two reference occurrences remain distinct even when they share one target. -/
theorem distinct_occurrences (rep : TraceRep v source target) (x y z : Fin o) (h : x ≠ y) :
    [rep.label x, rep.label z] ≠ [rep.label y, rep.label z] := by
  intro he
  exact h (rep.label_injective (List.cons.inj he).1)

-- [proof->req~compiler-trace-representation~1]
/-- Absence and later reappearance cannot change one object's actual parent. -/
theorem parent_stable (rep : TraceRep v source target) (t u : Nat) (x p q : Fin o)
    (hp : [rep.label x, rep.label p] ∈ (target.unfold.state t).fields[0]?.getD [])
    (hq : [rep.label x, rep.label q] ∈ (target.unfold.state u).fields[0]?.getD []) : p = q := by
  have hp := (rep.parent_row t x p).mp hp
  have hq := (rep.parent_row u x q).mp hq
  exact Option.some.inj (hp.symm.trans hq)

end TraceRep

def encodeObjects (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y) :
    Fin o ≃ Pool (encode v source) :=
  Equiv.ofBijective (fun x => ⟨source.identities.ids[x], by
    simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
      Vector.mem_toList_iff, Vector.mem_iff_getElem]
    exact ⟨x.val, x.isLt, rfl⟩⟩) (by
      constructor
      · intro x y h
        exact unique x y (congrArg Subtype.val h)
      · rintro ⟨label, hl⟩
        simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
          Vector.mem_toList_iff, Vector.mem_iff_getElem] at hl
        obtain ⟨i, hi, he⟩ := hl
        exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

@[simp] theorem encodeObjects_label (v : IR.Structural.Layout k)
    (source : IR.Behavioral.Lasso k o steps) (unique) (x : Fin o) :
    (encodeObjects v source unique x).val = source.identities.ids[x] := rfl

-- [proof->req~compiler-trace-representation~1]
/-- Encoding preserves the whole observation trace using a single finite-carrier
bijection. Only distinct source labels are needed, not source satisfaction. -/
def encode_rep (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (rootType : source.identities.directType[source.identities.root] = v.core.root)
    (rootOnly : ∀ x : Fin o, source.identities.directType[x] = v.core.root → x = source.identities.root) :
    TraceRep v source (encode v source) where
  objects := encodeObjects v source unique
  length := by simp [encode]
  loop := rfl
  roots := by
    intro t label
    simp only [encode_unfold, encode_pool, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and, encodeObjects_label, ancestor_agrees, Structural.ancestor_root_iff]
    constructor
    · rintro ⟨x, hx, he⟩
      simpa [rootOnly x hx] using he.symm
    · intro he
      exact ⟨source.identities.root, rootType, he.symm⟩
  pools := by
    intro t d label
    simp only [encode_unfold, encode_pool, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and, encodeObjects_label]
    aesop
  allObjects := by
    intro t label
    simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
      Vector.mem_toList_iff, Vector.mem_iff_getElem, encodeObjects_label]
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨⟨i, hi⟩, he.symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.isLt, rfl⟩
  parents := by
    intro t row
    simp only [encode_unfold, encodeState, encodeObjects_label]
    aesop
  lives := by
    intro t row
    simp only [encode_unfold, encodeState, encodeObjects_label]
    aesop
  references := by
    intro t d row
    simp only [encode_unfold, encode_references, List.mem_map, List.mem_filter,
      beq_iff_eq, encodeObjects_label]
    constructor
    · rintro ⟨⟨e, x, y⟩, ⟨hm, he⟩, hr⟩
      change e = d at he
      subst e
      exact ⟨x, y, hm, hr.symm⟩
    · rintro ⟨x, y, hm, hr⟩
      exact ⟨(d, x, y), ⟨hm, rfl⟩, hr.symm⟩

end ClaferCompiler.Correctness.Behavioral
