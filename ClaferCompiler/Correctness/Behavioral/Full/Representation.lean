module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Representation
public import ClaferCompiler.SemanticsBridge.BehavioralStructural
public import ClaferCompiler.SemanticsBridge.Behavioral.Trace

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
@[simp] theorem encode_index (l : ObservedLasso k o steps) (t : Nat) :
    (encode l).index t = (l.objects.index t).val := by
  by_cases h : t < steps <;>
    simp [Temporal.Lasso.index, encode, IR.Behavioral.Lasso.index, h]

@[simp] theorem encode_unfold (l : ObservedLasso k o steps) (t : Nat) :
    (encode l).unfold.state t =
      encodeState l.objects.identities (l.objects.at t) (l.valuesAt t) := by
  change (encode l).frames[(encode l).index t]?.getD _ = _
  rw [encode_index]
  simp [encode, IR.Behavioral.Lasso.at, ObservedLasso.valuesAt, (l.objects.index t).isLt]

@[simp] theorem encode_direct (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o) (values : Vector Int o) (d : Fin k) :
    (encodeState ids f values).signatures[signatureId d]?.getD [] =
      ((List.finRange o).filter (fun x => ids.directType[x] == d)).map
        (fun x => ids.ids[x]) := by
  simp [encodeState, signatureId, Nat.add_comm 1, d.isLt]

@[simp] theorem encode_references (ids : IR.Behavioral.Identities k o)
    (f : IR.Behavioral.Frame k o) (values : Vector Int o) (d : Fin k) :
    (encodeState ids f values).fields[2 + d.val]?.getD [] =
      (f.references.filter (fun r => r.1 == d)).map
        (fun r => [ids.ids[r.2.1], ids.ids[r.2.2]]) := by
  simp [encodeState, Nat.add_comm 2, d.isLt]

abbrev Pool (target : Temporal.Lasso) :=
  {x : Nat // x ∈ (target.unfold.state 0).signatures[0]?.getD []}

-- [impl->req~compiler-trace-assurance~1]
/-- A single map for every occurrence across all frames, plus exact mathematical
scalar observations. These are data equations only; neither source validity nor
target satisfaction is a field. Primitive universes are not this finite carrier. -/
structure TraceRep (v : IR.BehavioralStructural.Validated k)
    (source : ObservedLasso k o steps) (target : Temporal.Lasso) where
  objects : Fin o ≃ Pool target
  length : target.frames.length = steps
  loop : target.loop = source.objects.loop.val
  roots : ∀ t label,
    label ∈ (target.unfold.state t).signatures[signatureId v.core.structural.root]?.getD [] ↔
      label = (objects source.objects.identities.root).val
  directTypes : ∀ t d label,
    label ∈ (target.unfold.state t).signatures[signatureId d]?.getD [] ↔
      ∃ x, source.objects.identities.directType[x] = d ∧ label = (objects x).val
  allObjects : ∀ t label, label ∈ (target.unfold.state t).signatures[0]?.getD [] ↔
    ∃ x, label = (objects x).val
  parents : ∀ t row, row ∈ (target.unfold.state t).fields[0]?.getD [] ↔
    ∃ x p, source.objects.identities.parent[x] = some p ∧
      row = [(objects x).val, (objects p).val]
  lives : ∀ t row, row ∈ (target.unfold.state t).fields[1]?.getD [] ↔
    ∃ x, (source.objects.at t).live[x] = true ∧
      row = [(objects source.objects.identities.root).val, (objects x).val]
  references : ∀ t d row, row ∈ (target.unfold.state t).fields[2 + d.val]?.getD [] ↔
    ∃ x y, (d, x, y) ∈ (source.objects.at t).references ∧
      row = [(objects x).val, (objects y).val]
  values : ∀ t row, row ∈ (target.unfold.state t).values[0]?.getD [] ↔
    ∃ x, row = ((objects x).val, (source.valuesAt t)[x])

def encodeObjects (source : ObservedLasso k o steps)
    (unique : ∀ x y : Fin o,
      source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y) :
    Fin o ≃ Pool (encode source) :=
  Equiv.ofBijective (fun x => ⟨source.objects.identities.ids[x], by
    simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
      Vector.mem_toList_iff, Vector.mem_iff_getElem]
    exact ⟨x.val, x.isLt, rfl⟩⟩) (by
      constructor
      · intro x y h; exact unique x y (congrArg Subtype.val h)
      · rintro ⟨label, hl⟩
        simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
          Vector.mem_toList_iff, Vector.mem_iff_getElem] at hl
        obtain ⟨i, hi, he⟩ := hl
        exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

@[simp] theorem encodeObjects_label (source : ObservedLasso k o steps) (unique) (x : Fin o) :
    (encodeObjects source unique x).val = source.objects.identities.ids[x] := rfl

-- [proof->req~compiler-full-behavioral-correctness~1]
def encode_rep (v : IR.BehavioralStructural.Validated k) (source : ObservedLasso k o steps)
    (unique : ∀ x y : Fin o,
      source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y)
    (rootType : source.objects.identities.directType[source.objects.identities.root] = v.core.structural.root)
    (rootOnly : ∀ x : Fin o, source.objects.identities.directType[x] = v.core.structural.root →
      x = source.objects.identities.root) : TraceRep v source (encode source) where
  objects := encodeObjects source unique
  length := by simp [encode]
  loop := rfl
  roots := by
    intro t label
    simp only [encode_unfold, encode_direct, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and, beq_iff_eq, encodeObjects_label]
    constructor
    · rintro ⟨x, hx, he⟩
      simpa [rootOnly x hx] using he.symm
    · intro he
      exact ⟨source.objects.identities.root, rootType, he.symm⟩
  directTypes := by
    intro t d label
    simp only [encode_unfold, encode_direct, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and, beq_iff_eq, encodeObjects_label]
    aesop
  allObjects := by
    intro t label
    simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
      Vector.mem_toList_iff, Vector.mem_iff_getElem, encodeObjects_label]
    constructor
    · rintro ⟨i, hi, he⟩; exact ⟨⟨i, hi⟩, he.symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨x.val, x.isLt, rfl⟩
  parents := by
    intro t row
    rw [encode_unfold]
    change row ∈ (List.finRange o).flatMap (fun x =>
      (source.objects.identities.parent[x]).toList.map (fun p =>
        [source.objects.identities.ids[x], source.objects.identities.ids[p]])) ↔ _
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
      Option.mem_toList, encodeObjects_label]
    constructor
    · rintro ⟨x, p, hp, he⟩; exact ⟨x, p, hp, he.symm⟩
    · rintro ⟨x, p, hp, he⟩; exact ⟨x, p, hp, he.symm⟩
  lives := by
    intro t row
    rw [encode_unfold]
    change row ∈ ((List.finRange o).filter (fun x => (source.objects.at t).live[x])).map
      (fun x => [source.objects.identities.ids[source.objects.identities.root],
        source.objects.identities.ids[x]]) ↔ _
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, encodeObjects_label]
    constructor
    · rintro ⟨x, hx, he⟩; exact ⟨x, hx, he.symm⟩
    · rintro ⟨x, hx, he⟩; exact ⟨x, hx, he.symm⟩
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
  values := by
    intro t row
    simp only [encode_unfold, encodeState, List.getElem?_cons_zero, Option.getD_some,
      List.mem_map, List.mem_finRange, true_and, encodeObjects_label]
    exact exists_congr fun _ => eq_comm

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Temporal.Lasso}

def label (rep : TraceRep v source target) (x : Fin o) : Nat := (rep.objects x).val

theorem label_injective (rep : TraceRep v source target) : Function.Injective rep.label := by
  intro x y h
  exact rep.objects.injective (Subtype.ext h)

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem index (rep : TraceRep v source target) (t : Nat) :
    target.index t = (source.objects.index t).val := by
  by_cases h : t < steps <;>
    simp [Temporal.Lasso.index, IR.Behavioral.Lasso.index, rep.length, rep.loop, h]

theorem direct_type (rep : TraceRep v source target) (t : Nat) (d : Fin k) (x : Fin o) :
    rep.label x ∈ (target.unfold.state t).signatures[signatureId d]?.getD [] ↔
      source.objects.identities.directType[x] = d := by
  rw [rep.directTypes]
  constructor
  · rintro ⟨y, hy, he⟩; exact rep.label_injective he ▸ hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem parent_row (rep : TraceRep v source target) (t : Nat) (x p : Fin o) :
    [rep.label x, rep.label p] ∈ (target.unfold.state t).fields[0]?.getD [] ↔
      source.objects.identities.parent[x] = some p := by
  rw [rep.parents]
  constructor
  · rintro ⟨a, b, hp, he⟩
    have ha := rep.label_injective (List.cons.inj he).1
    have hb := rep.label_injective (List.cons.inj (List.cons.inj he).2).1
    subst a b
    exact hp
  · intro hp; exact ⟨x, p, hp, rfl⟩

theorem value_row (rep : TraceRep v source target) (t : Nat) (x : Fin o) (z : Int) :
    (rep.label x, z) ∈ (target.unfold.state t).values[0]?.getD [] ↔
      z = (source.valuesAt t)[x] := by
  rw [rep.values]
  constructor
  · rintro ⟨y, he⟩
    have hx := rep.label_injective (Prod.mk.inj he).1
    subst y
    exact (Prod.mk.inj he).2
  · rintro rfl; exact ⟨x, rfl⟩

/-- Equal integer targets retain distinct occurrence identities. -/
theorem distinct_occurrences (rep : TraceRep v source target) (x y : Fin o) (z : Int)
    (h : x ≠ y) : (rep.label x, z) ≠ (rep.label y, z) := by
  intro he
  exact h (rep.label_injective (Prod.mk.inj he).1)

theorem parent_stable (rep : TraceRep v source target) (t u : Nat) (x p q : Fin o)
    (hp : [rep.label x, rep.label p] ∈ (target.unfold.state t).fields[0]?.getD [])
    (hq : [rep.label x, rep.label q] ∈ (target.unfold.state u).fields[0]?.getD []) : p = q := by
  exact Option.some.inj (((rep.parent_row t x p).mp hp).symm.trans
    ((rep.parent_row u x q).mp hq))

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
