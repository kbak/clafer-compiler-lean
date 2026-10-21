module

public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Encodable.Basic
public import ClaferCompiler.Backend.Alloy.SourceObservation
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section
/-! [proof->req~compiler-pipeline-correctness~1] -/
namespace ClaferCompiler.Correctness.Pipeline
open IR.Expr

/-- Decode scalar identity, retaining ordinary target labels in a disjoint
namespace. Only the finite live restriction is used by representation. -/
abbrev atom := Backend.Alloy.Expressions.decodeAtom

theorem atom_injective (rows : List (Nat × Int))
    (hinj : ∀ a ∈ rows, ∀ b ∈ rows, a.2 = b.2 → a.1 = b.1) :
    Function.Injective (atom rows) := by
  intro a b h
  cases hx : rows.find? (fun row => row.1 == a) with
  | none =>
    cases hy : rows.find? (fun row => row.1 == b) with
    | none => simpa [atom, Backend.Alloy.Expressions.decodeAtom, hx, hy] using h
    | some y => simp [atom, Backend.Alloy.Expressions.decodeAtom, hx, hy] at h
  | some x =>
    cases hy : rows.find? (fun row => row.1 == b) with
    | none => simp [atom, Backend.Alloy.Expressions.decodeAtom, hx, hy] at h
    | some y =>
      have hxk : x.1 = a := by simpa using List.find?_some hx
      have hyk : y.1 = b := by simpa using List.find?_some hy
      have hz : x.2 = y.2 := by simpa [atom, Backend.Alloy.Expressions.decodeAtom, hx, hy] using h
      exact hxk.symm.trans ((hinj x (List.mem_of_find?_eq_some hx) y
        (List.mem_of_find?_eq_some hy) hz).trans hyk)

theorem atom_integer (rows : List (Nat × Int))
    (hkeys : (rows.map Prod.fst).Nodup) (a : Nat) (z : Int) :
    atom rows a = .integer z ↔ (a, z) ∈ rows := by
  unfold atom Backend.Alloy.Expressions.decodeAtom
  cases hf : rows.find? (fun row => row.1 == a) with
  | none =>
    simp only [reduceCtorEq, false_iff]
    intro hm
    have := (List.find?_eq_none.mp hf) (a, z) hm
    simp at this
  | some row =>
    have hm := List.mem_of_find?_eq_some hf
    have hk : row.1 = a := by simpa using List.find?_some hf
    simp only [Atom.integer.injEq]
    constructor
    · intro hz
      simpa only [show row = (a, z) from Prod.ext hk hz] using hm
    · intro ha
      exact congrArg Prod.snd (List.inj_on_of_nodup_map hkeys hm ha hk)

theorem atom_object (rows : List (Nat × Int)) (a : Nat)
    (h : ∀ z, (a, z) ∉ rows) : atom rows a = .object a := by
  unfold atom Backend.Alloy.Expressions.decodeAtom
  have hf : rows.find? (fun row => row.1 == a) = none := by
    apply List.find?_eq_none.mpr
    intro row hm he
    have hk : row.1 = a := by simpa using he
    exact h row.2 (by simpa only [← hk] using hm)
  rw [hf]

/-- Reuse the standard countable encoding; no custom signed-integer numbering. -/
def atomCode (a : Atom) : Nat :=
  Encodable.encode (α := Sum Nat Int) (match a with
    | .object n => .inl n | .integer z => .inr z)

theorem atomCode_injective : Function.Injective atomCode := by
  intro a b h
  have he := Encodable.encode_injective h
  cases a <;> cases b <;> simp_all [atomCode]

/-- Extend the *finite* observed labeling to the globally injective map required
by the accepted expression theorem. The unused integer domain is never counted
or assumed to fit an Alloy scope. -/
theorem exists_encoding (live : List Nat) (g : Nat → Atom) (hg : Function.Injective g) :
    ∃ f : Atom → Nat, Function.Injective f ∧ ∀ a ∈ live, f (g a) = a := by
  classical
  let : Fintype {a : Nat // a ∈ live} := Fintype.ofFinset live.toFinset (by
    intro a
    change a ∈ live.toFinset ↔ a ∈ live
    simp)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : {a : Nat // a ∈ live} => atomCode (g a.val)) Subtype.val
    (atomCode_injective.comp (hg.comp Subtype.val_injective)) Subtype.val_injective
  exact ⟨σ ∘ atomCode, σ.injective.comp atomCode_injective, fun a ha => hσ ⟨a, ha⟩⟩

end ClaferCompiler.Correctness.Pipeline
