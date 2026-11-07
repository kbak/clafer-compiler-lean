module

public import ClaferCompiler.Correctness.Behavioral.Full.Collections
public import ClaferCompiler.Correctness.Behavioral.Full.PrimitiveCompletionRestriction
public import ClaferCompiler.Correctness.Behavioral.Arithmetic
public import ClaferCompiler.Correctness.StructuralRelations
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Integers

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy Backend.Alloy.Temporal

/-- A collection is a finite unary relation; object and integer atoms retain
separate identities. No formula truth appears in this observation relation. -/
def UnaryRows (rows : Temporal.Relation) : Prop :=
  ∀ row ∈ rows, ∃ a, row = [a]
def rowSet (rows : Temporal.Relation) : Set Temporal.Atom := {a | [a] ∈ rows}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem extract_rows (rows : Temporal.Relation) (unary : UnaryRows rows) (z : Int) :
    atomIntegers.extract (rowSet rows) = some z ↔ rows.eraseDups = [[.integer z]] := by
  rw [FormalCD.IntegerRealization.extract_eq_some_iff]
  change rowSet rows = {Temporal.Atom.integer z} ↔ rows.eraseDups = [[.integer z]]
  constructor
  · intro hset
    apply List.Perm.eq_singleton
    apply (List.perm_ext_iff_of_nodup (Structural.eraseDups_nodup rows) (by simp)).mpr
    intro row
    simp only [List.mem_eraseDups, List.mem_singleton]
    constructor
    · intro hr
      obtain ⟨a, rfl⟩ := unary row hr
      have ha : a ∈ rowSet rows := hr
      rw [hset] at ha
      have he := Set.mem_singleton_iff.mp ha
      rw [he]
    · intro he
      subst row
      have hz : Temporal.Atom.integer z ∈ rowSet rows := by rw [hset]; simp
      exact hz
  · intro hrows
    ext a
    change [a] ∈ rows ↔ a ∈ ({Temporal.Atom.integer z} : Set Temporal.Atom)
    rw [← List.mem_eraseDups, hrows]
    simp

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem scalarValue_singleton (rows : Temporal.Relation) (hrows : rows.eraseDups = [[.integer z]])
    (lo : lower ≤ z) (hi : z ≤ upper) : scalarValue lower upper rows = z := by
  simp [scalarValue, hrows, lo, hi]

theorem scalar_eval_singleton (r : Temporal.Rel)
    (hrows : (r.eval s w τ e t).eraseDups = [[.integer z]])
    (lo : lower ≤ z) (hi : z ≤ upper) (fits : fitsInt w z = true) :
    (Temporal.Integer.scalar lower upper r).eval s w τ e t = some z := by
  change boundedInt w (scalarValue lower upper (r.eval s w τ e t)) = some z
  rw [scalarValue_singleton _ hrows lo hi]
  exact (boundedInt_some_iff w z).mpr fits

/-- Concrete extraction preserves the original partial value once its unary
observation is represented. In particular the premise is observation equality,
not agreement of the expression or property being proved. -/
theorem scalar_extract_some (r : Temporal.Rel) (unary : UnaryRows (r.eval s w τ e t))
    (source : atomIntegers.extract (rowSet (r.eval s w τ e t)) = some z)
    (lo : lower ≤ z) (hi : z ≤ upper) (fits : fitsInt w z = true) :
    (Temporal.Integer.scalar lower upper r).eval s w τ e t = some z :=
  scalar_eval_singleton r ((extract_rows _ unary z).mp source) lo hi fits

/-- Canonical source integers are carried through the one fixed mixed atom map. -/
theorem completed_extract_some (labels : Fin o ↪ Nat) (S : Set (Completion o))
    (r : Temporal.Rel) (unary : UnaryRows (r.eval s w τ e t))
    (represented : rowSet (r.eval s w τ e t) = completionAtom labels '' S)
    (source : completeIntegers.extract S = some z)
    (lo : lower ≤ z) (hi : z ≤ upper) (fits : fitsInt w z = true) :
    (Temporal.Integer.scalar lower upper r).eval s w τ e t = some z := by
  apply scalar_extract_some r unary _ lo hi fits
  rw [represented, completionAtom_extract]
  exact source

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The generated extraction guard checks the original singleton integer
domain. The additional fit condition is precisely target integer membership. -/
theorem extract_guard (r : Temporal.Rel) (unary : UnaryRows (r.eval s w τ e t))
    (positive : 0 < w) (small : w ≤ 16) :
    (Temporal.Formula.binary .conj (.mult .one r) (.subset r .ints)).Holds s w τ e t ↔
      ∃ z, atomIntegers.extract (rowSet (r.eval s w τ e t)) = some z ∧ fitsInt w z = true := by
  rw [Encoding.holds_and (.mult _ _) (.subset _ _)]
  change ((Backend.Alloy.Multiplicity.one.holds (r.eval s w τ e t).eraseDups.length = true) ∧
    (∀ row ∈ r.eval s w τ e t, row ∈ (Temporal.Rel.ints).eval s w τ e t)) ↔ _
  simp only [Backend.Alloy.Multiplicity.holds, beq_iff_eq]
  constructor
  · rintro ⟨one, typed⟩
    obtain ⟨row, hr⟩ := List.length_eq_one_iff.mp one
    have member : row ∈ r.eval s w τ e t := by
      rw [← List.mem_eraseDups, hr]
      exact List.mem_singleton_self _
    obtain ⟨a, rfl⟩ := unary row member
    have ha := typed [a] member
    change [a] ∈ (integerAtoms w).map (fun x => [x]) at ha
    obtain ⟨atom, hatom, same⟩ := List.mem_map.mp ha
    have eqAtom : atom = a := by simpa using same
    subst atom
    obtain ⟨i, _, eqInt⟩ := List.mem_map.mp hatom
    subst a
    refine ⟨_, (extract_rows _ unary _).mpr hr, ?_⟩
    exact (integerAtoms_fits w positive small _).mp hatom
  · rintro ⟨z, source, fits⟩
    have hr := (extract_rows _ unary z).mp source
    refine ⟨by rw [hr]; rfl, ?_⟩
    intro row member
    have same : row = [.integer z] := by
      rw [← List.mem_eraseDups, hr, List.mem_singleton] at member
      exact member
    subst row
    change [Temporal.Atom.integer z] ∈ (integerAtoms w).map (fun x => [x])
    exact List.mem_map.mpr ⟨.integer z, (integerAtoms_fits w positive small z).mpr fits, rfl⟩

theorem completed_extract_guard (labels : Fin o ↪ Nat) (S : Set (Completion o))
    (r : Temporal.Rel) (unary : UnaryRows (r.eval s w τ e t))
    (represented : rowSet (r.eval s w τ e t) = completionAtom labels '' S)
    (positive : 0 < w) (small : w ≤ 16)
    (fit : ∀ z, Sum.inr z ∈ S → fitsInt w z = true) :
    (Temporal.Formula.binary .conj (.mult .one r) (.subset r .ints)).Holds s w τ e t ↔
      (completeIntegers.extract S).isSome = true := by
  rw [extract_guard r unary positive small, represented]
  simp only [completionAtom_extract]
  constructor
  · rintro ⟨z, hz, _⟩
    simp [hz]
  · intro h
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp h
    refine ⟨z, hz, fit z ?_⟩
    have single := (FormalCD.IntegerRealization.extract_eq_some_iff completeIntegers S z).mp hz
    change S = {Sum.inr z} at single
    rw [single]
    exact Set.mem_singleton _

end ClaferCompiler.Correctness.Behavioral.Full
