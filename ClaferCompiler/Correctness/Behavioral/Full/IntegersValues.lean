module

public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsValues
public import ClaferCompiler.Correctness.Behavioral.Full.Integers

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal

structure IntegerObservation (s : Schema) (w : Nat) (τ : Trace) (e : Environment)
    (t : Nat) (source : Option Int) (target : Backend.Alloy.Behavioral.Full.Value Integer) : Prop where
  built : Value.Built target
  sound : ∀ n, Value.Meaning s w τ e t target n →
    ∃ z, source = some z ∧ Arithmetic.Term n ∧ n.eval s w τ e t = some z
  complete : ∀ z, source = some z → ∃ n, Value.Meaning s w τ e t target n

namespace IntegerObservation
variable {U : Type} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}
  {f : U → Atom} {source : Option (Set U)} {a : Backend.Alloy.Behavioral.Full.Value Rel}

theorem literal (fits : Backend.Alloy.fitsInt w z = true) :
    IntegerObservation s w τ e t (some z) (.pure (.literal z)) := by
  refine ⟨Value.pure_built _, ?_, ?_⟩
  · intro n hn
    have same := (Value.pure_meaning _ _).mp hn
    subst n
    exact ⟨z, rfl, .literal z, (Backend.Alloy.boundedInt_some_iff w z).mpr fits⟩
  · intro _ _
    exact ⟨_, (Value.pure_meaning _ _).mpr rfl⟩

def cardinalityBody (aliases : List Rel) (budget : Nat) (r : Rel) :
    Backend.Alloy.Behavioral.Full.Value Integer :=
  (Backend.Alloy.Behavioral.Full.Value.selections aliases r budget).bind fun chosen =>
    ⟨[(.equal r (Backend.Alloy.Behavioral.Full.union chosen), .literal (Int.ofNat chosen.length))]⟩

theorem cardinalityBody_built (aliases : List Rel) (budget : Nat) (r : Rel) :
    Value.Built (cardinalityBody aliases budget r) := by
  apply Value.bind_built _ _ (Value.selections_built aliases r budget)
  intro chosen g x hg
  simp at hg
  rw [hg.1]
  exact .equal _ _

theorem cardinalityBody_meaning (aliases : List Rel) (budget : Nat) (r : Rel) :
    Value.Meaning s w τ e t (cardinalityBody aliases budget r) n ↔
      ∃ chosen, Value.Meaning s w τ e t
        (Backend.Alloy.Behavioral.Full.Value.selections aliases r budget) chosen ∧
        n = .literal (Int.ofNat chosen.length) ∧
        (Formula.equal r (Backend.Alloy.Behavioral.Full.union chosen)).Holds s w τ e t := by
  have body (chosen : List Rel) : Value.Built (Backend.Alloy.Behavioral.Full.Value.mk
      [(Formula.equal r (Backend.Alloy.Behavioral.Full.union chosen),
        Integer.literal (Int.ofNat chosen.length))]) := by
    intro g x hg
    simp at hg
    rw [hg.1]
    exact .equal _ _
  rw [cardinalityBody, Value.bind_meaning _ _ (Value.selections_built aliases r budget) body]
  simp only [Value.Meaning, List.mem_singleton, Prod.mk.injEq]
  aesop

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The emitted cardinality cases preserve the source finite-cardinality
operation, with the checked observation budget and one fixed alias cover. -/
theorem cardinality (ha : CollectionObservation s w τ e t f source a)
    (hf : Function.Injective f) (aliases : List Rel) (budget : Nat)
    (terms : ∀ entry ∈ aliases, entry.Term)
    (cover : ∀ S, source = some S → ∀ x ∈ S,
      ∃ entry ∈ aliases, Mixed.Unary f {x} (entry.eval s w τ e t))
    (bound : ∀ S, source = some S → S.ncard ≤ budget)
    (fits : ∀ S, source = some S → Backend.Alloy.fitsInt w (Int.ofNat S.ncard) = true) :
    IntegerObservation s w τ e t
      ((source.bind Clafer.Constraints.finiteCard).map ULift.down)
      (Backend.Alloy.Behavioral.Full.integerCardinality aliases budget a) := by
  change IntegerObservation s w τ e t _ (a.bind (cardinalityBody aliases budget))
  refine ⟨Value.bind_built a _ ha.built (cardinalityBody_built aliases budget), ?_, ?_⟩
  · intro n hn
    obtain ⟨r, hr, hn⟩ := (Value.bind_meaning a _ ha.built (cardinalityBody_built aliases budget)).mp hn
    obtain ⟨S, sourceS, _, rows⟩ := ha.sound r hr
    obtain ⟨chosen, hc, rfl, _⟩ := (cardinalityBody_meaning aliases budget r).mp hn
    have cardinal := source_selection_cardinality hf rows terms (cover S sourceS) (bound S sourceS) hc
    refine ⟨Int.ofNat S.ncard, ?_, .literal _, ?_⟩
    · rw [sourceS, Option.bind_some, Clafer.Constraints.finiteCard_finite S (Mixed.unary_finite hf rows)]
      rfl
    · rw [cardinal]
      exact (Backend.Alloy.boundedInt_some_iff w _).mpr (fits S sourceS)
  · intro z sourceZ
    cases sourceS : source with
    | none => simp [sourceS] at sourceZ
    | some S =>
      obtain ⟨r, hr⟩ := ha.complete S sourceS
      obtain ⟨T, sourceT, _, rows⟩ := ha.sound r hr
      have same : T = S := Option.some.inj (sourceT.symm.trans sourceS)
      subst T
      have rowCover : ∀ row ∈ r.eval s w τ e t,
          ∃ entry ∈ aliases, (entry.eval s w τ e t).eraseDups = [row] := by
        intro row hr
        obtain ⟨x, hx, rfl⟩ := (rows row).mp hr
        obtain ⟨entry, he, singleton⟩ := cover S sourceS x hx
        exact ⟨entry, he, Mixed.unary_singleton_rows singleton⟩
      have rowBound : (r.eval s w τ e t).toFinset.card ≤ budget := by
        rw [Mixed.unary_card hf rows]
        exact bound S sourceS
      obtain ⟨chosen, hc, _, _, equal⟩ :=
        Selection.selections_complete aliases r budget terms rowCover rowBound
      refine ⟨.literal (Int.ofNat chosen.length),
        (Value.bind_meaning a _ ha.built (cardinalityBody_built aliases budget)).mpr ?_⟩
      exact ⟨r, hr, (cardinalityBody_meaning aliases budget r).mpr
        ⟨chosen, hc, rfl, fun row => (equal row).symm⟩⟩

theorem defined {source : Option Int} {a : Backend.Alloy.Behavioral.Full.Value Integer}
    (h : IntegerObservation s w τ e t source a) :
    a.defined.Holds s w τ e t ↔ source.isSome = true := by
  rw [Value.defined_meaning a h.built]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz, _, _⟩ := h.sound n hn
    simp [hz]
  · intro hs
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs
    exact h.complete z hz

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem binary {left right : Option Int} {a b : Backend.Alloy.Behavioral.Full.Value Integer}
    (ha : IntegerObservation s w τ e t left a)
    (hb : IntegerObservation s w τ e t right b)
    (op : IR.BehavioralArithmetic.Binary) (ra rb : IR.Expr.Interval)
    (checked : IR.BehavioralArithmetic.Checked op w ra rb)
    (leftRange : ∀ x, left = some x → ra.Contains x)
    (rightRange : ∀ y, right = some y → rb.Contains y) :
    IntegerObservation s w τ e t
      ((SemanticsBridge.BehavioralArithmetic.binary op).eval left right)
      (Backend.Alloy.Behavioral.Full.integerBinary op a b) := by
  refine ⟨Value.map_built _ _ (Value.pair_built a b ha.built hb.built), ?_, ?_⟩
  · intro result meaning
    obtain ⟨⟨x, y⟩, pair, rfl⟩ := (Value.map_meaning _ _).mp meaning
    obtain ⟨hx, hy⟩ := (Value.pair_meaning a b ha.built hb.built).mp pair
    obtain ⟨i, hi, hxt, hxe⟩ := ha.sound x hx
    obtain ⟨j, hj, hyt, hye⟩ := hb.sound y hy
    obtain ⟨z, hz, he⟩ := Arithmetic.represented_binary op hxt hyt s w τ e t ra rb checked
      i j (leftRange i hi) (rightRange j hj) hxe hye
    exact ⟨z, by simpa [Clafer.Behavioral.Arithmetic.Binary.eval, hi, hj] using hz,
      .binary op hxt hyt, he⟩
  · intro z hz
    cases hl : left with
    | none => simp [hl] at hz
    | some i =>
      cases hr : right with
      | none => simp [hr] at hz
      | some j =>
        obtain ⟨x, hx⟩ := ha.complete i hl
        obtain ⟨y, hy⟩ := hb.complete j hr
        exact ⟨_, (Value.map_meaning _ _).mpr
          ⟨(x, y), (Value.pair_meaning a b ha.built hb.built).mpr ⟨hx, hy⟩, rfl⟩⟩

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem negate {source : Option Int} {a : Backend.Alloy.Behavioral.Full.Value Integer}
    (ha : IntegerObservation s w τ e t source a)
    (zero : Backend.Alloy.fitsInt w 0 = true)
    (fits : ∀ z, source = some z → Backend.Alloy.fitsInt w (-z) = true) :
    IntegerObservation s w τ e t (source.map Int.neg)
      (Backend.Alloy.Behavioral.Full.integerNegate a) := by
  refine ⟨Value.map_built _ _ ha.built, ?_, ?_⟩
  · intro result meaning
    obtain ⟨x, hx, rfl⟩ := (Value.map_meaning _ _).mp meaning
    obtain ⟨z, hz, ht, he⟩ := ha.sound x hx
    refine ⟨-z, by rw [hz]; rfl, .binary .subtract (.literal 0) ht, ?_⟩
    change (Backend.Alloy.Behavioral.Arithmetic.binary .subtract (.literal 0) x).eval s w τ e t = some (-z)
    rw [Arithmetic.eval_binary .subtract (.literal 0) ht]
    change (IR.BehavioralArithmetic.Binary.subtract.eval (Backend.Alloy.boundedInt w 0)
      (x.eval s w τ e t)).bind (Backend.Alloy.boundedInt w) = some (-z)
    rw [(Backend.Alloy.boundedInt_some_iff w 0).mpr zero, he]
    simpa [IR.BehavioralArithmetic.Binary.eval, IR.BehavioralArithmetic.Binary.apply] using
      (Backend.Alloy.boundedInt_some_iff w (-z)).mpr (fits z hz)
  · intro z hz
    obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp hz
    obtain ⟨x, hx⟩ := ha.complete i hi
    exact ⟨_, (Value.map_meaning _ _).mpr ⟨x, hx, rfl⟩⟩

end IntegerObservation
end ClaferCompiler.Correctness.Behavioral.Full
