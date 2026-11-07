module

public import ClaferCompiler.Correctness.Behavioral.Representation

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

theorem sameTables_refl [BEq α] [LawfulBEq α] (tables : List (List α)) :
    sameTables tables tables = true := by
  simp [sameTables, List.all_eq_true]

theorem sameTables_complete [BEq α] [LawfulBEq α] (a b : List (List α))
    (length : a.length = b.length)
    (members : ∀ (i : Nat) (x : α), x ∈ a[i]?.getD [] ↔ x ∈ b[i]?.getD []) :
    sameTables a b = true := by
  simp only [sameTables, length, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, List.mem_range, Bool.and_eq_true, List.contains_iff_mem]
  intro i _
  exact ⟨fun x hx => (members i x).mp hx, fun x hx => (members i x).mpr hx⟩

theorem sameRelation_complete (a b : Backend.Alloy.Relation)
    (members : ∀ row, row ∈ a ↔ row ∈ b) : sameRelation a b = true := by
  simp only [sameRelation, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun row h => (members row).mp h, fun row h => (members row).mpr h⟩

theorem roundTrip_encode (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (rootType : source.identities.directType[source.identities.root] = v.core.root)
    (rootOnly : ∀ x : Fin o, source.identities.directType[x] = v.core.root → x = source.identities.root) :
    roundTripChecks v source (encode v source) = true := by
  simp only [roundTripChecks, encode, List.length_map, Vector.length_toList,
    beq_self_eq_true, Bool.true_and, decide_eq_true rootType]
  simp [List.all_eq_true, sameState, sameTables_refl]
  exact ⟨unique, rootOnly⟩

theorem sameTables_meaning [BEq α] [LawfulBEq α] (a b : List (List α))
    (h : sameTables a b = true) (i : Nat) (x : α) :
    x ∈ a[i]?.getD [] ↔ x ∈ b[i]?.getD [] := by
  simp only [sameTables, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  by_cases hi : i < a.length
  · have he := h.2 i hi
    simp only [List.contains_iff_mem] at he
    exact ⟨he.1 x, he.2 x⟩
  · have hb : ¬ i < b.length := by omega
    simp [List.getElem?_eq_none (Nat.le_of_not_gt hi), List.getElem?_eq_none (Nat.le_of_not_gt hb)]

-- [proof->req~compiler-trace-representation~1]
theorem roundTrip_data (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (target : Temporal.Lasso) (h : roundTripChecks v source target = true) :
    target.frames.length = steps ∧ target.loop = source.loop.val ∧
    (∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y) ∧
    source.identities.directType[source.identities.root] = v.core.root ∧
    (∀ x : Fin o, source.identities.directType[x] = v.core.root → x = source.identities.root) ∧
    ∀ t, (∀ (i x : Nat), x ∈ (target.unfold.state t).signatures[i]?.getD [] ↔
      x ∈ ((encode v source).unfold.state t).signatures[i]?.getD []) ∧
      (∀ (i : Nat) (row : List Nat), row ∈ (target.unfold.state t).fields[i]?.getD [] ↔
      row ∈ ((encode v source).unfold.state t).fields[i]?.getD []) := by
  simp only [roundTripChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, forall_true_left] at h
  rcases h with ⟨⟨⟨⟨⟨hlen, hloop⟩, unique⟩, rootType⟩, rootOnly⟩, frames⟩
  refine ⟨hlen, hloop, unique, rootType, rootOnly, ?_⟩
  intro t
  have hi : target.index t = (source.index t).val := by
    by_cases ht : t < steps <;>
      simp [Temporal.Lasso.index, IR.Behavioral.Lasso.index, hlen, hloop, ht]
  have hf := frames (source.index t)
  simp only [sameState, Bool.and_eq_true] at hf
  have ht : target.unfold.state t = target.frames[(source.index t).val]?.getD ⟨[], [], []⟩ := by
    change target.frames[target.index t]?.getD _ = _
    rw [hi]
  rw [ht, encode_unfold]
  exact ⟨fun i x => sameTables_meaning _ _ hf.1 i x,
    fun i row => sameTables_meaning _ _ hf.2 i row⟩

/-- A successful finite re-encoding check produces the same global identity
correspondence as the encoder, transported across exact table membership. -/
def roundTrip_rep (v : IR.Structural.Layout k) (source : IR.Behavioral.Lasso k o steps)
    (target : Temporal.Lasso) (checked : roundTripChecks v source target = true) :
    TraceRep v source target := by
  obtain ⟨hlen, hloop, unique, rootType, rootOnly, hs⟩ := roundTrip_data v source target checked
  let base := encode_rep v source unique rootType rootOnly
  let pools : Pool (encode v source) ≃ Pool target :=
    Equiv.subtypeEquivProp (by
      funext x
      exact propext ((hs 0).1 0 x).symm)
  refine { objects := base.objects.trans pools
           length := hlen
           loop := hloop
           roots := ?_
           pools := ?_
           allObjects := ?_
           parents := ?_
           lives := ?_
           references := ?_ }
  · intro t label
    exact ((hs t).1 _ label).trans (base.roots t label)
  · intro t d label
    exact ((hs t).1 _ label).trans (base.pools t d label)
  · intro t label
    exact ((hs t).1 0 label).trans (base.allObjects t label)
  · intro t row
    exact ((hs t).2 0 row).trans (base.parents t row)
  · intro t row
    exact ((hs t).2 1 row).trans (base.lives t row)
  · intro t d row
    exact ((hs t).2 _ row).trans (base.references t d row)

-- [proof->req~compiler-trace-representation~1]
theorem decode_checked (v : IR.Structural.Layout k) (target : Temporal.Lasso)
    (decoded : Σ o steps, IR.Behavioral.Lasso k o steps)
    (h : decode v target = .ok decoded) : roundTripChecks v decoded.2.2 target = true := by
  unfold decode at h
  cases raw : decodeRaw v target with
  | error error => simp [raw, Except.bind, bind] at h
  | ok result =>
    simp only [raw, Except.bind, bind, pure] at h
    split at h
    · rename_i hc
      cases h
      exact hc
    · cases h

/-- Actual executable decoder success implies concrete trace representation;
this theorem never takes an assumed source observation or formula agreement. -/
def decode_rep (v : IR.Structural.Layout k) (target : Temporal.Lasso)
    (decoded : Σ o steps, IR.Behavioral.Lasso k o steps)
    (h : decode v target = .ok decoded) : TraceRep v decoded.2.2 target :=
  roundTrip_rep v decoded.2.2 target (decode_checked v target decoded h)

end ClaferCompiler.Correctness.Behavioral
