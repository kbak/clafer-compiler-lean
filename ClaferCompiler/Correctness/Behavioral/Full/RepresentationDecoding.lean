module

public import ClaferCompiler.Correctness.Behavioral.Full.Representation
public import ClaferCompiler.Correctness.Behavioral.RepresentationDecoding

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy
open Backend.Alloy.Behavioral.Full

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem roundTrip_encode (v : IR.BehavioralStructural.Validated k) (source : ObservedLasso k o steps)
    (unique : ∀ x y : Fin o,
      source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y)
    (rootType : source.objects.identities.directType[source.objects.identities.root] = v.core.structural.root)
    (rootOnly : ∀ x : Fin o, source.objects.identities.directType[x] = v.core.structural.root →
      x = source.objects.identities.root) :
    roundTripChecks v source (encode source) = true := by
  simp only [roundTripChecks, encode, List.length_map, List.length_finRange,
    beq_self_eq_true, Bool.true_and, decide_eq_true unique, decide_eq_true rootType, decide_eq_true rootOnly]
  simp [List.all_eq_true, sameState, sameTables_refl]

theorem roundTrip_data (v : IR.BehavioralStructural.Validated k) (source : ObservedLasso k o steps) (target : Temporal.Lasso)
    (h : roundTripChecks v source target = true) :
    target.frames.length = steps ∧ target.loop = source.objects.loop.val ∧
    (∀ x y : Fin o,
      source.objects.identities.ids[x] = source.objects.identities.ids[y] → x = y) ∧
    source.objects.identities.directType[source.objects.identities.root] = v.core.structural.root ∧
    (∀ x : Fin o, source.objects.identities.directType[x] = v.core.structural.root →
      x = source.objects.identities.root) ∧
    ∀ t, (∀ (i x : Nat), x ∈ (target.unfold.state t).signatures[i]?.getD [] ↔
      x ∈ ((encode source).unfold.state t).signatures[i]?.getD []) ∧
      (∀ (i : Nat) (row : List Nat), row ∈ (target.unfold.state t).fields[i]?.getD [] ↔
      row ∈ ((encode source).unfold.state t).fields[i]?.getD []) ∧
      (∀ row, row ∈ (target.unfold.state t).values[0]?.getD [] ↔
      row ∈ ((encode source).unfold.state t).values[0]?.getD []) := by
  simp only [roundTripChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, forall_true_left] at h
  rcases h with ⟨⟨⟨⟨⟨hlen, hloop⟩, unique⟩, rootType⟩, rootOnly⟩, frames⟩
  refine ⟨hlen, hloop, unique, rootType, rootOnly, ?_⟩
  intro t
  have hi : target.index t = (source.objects.index t).val := by
    by_cases ht : t < steps <;>
      simp [Temporal.Lasso.index, IR.Behavioral.Lasso.index, hlen, hloop, ht]
  have hf := frames (source.objects.index t)
  simp only [sameState, Bool.and_eq_true] at hf
  have ht : target.unfold.state t =
      target.frames[(source.objects.index t).val]?.getD ⟨[], [], []⟩ := by
    change target.frames[target.index t]?.getD _ = _
    rw [hi]
  rw [ht, encode_unfold]
  refine ⟨fun i x => sameTables_meaning _ _ hf.1.1 i x,
    fun i row => sameTables_meaning _ _ hf.1.2 i row, ?_⟩
  intro row
  exact sameTables_meaning _ _ hf.2 0 row

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Reflection transports a complete global representation across extensionally
equal tables. Scalar equations are checked alongside object equations. -/
def roundTrip_rep (v : IR.BehavioralStructural.Validated k) (source : ObservedLasso k o steps) (target : Temporal.Lasso)
    (checked : roundTripChecks v source target = true) : TraceRep v source target := by
  obtain ⟨hlen, hloop, unique, rootType, rootOnly, hs⟩ := roundTrip_data v source target checked
  let base := encode_rep v source unique rootType rootOnly
  let pools : Pool (encode source) ≃ Pool target :=
    Equiv.subtypeEquivProp (by
      funext x
      exact propext ((hs 0).1 0 x).symm)
  refine { objects := base.objects.trans pools
           length := hlen
           loop := hloop
           roots := ?_
           directTypes := ?_
           allObjects := ?_
           parents := ?_
           lives := ?_
           references := ?_
           values := ?_ }
  · intro t label
    exact ((hs t).1 _ label).trans (base.roots t label)
  · intro t d label
    exact ((hs t).1 _ label).trans (base.directTypes t d label)
  · intro t label
    exact ((hs t).1 0 label).trans (base.allObjects t label)
  · intro t row
    exact ((hs t).2.1 0 row).trans (base.parents t row)
  · intro t row
    exact ((hs t).2.1 1 row).trans (base.lives t row)
  · intro t d row
    exact ((hs t).2.1 _ row).trans (base.references t d row)
  · intro t row
    exact ((hs t).2.2 row).trans (base.values t row)

theorem decode_checked (v : IR.BehavioralStructural.Validated k) (target : Temporal.Lasso)
    (decoded : Σ o steps, ObservedLasso k o steps)
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

-- [proof->req~compiler-full-behavioral-correctness~1]
def decode_rep (v : IR.BehavioralStructural.Validated k) (target : Temporal.Lasso)
    (decoded : Σ o steps, ObservedLasso k o steps)
    (h : decode v target = .ok decoded) : TraceRep v decoded.2.2 target :=
  roundTrip_rep v decoded.2.2 target (decode_checked v target decoded h)

end ClaferCompiler.Correctness.Behavioral.Full
