module

public import ClaferCompiler.Correctness.Behavioral.Full.Structure

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

def ParentPath (source : ObservedLasso k o steps) : Nat → Fin o → Prop :=
  Nat.rec (fun x => x = source.objects.identities.root)
    (fun _ previous x => ∃ p, previous p ∧ source.objects.identities.parent[x] = some p)

theorem parentPath_term (v : IR.BehavioralStructural.Validated k) (n : Nat) :
    (Nat.repeat (fun r => Rel.join r (.transpose parent)) n (root v)).Term := by
  induction n with
  | zero => exact root_term v
  | succ n ih => exact .join ih (.transpose (.field 0))

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem root_head (rep : TraceRep v source target) (w t : Nat)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t) :
    ∀ x, x ∈ ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head
        v.core.structural.root ↔ x = source.objects.identities.root := by
  have ordinary := (rep.ordinary_concrete w identity source.objects.identities.root).2
  rw [rep.root_type] at ordinary
  have h := facts (.equal (head v v.core.structural.root) (root v)) (by simp [stateFacts])
  have eq := (Relations.unary_equal rep.label_injective
    (rep.head_source w [] t _ ordinary) (rep.root_meaning w [] t)).mp h
  intro x
  exact Set.ext_iff.mp eq x

theorem parentPath_meaning (rep : TraceRep v source target) (w : Nat)
    (e : Environment) (t n : Nat) :
    Relations.Unary rep.label {x | ParentPath source n x}
      ((Nat.repeat (fun r => Rel.join r (.transpose parent)) n (root v)).eval
        (schema v) w target.unfold e t) := by
  induction n with
  | zero => exact rep.root_meaning w e t
  | succ n ih =>
    exact Relations.unary_image rep.label_injective (parentPath_term v n)
      (.transpose (.field 0)) ih (Relations.binary_transpose (.field 0) (rep.parent_meaning w e t))

theorem parentPath_reaches (rep : TraceRep v source target) (w t : Nat)
    (shape : PrimitiveShape v)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (n : Nat) (x : Fin o) (path : ParentPath source n x)
    (live : (source.objects.at t).live[x] = true) :
    ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x := by
  induction n generalizing x with
  | zero =>
    have eq : x = source.objects.identities.root := path
    subst x
    exact .refl
  | succ n ih =>
    obtain ⟨p, hp, parent⟩ := path
    have parentLive := rep.parent_live w t facts x p live parent
    obtain ⟨c, hc, _⟩ := rep.parent_typed w shape identity x p parent
    refine (ih p hp parentLive).tail ⟨source.objects.identities.directType[x],
      ⟨⟨parentLive, live, parent⟩, .refl, ?_⟩⟩
    change (v.core.structural.get source.objects.identities.directType[x]).parent ≠ none
    rw [hc]
    exact Option.some_ne_none c

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- The generated bounded ownership paths imply unbounded source reachability.
The proof never turns references into containment edges. -/
theorem reachable (rep : TraceRep v source target) (w t capacity : Nat)
    (shape : PrimitiveShape v)
    (identity : ∀ f ∈ identityFacts v, f.Holds (schema v) w target.unfold [] 0)
    (facts : ∀ f ∈ stateFacts v, f.Holds (schema v) w target.unfold [] t)
    (reach : (reachabilityFact v capacity).Holds (schema v) w target.unfold [] t)
    (x : Fin o) (live : (source.objects.at t).live[x] = true) :
    ((SemanticsBridge.Behavioral.trace source.objects).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches x := by
  have input := (rep.live_meaning w [] t [.object (rep.label x)]).mpr ⟨x, live, rfl⟩
  have output := reach _ input
  change [.object (rep.label x)] ∈
    (((List.range (capacity + 1)).map fun depth =>
      Nat.repeat (fun r => Rel.join r (.transpose parent)) depth (root v)).foldl Rel.union
      (.empty .unary)).eval (schema v) w target.unfold [] t at output
  rw [union_rows _ (by
    intro r hr
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hr
    exact parentPath_term v n) _ (.empty _)] at output
  have empty : (Rel.empty .unary).eval (schema v) w target.unfold [] t = [] := rfl
  rw [empty] at output
  obtain ⟨r, hr, row⟩ := output.resolve_left List.not_mem_nil
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hr
  obtain ⟨y, path, eq⟩ := (rep.parentPath_meaning w [] t n _).mp row
  have eq : x = y := rep.label_injective (by simpa using eq)
  subst y
  exact rep.parentPath_reaches w t shape identity facts n x path live

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
