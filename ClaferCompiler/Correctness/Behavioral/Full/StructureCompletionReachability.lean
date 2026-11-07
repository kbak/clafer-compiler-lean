module

public import ClaferCompiler.Correctness.Behavioral.Full.StructureCompletionKeys
public import ClaferCompiler.Correctness.Behavioral.Full.StructureReachability

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

/-- Functional, immutable parents give every root path a unique depth. -/
theorem parentPath_unique_depth (source : ObservedLasso k o steps)
    (rootParent : source.objects.identities.parent[source.objects.identities.root] = none)
    {n m : Nat} {x : Fin o} (hn : ParentPath source n x) (hm : ParentPath source m x) : n = m := by
  induction n generalizing m x with
  | zero =>
    have hx : x = source.objects.identities.root := hn
    subst x
    cases m with
    | zero => rfl
    | succ m =>
      obtain ⟨y, _, hy⟩ := hm
      rw [rootParent] at hy
      contradiction
  | succ n ih =>
    obtain ⟨a, ha, hxa⟩ := hn
    cases m with
    | zero =>
      have hx : x = source.objects.identities.root := hm
      subst x
      rw [rootParent] at hxa
      contradiction
    | succ m =>
      obtain ⟨b, hb, hxb⟩ := hm
      have eq : a = b := Option.some.inj (hxa.symm.trans hxb)
      subst b
      exact congrArg Nat.succ (ih ha hb)

theorem parentPath_prefix (source : ObservedLasso k o steps)
    {n : Nat} {x : Fin o} (path : ParentPath source n x) (i : Nat) (bound : i ≤ n) :
    ∃ y, ParentPath source i y := by
  induction n generalizing x with
  | zero =>
    have eq : i = 0 := by omega
    subst i
    exact ⟨x, path⟩
  | succ n ih =>
    by_cases eq : i = n + 1
    · subst i; exact ⟨x, path⟩
    · obtain ⟨p, hp, _⟩ := path
      exact ih hp (by omega)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Every root path fits the finite inventory: two prefix depths cannot name
the same occurrence. This is a data cardinality argument, not a target fact. -/
theorem parentPath_bound (source : ObservedLasso k o steps)
    (rootParent : source.objects.identities.parent[source.objects.identities.root] = none)
    {n : Nat} {x : Fin o} (path : ParentPath source n x) : n < o := by
  let point (i : Fin (n + 1)) : Fin o := (parentPath_prefix source path i.val (by omega)).choose
  have hit (i : Fin (n + 1)) : ParentPath source i.val (point i) :=
    (parentPath_prefix source path i.val (by omega)).choose_spec
  have injective : Function.Injective point := by
    intro i j eq
    apply Fin.ext
    exact parentPath_unique_depth source rootParent (hit i) (eq ▸ hit j)
  have bound := Fintype.card_le_of_injective point injective
  simp only [Fintype.card_fin] at bound
  omega

theorem complete_reachable_parentPath (v : IR.BehavioralStructural.Validated k)
    (p : Fin k) (source : ObservedLasso k o steps) (t : Nat) (x : Fin o)
    (reachable : ((completeTrace v p source).raw
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches (Sum.inl x)) :
    ∃ n, ParentPath source n x := by
  have general {y : Completion o}
      (h : ((completeTrace v p source).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).Reaches y) :
      match y with
      | .inl y => ∃ n, ParentPath source n y
      | .inr _ => True := by
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail y z path edge ih =>
      cases z with
      | inr z => trivial
      | inl z =>
        obtain ⟨d, contained⟩ := edge
        have parent := contained.1.2.2
        cases y with
        | inr value =>
          change source.objects.identities.parent[z].map Sum.inl = some (Sum.inr value) at parent
          simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at parent
        | inl y =>
          obtain ⟨n, hn⟩ := ih
          exact ⟨n + 1, y, hn, (complete_parent_object v p source z y).mp parent⟩
  exact general reachable

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem reachabilityFact_complete (rep : TraceRep v source target) (p : Fin k)
    (w t capacity : Nat) (capacityFits : o ≤ capacity)
    (valid : Clafer.Behavioral.Structural.Valid
      (SemanticsBridge.BehavioralStructural.interpret v.core) (completeTrace v p source)) :
    (reachabilityFact v capacity).Holds (schema v) w target.unfold [] t := by
  intro row member
  obtain ⟨x, live, rfl⟩ := (rep.live_meaning w [] t row).mp member
  obtain ⟨n, path⟩ := complete_reachable_parentPath v p source t x ((valid.states t).reachable (Sum.inl x) live)
  have rootParent : source.objects.identities.parent[source.objects.identities.root] = none := by
    have rootParent := valid.identities.root_parent
    change (source.objects.identities.parent[source.objects.identities.root]).map Sum.inl = none at rootParent
    exact Option.map_eq_none_iff.mp rootParent
  have depth := parentPath_bound source rootParent path
  change [.object (rep.label x)] ∈
    (((List.range (capacity + 1)).map fun depth =>
      Nat.repeat (fun r => Rel.join r (.transpose parent)) depth (root v)).foldl Rel.union
      (.empty .unary)).eval (schema v) w target.unfold [] t
  rw [union_rows _ (by
    intro r hr
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hr
    exact parentPath_term v n) _ (.empty _)]
  apply Or.inr
  exact ⟨_, List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩,
    (rep.parentPath_meaning w [] t n _).mpr ⟨x, path, rfl⟩⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
